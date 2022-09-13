//! Tagged pointer support.

#![allow(clippy::new_ret_no_self)]

use std::{convert::TryFrom, mem::size_of, ops::Deref};

use num_bigint::BigInt;
use num_enum::{IntoPrimitive, UnsafeFromPrimitive};
use num_traits::{FromPrimitive, ToPrimitive};
use std::gc::Gc;

use std::gc::NoTrace;

use super::{
    core::VM,
    error::{VMError, VMErrorKind},
    objects::{ArbInt, Double, Int, Obj, ObjType, StaticObjType, String_, ThinObj},
};

// We use a fairly standard pointer tagging model where the low `TAG_BITSIZE` bits of a machine
// word (represented as a Rust `usize`) are used to store the type of the value (with the
// possibilities enumerated in `ValKind` below).

#[cfg(target_pointer_width = "64")]
pub const BITSIZE: usize = 64;
#[cfg(target_pointer_width = "64")]
pub const TAG_BITSIZE: usize = 2; // Number of bits
#[cfg(target_pointer_width = "64")]
pub const TAG_BITMASK: usize = 0b11;
#[cfg(target_pointer_width = "64")]
pub const INT_BITMASK: usize = 0b111;

#[cfg(target_pointer_width = "64")]
#[derive(Debug, PartialEq, IntoPrimitive, UnsafeFromPrimitive)]
#[repr(usize)]
// All of the values here must:
//   1) Fit inside TAG_BITSIZE bits
//   2) Safely convert to usize using `as`
// Anything which can be stored unboxed *must* not have the `NotUnboxable` trait implemented
// for them. In other words, if an existing type is added to the list of unboxable things, you
// need to check whether it implemented `NotUnboxable` and, if so, remove that implementation.
pub enum ValKind {
    /// A pointer to a `Gc` element.
    GCBOX = 0b01,
    /// A tagged integer.
    INT = 0b00,
    /// An illegal value. Any operations on a `Val` of this kind will result in a
    /// [`panic`](core::panic).
    ILLEGAL = 0b10,
}

/// Objects which `impl` this trait guarantee that they can only ever be stored boxed.
/// Implementing this trait on objects which can be stored unboxed leads to undefined behaviour.
pub trait NotUnboxable {}

/// The core struct representing values in the language runtime: boxed and unboxed values are
/// hidden behind this, such that they can be treated in exactly the same way.
#[derive(Debug, PartialEq, Clone, Copy)]
pub struct Val {
    // We use this usize for pointer tagging. Needless to say, this is highly dangerous, and needs
    // several parts of the code to cooperate in order to be correct.
    pub val: usize,
}

impl !NoTrace for Val {}

impl Val {
    /// Create a new `Val` from an object that should be allocated on the heap.
    pub fn from_obj<T: Obj + 'static>(obj: T) -> Val {
        let p = Gc::into_raw(ThinObj::new(obj));
        Val {
            val: (p as usize) | (ValKind::GCBOX as usize),
        }
    }

    /// Convert `obj` into a `Val`. `Obj` must previously have been created via `Val::from_obj` and
    /// then turned into an actual object with `tobj`: failure to follow these steps will result in
    /// undefined behaviour.
    pub fn recover<T: Obj + 'static>(obj: Gc<T>) -> Self {
        unsafe {
            let p = Gc::into_raw(ThinObj::recover_gc(obj));
            Val {
                val: (p as usize) | (ValKind::GCBOX as usize),
            }
        }
    }

    /// Create a value upon which all operations are invalid. This can be used as a sentinel or
    /// while initialising part of the system.
    pub fn illegal() -> Val {
        Val {
            val: ValKind::ILLEGAL as usize,
        }
    }

    /// What is this `Val`'s [`ValKind`](ValKind).
    pub fn valkind(&self) -> ValKind {
        // Since it should be impossible to create incorrect tags, in release mode, we want to make
        // this a zero-cost function (i.e. we get guarantees from the static type system but
        // without any run-time overhead). However, just in case someone does something silly, in
        // debug mode we explicitly check the tags.

        #[cfg(debug_assertions)]
        match self.val & TAG_BITMASK {
            x if x == ValKind::GCBOX as usize => (),
            x if x == ValKind::INT as usize => (),
            x if x == ValKind::ILLEGAL as usize => (),
            _ => panic!("Invalid tag {}", self.val & TAG_BITMASK),
        }

        unsafe { ValKind::from_unchecked(self.val & TAG_BITMASK) }
    }

    /// Cast a `Val` into an instance of type `T` (where `T` must statically be a type that cannot
    /// be boxed) or return a `VMError` if the cast is invalid.
    pub fn downcast<T: Obj + StaticObjType + NotUnboxable>(
        &self,
        vm: &VM,
    ) -> Result<Gc<T>, Box<VMError>> {
        match self.valkind() {
            ValKind::INT => Err(VMError::new(
                vm,
                VMErrorKind::BuiltinTypeError {
                    expected: T::static_objtype(),
                    got: Int::static_objtype(),
                },
            )),
            ValKind::GCBOX => {
                let tobj = unsafe { self.gcbox_to_tobj() };
                tobj.downcast().ok_or_else(|| {
                    VMError::new(
                        vm,
                        VMErrorKind::BuiltinTypeError {
                            expected: T::static_objtype(),
                            got: tobj.deref().as_gc().dyn_objtype(),
                        },
                    )
                })
            }
            ValKind::ILLEGAL => unreachable!(),
        }
    }

    /// Cast a `Val` into an instance of type `T` (where `T` must statically be a type that cannot
    /// be boxed) or return `None` if the cast is not valid.
    pub fn try_downcast<T: Obj + StaticObjType + NotUnboxable>(&self, _: &VM) -> Option<Gc<T>> {
        match self.valkind() {
            ValKind::INT => None,
            ValKind::GCBOX => unsafe { self.gcbox_to_tobj() }.downcast(),
            ValKind::ILLEGAL => unreachable!(),
        }
    }

    /// If this `Val` is a `GCBox` then convert it into `ThinObj`; if this `Val` is not a `GCBox`
    /// then undefined behaviour will occur (hence why this function is `unsafe`).
    unsafe fn gcbox_to_tobj(&self) -> Gc<ThinObj> {
        debug_assert_eq!(self.valkind(), ValKind::GCBOX);
        let ptr = (self.val & !(ValKind::GCBOX as usize)) as *const ThinObj;
        Gc::from_raw(ptr)
    }

    /// Return this `Val`'s box. If the `Val` refers to an unboxed value, this will box it.
    pub fn tobj(&self, vm: &mut VM) -> Result<Gc<ThinObj>, Box<VMError>> {
        match self.valkind() {
            ValKind::GCBOX => {
                debug_assert_eq!(size_of::<*const ThinObj>(), size_of::<usize>());
                Ok(unsafe { self.gcbox_to_tobj() })
            }
            ValKind::INT => {
                let i = self.as_isize(vm).unwrap();
                Int::boxed_isize(vm, i).tobj(vm)
            }
            ValKind::ILLEGAL => unreachable!(),
        }
    }

    /// Create a (possibly boxed) `Val` representing the `isize` integer `i`.
    pub fn from_isize(vm: &mut VM, i: isize) -> Val {
        let top_bits = i as usize & (INT_BITMASK << (BITSIZE - TAG_BITSIZE - 1));
        if top_bits == 0 || top_bits == INT_BITMASK << (BITSIZE - TAG_BITSIZE - 1) {
            // top_bits == 0: A positive integer that fits in our tagging scheme
            // top_bits all set to 1: A negative integer that fits in our tagging scheme
            Val {
                val: ((i as usize) << TAG_BITSIZE) | (ValKind::INT as usize),
            }
        } else {
            Int::boxed_isize(vm, i)
        }
    }

    /// Create a (possibly boxed) `Val` representing the `usize` integer `i`.
    pub fn from_usize(vm: &mut VM, i: usize) -> Val {
        if i & (INT_BITMASK << (BITSIZE - TAG_BITSIZE - 1)) == 0 {
            // The top TAG_BITSIZE bits aren't set, so this fits within our pointer tagging scheme.
            Val {
                val: (i << TAG_BITSIZE) | (ValKind::INT as usize),
            }
        } else {
            ArbInt::new(vm, BigInt::from_usize(i).unwrap())
        }
    }

    #[cfg(target_pointer_width = "64")]
    pub fn from_u64(vm: &mut VM, i: u64) -> Val {
        Val::from_usize(vm, i as usize)
    }

    /// If `v == true`, return a `Val` representing `vm.true_`, otherwise return a `Val`
    /// representing `vm.false_`.
    pub fn from_bool(vm: &VM, v: bool) -> Val {
        if v {
            vm.true_
        } else {
            vm.false_
        }
    }

    /// If this `Val` represents a non-bigint integer, return its value as an `isize`.
    pub fn as_isize(&self, vm: &mut VM) -> Result<isize, Box<VMError>> {
        match self.valkind() {
            ValKind::GCBOX => match unsafe { self.gcbox_to_tobj() }.downcast::<Int>() {
                Some(tobj) => Ok(tobj.as_isize()),
                None => Err(VMError::new(vm, VMErrorKind::CantRepresentAsIsize)),
            },
            ValKind::INT => {
                if self.val & 1 << (BITSIZE - 1) == 0 {
                    Ok((self.val >> TAG_BITSIZE) as isize)
                } else {
                    // For negative integers we need to pad the top TAG_BITSIZE bits with 1s.
                    Ok(
                        ((self.val >> TAG_BITSIZE) | (TAG_BITMASK << (BITSIZE - TAG_BITSIZE)))
                            as isize,
                    )
                }
            }
            ValKind::ILLEGAL => unreachable!(),
        }
    }

    /// If this `Val` represents a non-bigint integer, return its value as an `usize`.
    pub fn as_usize(&self, vm: &mut VM) -> Result<usize, Box<VMError>> {
        match self.valkind() {
            ValKind::GCBOX => match unsafe { self.gcbox_to_tobj() }.downcast::<Int>() {
                Some(tobj) => tobj.as_usize(vm),
                None => Err(VMError::new(vm, VMErrorKind::CantRepresentAsUsize)),
            },
            ValKind::INT => {
                if self.val & 1 << (BITSIZE - 1) == 0 {
                    Ok(self.val >> TAG_BITSIZE)
                } else {
                    Err(VMError::new(vm, VMErrorKind::CantRepresentAsUsize))
                }
            }
            ValKind::ILLEGAL => unreachable!(),
        }
    }

    pub fn as_f64(&self, vm: &mut VM) -> Result<f64, Box<VMError>> {
        match self.valkind() {
            ValKind::GCBOX => match unsafe { self.gcbox_to_tobj() }.downcast::<ArbInt>() {
                Some(tobj) => tobj.to_f64(vm),
                None => Err(VMError::new(vm, VMErrorKind::CantRepresentAsDouble)),
            },
            ValKind::INT => {
                if self.val & 1 << (BITSIZE - 1) == 0 {
                    Ok((self.val >> TAG_BITSIZE) as isize as f64)
                } else {
                    // For negative integers we need to pad the top TAG_BITSIZE bits with 1s.
                    Ok(
                        ((self.val >> TAG_BITSIZE) | (TAG_BITMASK << (BITSIZE - TAG_BITSIZE)))
                            as isize as f64,
                    )
                }
            }
            ValKind::ILLEGAL => unreachable!(),
        }
    }

    /// Is this `Val` bit equal to `other`? This is a very strong property, generally used as a
    /// fast proxy for "if both `Val`s are `GCBox`s then do they point to the same thing?" since,
    /// in such cases, at least one of the sides has been pre-guaranteed to be a `GCBox`.
    pub fn bit_eq(&self, other: &Val) -> bool {
        self.val == other.val
    }
}

// Implement each function from the `Obj` type so that we can efficiently deal with tagged values.
impl Val {
    /// What `ObjType` does this `Val` represent?
    pub fn dyn_objtype(&self, vm: &mut VM) -> ObjType {
        match self.valkind() {
            ValKind::INT => ObjType::Int,
            ValKind::GCBOX => self.tobj(vm).unwrap().as_gc().dyn_objtype(),
            ValKind::ILLEGAL => unreachable!(),
        }
    }

    /// What class is this `Val` an instance of?
    pub fn get_class(&self, vm: &mut VM) -> Val {
        match self.valkind() {
            ValKind::INT => vm.int_cls,
            ValKind::GCBOX => self.tobj(vm).unwrap().as_gc().get_class(vm),
            ValKind::ILLEGAL => unreachable!(),
        }
    }

    pub fn to_strval(&self, vm: &mut VM) -> Result<Val, Box<VMError>> {
        match self.valkind() {
            ValKind::INT => {
                let s = self.as_isize(vm).unwrap().to_string();
                Ok(String_::new_str(vm, s.into()))
            }
            ValKind::GCBOX => self.tobj(vm).unwrap().as_gc().to_strval(vm),
            ValKind::ILLEGAL => unreachable!(),
        }
    }

    /// Produce a new `Val` which adds `other` to this.
    pub fn hashcode(&self, vm: &mut VM) -> Val {
        match self.valkind() {
            ValKind::INT => {
                // Integer.som (not very sensibly) defines hashing an integer to be the integer
                // itself.
                unreachable!()
            }
            ValKind::GCBOX => {
                let hc = self.tobj(vm).unwrap().as_gc().hashcode();
                Val::from_u64(vm, hc)
            }
            ValKind::ILLEGAL => unreachable!(),
        }
    }

    /// Produce a new `Val` which adds `other` to this.
    pub fn add(&self, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        debug_assert_eq!(ValKind::INT as usize, 0);
        if self.valkind() == ValKind::INT && other.valkind() == ValKind::INT {
            if let Some(val) = self.val.checked_add(other.val) {
                return Ok(Val { val });
            }
        }
        self.tobj(vm).unwrap().as_gc().add(vm, other)
    }

    /// Produce a new `Val` which performs a bitwise and operation with `other` and this.
    pub fn and(&self, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Ok(lhs) = self.as_isize(vm) {
            if let Ok(rhs) = other.as_isize(vm) {
                return Ok(Val::from_isize(vm, lhs & rhs));
            } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
                return Ok(ArbInt::new(
                    vm,
                    BigInt::from_isize(lhs).unwrap() & rhs.bigint(),
                ));
            }
            let expected = self.dyn_objtype(vm);
            let got = other.dyn_objtype(vm);
            return Err(VMError::new(
                vm,
                VMErrorKind::BuiltinTypeError { expected, got },
            ));
        }
        debug_assert_eq!(self.valkind(), ValKind::GCBOX);
        unsafe { self.gcbox_to_tobj() }.as_gc().and(vm, other)
    }

    /// Produce a new `Val` which divides `other` from this.
    pub fn div(&self, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Ok(lhs) = self.as_isize(vm) {
            if let Ok(rhs) = other.as_isize(vm) {
                if rhs == 0 {
                    return Err(VMError::new(vm, VMErrorKind::DivisionByZero));
                } else {
                    return Ok(Val::from_isize(vm, lhs / rhs));
                }
            } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
                return Ok(ArbInt::new(
                    vm,
                    BigInt::from_isize(lhs).unwrap() / rhs.bigint(),
                ));
            } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
                if rhs.double() == 0f64 {
                    return Err(VMError::new(vm, VMErrorKind::DivisionByZero));
                } else {
                    return Ok(Val::from_isize(vm, ((lhs as f64) / rhs.double()) as isize));
                }
            }
            let got = other.dyn_objtype(vm);
            return Err(VMError::new(vm, VMErrorKind::NotANumber { got }));
        }
        debug_assert_eq!(self.valkind(), ValKind::GCBOX);
        unsafe { self.gcbox_to_tobj() }.as_gc().div(vm, other)
    }

    /// Produce a new `Val` which perfoms a Double divide on `other` with this.
    pub fn double_div(&self, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Ok(lhs) = self.as_isize(vm) {
            if let Ok(rhs) = other.as_isize(vm) {
                if rhs == 0 {
                    return Err(VMError::new(vm, VMErrorKind::DivisionByZero));
                } else {
                    return Ok(Double::new(vm, (lhs as f64) / (rhs as f64)));
                }
            } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
                if let Some(i) = rhs.bigint().to_f64() {
                    return Ok(Double::new(vm, (lhs as f64) / i));
                } else {
                    return Err(VMError::new(vm, VMErrorKind::CantRepresentAsDouble));
                }
            } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
                if rhs.double() == 0f64 {
                    return Err(VMError::new(vm, VMErrorKind::DivisionByZero));
                } else {
                    return Ok(Double::new(vm, (lhs as f64) / rhs.double()));
                }
            }
            let got = other.dyn_objtype(vm);
            return Err(VMError::new(vm, VMErrorKind::NotANumber { got }));
        }
        debug_assert_eq!(self.valkind(), ValKind::GCBOX);
        unsafe { self.gcbox_to_tobj() }
            .as_gc()
            .double_div(vm, other)
    }

    /// Produce a new `Val` which performs a mod operation on this with `other`.
    pub fn modulus(&self, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Ok(lhs) = self.as_isize(vm) {
            if let Ok(rhs) = other.as_isize(vm) {
                if rhs == 0 {
                    return Err(VMError::new(vm, VMErrorKind::DivisionByZero));
                }
                return Ok(Val::from_isize(vm, ((lhs % rhs) + rhs) % rhs));
            } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
                let lhs = BigInt::from_isize(lhs).unwrap();
                let rhs = rhs.bigint();
                return Ok(ArbInt::new(vm, ((lhs % rhs) + rhs) % rhs));
            } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
                return Ok(Double::new(vm, (lhs as f64) % rhs.double()));
            }
            let got = other.dyn_objtype(vm);
            return Err(VMError::new(vm, VMErrorKind::NotANumber { got }));
        }
        debug_assert_eq!(self.valkind(), ValKind::GCBOX);
        unsafe { self.gcbox_to_tobj() }.as_gc().modulus(vm, other)
    }

    /// Produce a new `Val` which multiplies `other` to this.
    pub fn mul(&self, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        debug_assert_eq!(ValKind::INT as usize, 0);
        if self.valkind() == ValKind::INT && other.valkind() == ValKind::INT {
            if let Some(val) = self.val.checked_mul(other.val / (1 << TAG_BITSIZE)) {
                return Ok(Val { val });
            }
        }
        self.tobj(vm).unwrap().as_gc().mul(vm, other)
    }

    /// Produce a new `Val` which performs a mod operation on this with `other`.
    pub fn remainder(&self, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Ok(lhs) = self.as_isize(vm) {
            if let Ok(rhs) = other.as_isize(vm) {
                match lhs.checked_rem(rhs) {
                    Some(i) => return Ok(Val::from_isize(vm, i)),
                    None => return Err(VMError::new(vm, VMErrorKind::RemainderError)),
                }
            } else if other.try_downcast::<ArbInt>(vm).is_some() {
                todo!();
            } else if other.try_downcast::<Double>(vm).is_some() {
                todo!();
            }
            let got = other.dyn_objtype(vm);
            return Err(VMError::new(vm, VMErrorKind::NotANumber { got }));
        }
        debug_assert_eq!(self.valkind(), ValKind::GCBOX);
        unsafe { self.gcbox_to_tobj() }.as_gc().remainder(vm, other)
    }

    /// Produce a new `Val` which shifts `self` `other` bits to the left.
    pub fn shl(&self, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Ok(lhs) = self.as_isize(vm) {
            if let Ok(rhs) = other.as_isize(vm) {
                if rhs < 0 {
                    return Err(VMError::new(vm, VMErrorKind::NegativeShift));
                } else {
                    let rhs_i = u32::try_from(rhs)
                        .map_err(|_| VMError::new(vm, VMErrorKind::ShiftTooBig))?;
                    if let Some(i) = lhs.checked_shl(rhs_i) {
                        // We have to be careful as shifting bits in an isize can lead to positive
                        // numbers becoming negative in two's complement. For example, on a 64-bit
                        // machine, (1isize<<63) == -9223372036854775808. To avoid this, if
                        // shifting +ve number leads to a -ve number being produced, we know we've
                        // exceeded an isize's ability to store the result, and need to fall back
                        // to the ArbInt case.
                        if lhs < 0 || (lhs > 0 && i > 0) {
                            return Ok(Val::from_isize(vm, i as isize));
                        }
                    }
                    return Ok(ArbInt::new(
                        vm,
                        BigInt::from_isize(lhs).unwrap() << usize::try_from(rhs_i).unwrap(),
                    ));
                }
            }
            if other.try_downcast::<ArbInt>(vm).is_some() {
                return Err(VMError::new(vm, VMErrorKind::ShiftTooBig));
            }
            let got = other.dyn_objtype(vm);
            return Err(VMError::new(vm, VMErrorKind::NotANumber { got }));
        }
        debug_assert_eq!(self.valkind(), ValKind::GCBOX);
        unsafe { self.gcbox_to_tobj() }.as_gc().shl(vm, other)
    }

    /// Produce a new `Val` which shifts `self` `other` bits to the right, treating `self` as if it
    /// did not have a sign bit.
    pub fn shr(&self, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Ok(lhs) = self.as_isize(vm) {
            if let Ok(rhs) = other.as_isize(vm) {
                if rhs < 0 {
                    return Err(VMError::new(vm, VMErrorKind::NegativeShift));
                } else {
                    let rhs_i = u32::try_from(rhs)
                        .map_err(|_| VMError::new(vm, VMErrorKind::ShiftTooBig))?;
                    return Ok(Val::from_isize(vm, ((lhs as usize) >> rhs_i) as isize));
                }
            }
            if other.try_downcast::<ArbInt>(vm).is_some() {
                return Err(VMError::new(vm, VMErrorKind::ShiftTooBig));
            }
            let got = other.dyn_objtype(vm);
            return Err(VMError::new(vm, VMErrorKind::NotANumber { got }));
        }
        debug_assert_eq!(self.valkind(), ValKind::GCBOX);
        unsafe { self.gcbox_to_tobj() }.as_gc().shr(vm, other)
    }

    /// Produces a new `Val` which is the square root of this.
    pub fn sqrt(&self, vm: &mut VM) -> Result<Val, Box<VMError>> {
        if let Ok(lhs) = self.as_isize(vm) {
            if lhs < 0 {
                return Err(VMError::new(vm, VMErrorKind::DomainError));
            } else {
                let result = (lhs as f64).sqrt();
                if result.round() == result {
                    return Ok(Val::from_isize(vm, result as isize));
                } else {
                    return Ok(Double::new(vm, result));
                }
            }
        }
        debug_assert_eq!(self.valkind(), ValKind::GCBOX);
        unsafe { self.gcbox_to_tobj() }.as_gc().sqrt(vm)
    }

    /// Produce a new `Val` which subtracts `other` from this.
    pub fn sub(&self, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        debug_assert_eq!(ValKind::INT as usize, 0);
        if self.valkind() == ValKind::INT && other.valkind() == ValKind::INT {
            if let Some(val) = self.val.checked_sub(other.val) {
                return Ok(Val { val });
            }
        }
        self.tobj(vm).unwrap().as_gc().sub(vm, other)
    }

    /// Produce a new `Val` which performs a bitwise xor operation with `other` and this.
    pub fn xor(&self, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Ok(lhs) = self.as_isize(vm) {
            if let Ok(rhs) = other.as_isize(vm) {
                return Ok(Val::from_isize(vm, lhs ^ rhs));
            } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
                return Ok(ArbInt::new(
                    vm,
                    BigInt::from_isize(lhs).unwrap() ^ rhs.bigint(),
                ));
            }
            let expected = self.dyn_objtype(vm);
            let got = other.dyn_objtype(vm);
            return Err(VMError::new(
                vm,
                VMErrorKind::BuiltinTypeError { expected, got },
            ));
        }
        debug_assert_eq!(self.valkind(), ValKind::GCBOX);
        unsafe { self.gcbox_to_tobj() }.as_gc().xor(vm, other)
    }

    /// Is this `Val` reference equal to `other`? Notice that for integers (but not Doubles)
    /// "reference equal" is equivalent to "equals".
    pub fn ref_equals(&self, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        match self.valkind() {
            ValKind::INT => self.equals(vm, other),
            ValKind::GCBOX => unsafe { self.gcbox_to_tobj() }
                .as_gc()
                .ref_equals(vm, other),
            ValKind::ILLEGAL => unreachable!(),
        }
    }
}

macro_rules! binop_all {
    ($name:ident, $op:tt, $tf:ident) => {
        impl Val {
            pub fn $name(&self, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
                if let Ok(lhs) = self.as_isize(vm) {
                    if let Ok(rhs) = other.as_isize(vm) {
                        Ok(Val::from_bool(vm, lhs $op rhs))
                    } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
                        Ok(Val::from_bool(vm, (lhs as f64) $op rhs.double()))
                    } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
                        Ok(Val::from_bool(vm,
                            &BigInt::from_isize(lhs).unwrap() $op rhs.bigint()))
                    } else {
                        Ok(vm.$tf)
                    }
                } else {
                    debug_assert_eq!(self.valkind(), ValKind::GCBOX);
                    unsafe { self.gcbox_to_tobj() }.as_gc().$name(vm, other)
                }
            }
        }
    };
}

macro_rules! binop_typeerror {
    ($name:ident, $op:tt) => {
        impl Val {
            pub fn $name(&self, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
                if let Ok(lhs) = self.as_isize(vm) {
                    if let Ok(rhs) = other.as_isize(vm) {
                        Ok(Val::from_bool(vm, lhs $op rhs))
                    } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
                        Ok(Val::from_bool(vm,
                            &BigInt::from_isize(lhs).unwrap() $op rhs.bigint()))
                    } else {
                        let got = other.dyn_objtype(vm);
                        Err(VMError::new(vm, VMErrorKind::NotANumber {
                          got
                        }))
                    }
                } else {
                    debug_assert_eq!(self.valkind(), ValKind::GCBOX);
                    unsafe { self.gcbox_to_tobj() }.as_gc().$name(vm, other)
                }
            }
        }
    };
}

binop_all!(equals, ==, false_);
binop_all!(not_equals, !=, true_);
binop_typeerror!(greater_than, >);
binop_typeerror!(greater_than_equals, >=);
binop_typeerror!(less_than, <);
binop_typeerror!(less_than_equals, <=);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm::{
        core::VM,
        objects::{Class, ObjType, String_},
    };

    use serial_test::serial;
    use smartstring::alias::String as SmartString;

    #[test]
    #[serial]
    fn test_isize() {
        let mut vm = VM::new_no_bootstrap();

        let v = Val::from_isize(&mut vm, 0);
        assert_eq!(v.valkind(), ValKind::INT);
        assert_eq!(v.as_usize(&mut vm).unwrap(), 0);
        assert_eq!(v.as_isize(&mut vm).unwrap(), 0);

        let v = Val::from_isize(&mut vm, -1);
        assert_eq!(v.valkind(), ValKind::INT);
        assert!(v.as_usize(&mut vm).is_err());
        assert_eq!(v.as_isize(&mut vm).unwrap(), -1);

        let v = Val::from_isize(&mut vm, isize::min_value());
        assert_eq!(v.valkind(), ValKind::GCBOX);
        assert_eq!(v.as_isize(&mut vm).unwrap(), isize::min_value());
        let v = Val::from_isize(&mut vm, isize::max_value());
        assert_eq!(v.valkind(), ValKind::GCBOX);
        assert_eq!(v.as_isize(&mut vm).unwrap(), isize::max_value());

        let v = Val::from_isize(&mut vm, 1 << (BITSIZE - 1 - TAG_BITSIZE) - 1);
        assert_eq!(v.valkind(), ValKind::INT);
        assert_eq!(
            v.as_usize(&mut vm).unwrap(),
            1 << (BITSIZE - 1 - TAG_BITSIZE) - 1
        );
        assert_eq!(
            v.as_isize(&mut vm).unwrap(),
            1 << (BITSIZE - 1 - TAG_BITSIZE) - 1
        );

        let v = Val::from_isize(&mut vm, 1 << (BITSIZE - 2));
        assert_eq!(v.valkind(), ValKind::GCBOX);
        assert_eq!(v.as_usize(&mut vm).unwrap(), 1 << (BITSIZE - 2));
        assert_eq!(v.as_isize(&mut vm).unwrap(), 1 << (BITSIZE - 2));
    }

    #[test]
    #[serial]
    fn test_usize() {
        let mut vm = VM::new_no_bootstrap();

        let v = Val::from_usize(&mut vm, 0);
        assert_eq!(v.valkind(), ValKind::INT);
        assert_eq!(v.as_usize(&mut vm).unwrap(), 0);
        assert_eq!(v.as_isize(&mut vm).unwrap(), 0);

        let v = Val::from_usize(&mut vm, 1 << (BITSIZE - 1 - TAG_BITSIZE) - 1);
        assert_eq!(v.valkind(), ValKind::INT);
        assert_eq!(
            v.as_usize(&mut vm).unwrap(),
            1 << (BITSIZE - 1 - TAG_BITSIZE) - 1
        );
        assert_eq!(
            v.as_isize(&mut vm).unwrap(),
            1 << (BITSIZE - 1 - TAG_BITSIZE) - 1
        );

        assert!(Val::from_usize(&mut vm, 1 << (BITSIZE - 1))
            .try_downcast::<ArbInt>(&mut vm)
            .is_some());

        let v = Val::from_usize(&mut vm, 1 << (BITSIZE - 2));
        assert_eq!(v.valkind(), ValKind::GCBOX);
        assert_eq!(v.as_usize(&mut vm).unwrap(), 1 << (BITSIZE - 2));
        assert_eq!(v.as_isize(&mut vm).unwrap(), 1 << (BITSIZE - 2));

        let v = String_::new_str(&mut vm, SmartString::new());
        assert!(v.as_usize(&mut vm).is_err());
    }

    #[test]
    #[serial]
    fn test_recovery() {
        let mut vm = VM::new_no_bootstrap();

        let v = {
            let v = String_::new_str(&mut vm, SmartString::from("s"));
            let v_tobj = v.tobj(&mut vm).unwrap();
            let v_str: Gc<String_> = v_tobj.downcast().unwrap();
            let v_recovered = Val::recover(v_str);
            assert_eq!(v_recovered.val, v.val);
            v_recovered
        };
        // At this point, we will have dropped one of the references to the String above so the
        // assertion below is really checking that we're not doing a read after free.
        assert_eq!(v.downcast::<String_>(&mut vm).unwrap().as_str(), "s");
    }

    #[test]
    #[serial]
    fn test_cast() {
        let mut vm = VM::new_no_bootstrap();
        let v = String_::new_str(&mut vm, SmartString::from("s"));
        assert!(v.downcast::<String_>(&mut vm).is_ok());
        assert_eq!(
            v.downcast::<Class>(&mut vm).unwrap_err().kind,
            VMErrorKind::BuiltinTypeError {
                expected: ObjType::Class,
                got: ObjType::String_
            }
        );
    }

    #[test]
    #[serial]
    fn test_downcast() {
        let mut vm = VM::new_no_bootstrap();
        let v = String_::new_str(&mut vm, SmartString::from("s"));
        assert!(v.downcast::<String_>(&mut vm).is_ok());
        assert!(v.downcast::<Class>(&mut vm).is_err());
        assert!(v.try_downcast::<String_>(&mut vm).is_some());
        assert!(v.try_downcast::<Class>(&mut vm).is_none());

        let v = Val::from_isize(&mut vm, 0);
        assert!(v.downcast::<String_>(&mut vm).is_err());
        assert!(v.try_downcast::<String_>(&mut vm).is_none());
    }
}
