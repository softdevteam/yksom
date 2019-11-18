// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

//! Tagged pointer support.

#![allow(clippy::new_ret_no_self)]

use std::{
    convert::TryFrom,
    mem::{size_of, transmute},
    ops::Deref,
};

use abgc::{self, Gc};
use num_bigint::BigInt;
use num_enum::{IntoPrimitive, UnsafeFromPrimitive};
use num_traits::{FromPrimitive, ToPrimitive, Zero};

use super::{
    core::{VMError, VM},
    objects::{ArbInt, Double, Int, Obj, ObjType, StaticObjType, String_, ThinObj},
};

// We use a fairly standard pointer tagging model where the low `TAG_BITSIZE` bits of a machine
// word (represented as a Rust `usize`) are used to store the type of the value (with the
// possibilities enumerated in `ValKind` below).

#[cfg(target_pointer_width = "64")]
pub const BITSIZE: usize = 64;
#[cfg(target_pointer_width = "64")]
pub const TAG_BITSIZE: usize = 1; // Number of bits
#[cfg(target_pointer_width = "64")]
pub const TAG_BITMASK: usize = 0b1;
#[cfg(target_pointer_width = "64")]
pub const INT_BITMASK: usize = 0b11;

#[cfg(target_pointer_width = "64")]
#[derive(Debug, PartialEq, IntoPrimitive, UnsafeFromPrimitive)]
#[repr(usize)]
// All of the values here must:
//   1) Fit inside TAG_BITSIZE bits
//   2) Safely convert to usize using `as`
pub enum ValKind {
    GCBOX = 0b1,
    // Anything which can be stored unboxed *must* not have the `NotUnboxable` trait implemented
    // for them. In other words, if an existing type is added to the list of unboxable things, you
    // need to check whether it implemented `NotUnboxable` and, if so, remove that implementation.
    INT = 0b0,
}

/// Objects which `impl` this trait guarantee that they can only ever be stored boxed.
/// Implementing this trait on objects which can be stored unboxed leads to undefined behaviour.
pub trait NotUnboxable {}

/// The core struct representing values in the language runtime: boxed and unboxed values are
/// hidden behind this, such that they can be treated in exactly the same way.
#[derive(Debug, PartialEq)]
pub struct Val {
    // We use this usize for pointer tagging. Needless to say, this is highly dangerous, and needs
    // several parts of the code to cooperate in order to be correct.
    val: usize,
}

impl Val {
    /// Create a `Val` from a given instance of the `Obj` trait.
    ///
    /// [In an ideal world, this would be a function on `Obj` itself, but that would mean that
    /// `Obj` couldn't be a trait object. Oh well.]
    pub fn from_obj<T: Obj + 'static>(_: &VM, obj: T) -> Self {
        debug_assert_eq!(size_of::<*const ThinObj>(), size_of::<usize>());
        let ptr = ThinObj::new(obj).into_raw();
        Val {
            val: unsafe { transmute::<*const ThinObj, usize>(ptr) | (ValKind::GCBOX as usize) },
        }
    }

    /// If this `Val` is a `GCBox` then convert it into `ThinObj`; if this `Val` is not a `GCBox`
    /// then undefined behaviour will occur (hence why this function is `unsafe`).
    unsafe fn val_to_tobj(&self) -> &ThinObj {
        debug_assert_eq!(self.valkind(), ValKind::GCBOX);
        let ptr = (self.val & !(ValKind::GCBOX as usize)) as *const ThinObj;
        &*ptr
    }

    /// Convert `obj` into a `Val`. `Obj` must previously have been created via `Val::from_obj` and
    /// then turned into an actual object with `tobj`: failure to follow these steps will result in
    /// undefined behaviour.
    pub fn recover(obj: &dyn Obj) -> Self {
        unsafe {
            let ptr = ThinObj::recover(obj).into_raw();
            Val {
                val: transmute::<*const ThinObj, usize>(ptr) | (ValKind::GCBOX as usize),
            }
        }
    }

    /// Create a value upon which all operations are invalid. This can be used as a sentinel or
    /// while initialising part of the system.
    pub fn illegal() -> Val {
        Val {
            val: ValKind::GCBOX as usize,
        }
    }

    /// Is this `Var` illegal i.e. is it an empty placeholder waiting for a "proper" value?
    pub fn is_illegal(&self) -> bool {
        self.val == (ValKind::GCBOX as usize)
    }

    pub fn valkind(&self) -> ValKind {
        // Since it should be impossible to create incorrect tags, in release mode, we want to make
        // this a zero-cost function (i.e. we get guarantees from the static type system but
        // without any run-time overhead). However, just in case someone does something silly, in
        // debug mode we explicitly check the tags.

        #[cfg(debug_assertions)]
        match self.val & TAG_BITMASK {
            x if x == ValKind::GCBOX as usize => (),
            x if x == ValKind::INT as usize => (),
            _ => panic!("Invalid tag {}", self.val & TAG_BITMASK),
        }

        unsafe { ValKind::from_unchecked(self.val & TAG_BITMASK) }
    }

    /// Cast a `Val` into an instance of type `T` (where `T` must statically be a type that cannot
    /// be boxed) or return a `VMError` if the cast is invalid.
    pub fn downcast<T: Obj + StaticObjType + NotUnboxable>(
        &self,
        _: &VM,
    ) -> Result<&T, Box<VMError>> {
        match self.valkind() {
            ValKind::INT => Err(Box::new(VMError::TypeError {
                expected: T::static_objtype(),
                got: Int::static_objtype(),
            })),
            ValKind::GCBOX => {
                let tobj = unsafe { self.val_to_tobj() };
                tobj.downcast().ok_or_else(|| {
                    Box::new(VMError::TypeError {
                        expected: T::static_objtype(),
                        got: tobj.deref().dyn_objtype(),
                    })
                })
            }
        }
    }

    /// Cast a `Val` into an instance of type `T` (where `T` must statically be a type that cannot
    /// be boxed) or return `None` if the cast is not valid.
    pub fn try_downcast<T: Obj + StaticObjType + NotUnboxable>(&self, _: &VM) -> Option<&T> {
        debug_assert!(!self.is_illegal());
        match self.valkind() {
            ValKind::INT => None,
            ValKind::GCBOX => unsafe { self.val_to_tobj() }.downcast(),
        }
    }

    /// Return this `Val`'s box. If the `Val` refers to an unboxed value, this will box it.
    pub fn tobj(&self, vm: &VM) -> Result<Gc<ThinObj>, Box<VMError>> {
        debug_assert!(!self.is_illegal());
        match self.valkind() {
            ValKind::GCBOX => {
                debug_assert_eq!(size_of::<*const ThinObj>(), size_of::<usize>());
                Ok(unsafe { Gc::clone_from_raw(self.val_to_tobj()) })
            }
            ValKind::INT => Int::boxed_isize(vm, self.as_isize(vm).unwrap()).map(|v| v.tobj(vm))?,
        }
    }

    /// Create a (possibly boxed) `Val` representing the `isize` integer `i`.
    pub fn from_isize(vm: &VM, i: isize) -> Result<Val, Box<VMError>> {
        let top_bits = i as usize & (INT_BITMASK << (BITSIZE - TAG_BITSIZE - 1));
        if top_bits == 0 || top_bits == INT_BITMASK << (BITSIZE - TAG_BITSIZE - 1) {
            // top_bits == 0: A positive integer that fits in our tagging scheme
            // top_bits all set to 1: A negative integer that fits in our tagging scheme
            Ok(Val {
                val: ((i as usize) << TAG_BITSIZE) | (ValKind::INT as usize),
            })
        } else {
            Int::boxed_isize(vm, i)
        }
    }

    /// Create a (possibly boxed) `Val` representing the `usize` integer `i`. Notice that this can
    /// fail if `i` is too big (since we don't have BigNum support and ints are internally
    /// represented as `isize`).
    pub fn from_usize(vm: &VM, i: usize) -> Result<Val, Box<VMError>> {
        if i & (INT_BITMASK << (BITSIZE - TAG_BITSIZE - 1)) == 0 {
            // The top TAG_BITSIZE bits aren't set, so this fits within our pointer tagging scheme.
            Ok(Val {
                val: (i << TAG_BITSIZE) | (ValKind::INT as usize),
            })
        } else {
            ArbInt::new(vm, BigInt::from_usize(i).unwrap())
        }
    }

    /// If `v == true`, return a `Val` representing `vm.true_`, otherwise return a `Val`
    /// representing `vm.false_`.
    pub fn from_bool(vm: &VM, v: bool) -> Val {
        if v {
            vm.true_.clone()
        } else {
            vm.false_.clone()
        }
    }

    /// If this `Val` represents a non-bigint integer, return its value as an `isize`.
    pub fn as_isize(&self, vm: &VM) -> Option<isize> {
        match self.valkind() {
            ValKind::GCBOX => self
                .tobj(vm)
                .unwrap()
                .downcast::<Int>()
                .map(|tobj| tobj.as_isize()),
            ValKind::INT => {
                if self.val & 1 << (BITSIZE - 1) == 0 {
                    Some((self.val >> TAG_BITSIZE) as isize)
                } else {
                    // For negative integers we need to pad the top TAG_BITSIZE bits with 1s.
                    Some(
                        ((self.val >> TAG_BITSIZE) | (TAG_BITMASK << (BITSIZE - TAG_BITSIZE)))
                            as isize,
                    )
                }
            }
        }
    }

    /// If this `Val` represents a non-bigint integer, return its value as an `usize`.
    pub fn as_usize(&self, vm: &VM) -> Option<usize> {
        match self.valkind() {
            ValKind::GCBOX => self
                .tobj(vm)
                .unwrap()
                .downcast::<Int>()
                .and_then(|tobj| tobj.as_usize()),
            ValKind::INT => {
                if self.val & 1 << (BITSIZE - 1) == 0 {
                    Some(self.val >> TAG_BITSIZE)
                } else {
                    None
                }
            }
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
    pub fn dyn_objtype(&self, vm: &VM) -> ObjType {
        debug_assert!(!self.is_illegal());
        match self.valkind() {
            ValKind::INT => ObjType::Int,
            ValKind::GCBOX => self.tobj(vm).unwrap().dyn_objtype(),
        }
    }

    /// What class is this `Val` an instance of?
    pub fn get_class(&self, vm: &VM) -> Val {
        debug_assert!(!self.is_illegal());
        match self.valkind() {
            ValKind::INT => vm.int_cls.clone(),
            ValKind::GCBOX => self.tobj(vm).unwrap().get_class(vm),
        }
    }

    pub fn to_strval(&self, vm: &VM) -> Result<Val, Box<VMError>> {
        debug_assert!(!self.is_illegal());
        match self.valkind() {
            ValKind::INT => Ok(String_::new(vm, self.as_isize(vm).unwrap().to_string())),
            ValKind::GCBOX => self.tobj(vm).unwrap().to_strval(vm),
        }
    }

    /// Produce a new `Val` which adds `other` to this.
    pub fn add(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        debug_assert_eq!(ValKind::INT as usize, 0);
        if self.valkind() == ValKind::INT && other.valkind() == ValKind::INT {
            if let Some(val) = self.val.checked_add(other.val) {
                return Ok(Val { val });
            }
        }
        self.tobj(vm).unwrap().add(vm, other)
    }

    /// Produce a new `Val` which performs a bitwise and operation with `other` and this.
    pub fn and(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Some(lhs) = self.as_isize(vm) {
            if let Some(rhs) = other.as_isize(vm) {
                return Val::from_isize(vm, lhs & rhs);
            } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
                return ArbInt::new(vm, BigInt::from_isize(lhs).unwrap() & rhs.bigint());
            }
            return Err(Box::new(VMError::TypeError {
                expected: self.dyn_objtype(vm),
                got: other.dyn_objtype(vm),
            }));
        }
        self.tobj(vm).unwrap().and(vm, other)
    }

    /// Produce a new `Val` which divides `other` from this.
    pub fn div(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        debug_assert_eq!(ValKind::INT as usize, 0);
        if self.valkind() == ValKind::INT && other.valkind() == ValKind::INT {
            if other.val != 0 {
                return Ok(Val {
                    val: (self.val / other.val) * (1 << TAG_BITSIZE),
                });
            } else {
                return Err(Box::new(VMError::DivisionByZero));
            }
        }
        self.tobj(vm).unwrap().div(vm, other)
    }

    /// Produce a new `Val` which perfoms a Double divide on `other` with this.
    pub fn double_div(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Some(lhs) = self.as_isize(vm) {
            if let Some(rhs) = other.as_isize(vm) {
                if rhs == 0 {
                    return Err(Box::new(VMError::DivisionByZero));
                } else {
                    return Ok(Double::new(vm, (lhs as f64) / (rhs as f64)));
                }
            } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
                if Zero::is_zero(rhs.bigint()) {
                    return Err(Box::new(VMError::DivisionByZero));
                } else if let Some(i) = rhs.bigint().to_f64() {
                    return Ok(Double::new(vm, (lhs as f64) / i));
                } else {
                    return Err(Box::new(VMError::CantRepresentAsDouble));
                }
            } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
                if rhs.double() == 0f64 {
                    return Err(Box::new(VMError::DivisionByZero));
                } else {
                    return Ok(Double::new(vm, (lhs as f64) / rhs.double()));
                }
            }
            return Err(Box::new(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            }));
        }
        self.tobj(vm).unwrap().double_div(vm, other)
    }

    /// Produce a new `Val` which performs a mod operation on this with `other`.
    pub fn modulus(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Some(lhs) = self.as_isize(vm) {
            if let Some(rhs) = other.as_isize(vm) {
                return Val::from_isize(vm, lhs % rhs);
            } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
                return ArbInt::new(vm, BigInt::from_isize(lhs).unwrap() % rhs.bigint());
            } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
                return Ok(Double::new(vm, (lhs as f64) % rhs.double()));
            }
            return Err(Box::new(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            }));
        }
        self.tobj(vm).unwrap().modulus(vm, other)
    }

    /// Produce a new `Val` which multiplies `other` to this.
    pub fn mul(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        debug_assert_eq!(ValKind::INT as usize, 0);
        if self.valkind() == ValKind::INT && other.valkind() == ValKind::INT {
            if let Some(val) = self.val.checked_mul(other.val / (1 << TAG_BITSIZE)) {
                return Ok(Val { val });
            }
        }
        self.tobj(vm).unwrap().mul(vm, other)
    }

    /// Produce a new `Val` which shifts `self` `other` bits to the left.
    pub fn shl(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Some(lhs) = self.as_isize(vm) {
            if let Some(rhs) = other.as_isize(vm) {
                if rhs < 0 {
                    return Err(Box::new(VMError::NegativeShift));
                } else {
                    let rhs_i = u32::try_from(rhs).map_err(|_| Box::new(VMError::ShiftTooBig))?;
                    if let Some(i) = lhs.checked_shl(rhs_i) {
                        // We have to be careful as shifting bits in an isize can lead to positive
                        // numbers becoming negative in two's complement. For example, on a 64-bit
                        // machine, (1isize<<63) == -9223372036854775808. To avoid this, if
                        // shifting +ve number leads to a -ve number being produced, we know we've
                        // exceeded an isize's ability to store the result, and need to fall back
                        // to the ArbInt case.
                        if lhs < 0 || (lhs > 0 && i > 0) {
                            return Val::from_isize(vm, i as isize);
                        }
                    }
                    return ArbInt::new(
                        vm,
                        BigInt::from_isize(lhs).unwrap() << usize::try_from(rhs_i).unwrap(),
                    );
                }
            }
            if other.try_downcast::<ArbInt>(vm).is_some() {
                return Err(Box::new(VMError::ShiftTooBig));
            }
            return Err(Box::new(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            }));
        }
        self.tobj(vm).unwrap().shl(vm, other)
    }

    /// Produces a new `Val` which is the square root of this.
    pub fn sqrt(&self, vm: &VM) -> Result<Val, Box<VMError>> {
        if let Some(lhs) = self.as_isize(vm) {
            if lhs < 0 {
                return Err(Box::new(VMError::DomainError));
            } else {
                let result = (lhs as f64).sqrt();
                if result.round() == result {
                    return Val::from_isize(vm, result as isize);
                } else {
                    return Ok(Double::new(vm, result));
                }
            }
        }
        self.tobj(vm).unwrap().sqrt(vm)
    }

    /// Produce a new `Val` which subtracts `other` from this.
    pub fn sub(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        debug_assert_eq!(ValKind::INT as usize, 0);
        if self.valkind() == ValKind::INT && other.valkind() == ValKind::INT {
            if let Some(val) = self.val.checked_sub(other.val) {
                return Ok(Val { val });
            }
        }
        self.tobj(vm).unwrap().sub(vm, other)
    }

    /// Produce a new `Val` which performs a bitwise xor operation with `other` and this.
    pub fn xor(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Some(lhs) = self.as_isize(vm) {
            if let Some(rhs) = other.as_isize(vm) {
                return Val::from_isize(vm, lhs ^ rhs);
            } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
                return ArbInt::new(vm, BigInt::from_isize(lhs).unwrap() ^ rhs.bigint());
            }
            return Err(Box::new(VMError::TypeError {
                expected: self.dyn_objtype(vm),
                got: other.dyn_objtype(vm),
            }));
        }
        self.tobj(vm).unwrap().xor(vm, other)
    }

    /// Is this `Val` reference equal to `other`? Notice that for integers (but not Doubles)
    /// "reference equal" is equivalent to "equals".
    pub fn ref_equals(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        match self.valkind() {
            ValKind::INT => self.equals(vm, other),
            ValKind::GCBOX => self.tobj(vm)?.ref_equals(vm, other),
        }
    }
}

macro_rules! binop_all {
    ($name:ident, $op:tt, $tf:ident) => {
        impl Val {
            pub fn $name(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
                if let Some(lhs) = self.as_isize(vm) {
                    if let Some(rhs) = other.as_isize(vm) {
                        Ok(Val::from_bool(vm, lhs $op rhs))
                    } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
                        Ok(Val::from_bool(vm,
                            &BigInt::from_isize(lhs).unwrap() $op rhs.bigint()))
                    } else {
                        Ok(vm.$tf.clone())
                    }
                } else {
                    self.tobj(vm).unwrap().$name(vm, other)
                }
            }
        }
    };
}

macro_rules! binop_typeerror {
    ($name:ident, $op:tt) => {
        impl Val {
            pub fn $name(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
                if let Some(lhs) = self.as_isize(vm) {
                    if let Some(rhs) = other.as_isize(vm) {
                        Ok(Val::from_bool(vm, lhs $op rhs))
                    } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
                        Ok(Val::from_bool(vm,
                            &BigInt::from_isize(lhs).unwrap() $op rhs.bigint()))
                    } else {
                        Err(Box::new(VMError::NotANumber {
                          got: other.dyn_objtype(vm),
                        }))
                    }
                } else {
                    self.tobj(vm).unwrap().$name(vm, other)
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

impl Clone for Val {
    fn clone(&self) -> Self {
        debug_assert!(!self.is_illegal());
        let val = match self.valkind() {
            ValKind::GCBOX => unsafe {
                transmute::<*const ThinObj, usize>(
                    Gc::<ThinObj>::clone_from_raw(self.val_to_tobj()).into_raw(),
                ) | (ValKind::GCBOX as usize)
            },
            ValKind::INT => self.val,
        };
        Val { val }
    }
}

impl Drop for Val {
    fn drop(&mut self) {
        if !self.is_illegal() {
            match self.valkind() {
                ValKind::GCBOX => {
                    drop(unsafe { Gc::<ThinObj>::from_raw(self.val_to_tobj()) });
                }
                ValKind::INT => (),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm::{
        core::{VMError, VM},
        objects::{Class, ObjType, String_},
    };

    use std::ops::Deref;

    #[test]
    fn test_isize() {
        let vm = VM::new_no_bootstrap();

        let v = Val::from_isize(&vm, 0).unwrap();
        assert_eq!(v.valkind(), ValKind::INT);
        assert_eq!(v.as_usize(&vm).unwrap(), 0);
        assert_eq!(v.as_isize(&vm).unwrap(), 0);

        let v = Val::from_isize(&vm, -1).unwrap();
        assert_eq!(v.valkind(), ValKind::INT);
        assert!(v.as_usize(&vm).is_none());
        assert_eq!(v.as_isize(&vm).unwrap(), -1);

        let v = Val::from_isize(&vm, isize::min_value()).unwrap();
        assert_eq!(v.valkind(), ValKind::GCBOX);
        assert_eq!(v.as_isize(&vm).unwrap(), isize::min_value());
        let v = Val::from_isize(&vm, isize::max_value()).unwrap();
        assert_eq!(v.valkind(), ValKind::GCBOX);
        assert_eq!(v.as_isize(&vm).unwrap(), isize::max_value());

        let v = Val::from_isize(&vm, 1 << (BITSIZE - 1 - TAG_BITSIZE) - 1).unwrap();
        assert_eq!(v.valkind(), ValKind::INT);
        assert_eq!(
            v.as_usize(&vm).unwrap(),
            1 << (BITSIZE - 1 - TAG_BITSIZE) - 1
        );
        assert_eq!(
            v.as_isize(&vm).unwrap(),
            1 << (BITSIZE - 1 - TAG_BITSIZE) - 1
        );

        let v = Val::from_isize(&vm, 1 << (BITSIZE - 2)).unwrap();
        assert_eq!(v.valkind(), ValKind::GCBOX);
        assert_eq!(v.as_usize(&vm).unwrap(), 1 << (BITSIZE - 2));
        assert_eq!(v.as_isize(&vm).unwrap(), 1 << (BITSIZE - 2));
    }

    #[test]
    fn test_usize() {
        let vm = VM::new_no_bootstrap();

        let v = Val::from_usize(&vm, 0).unwrap();
        assert_eq!(v.valkind(), ValKind::INT);
        assert_eq!(v.as_usize(&vm).unwrap(), 0);
        assert_eq!(v.as_isize(&vm).unwrap(), 0);

        let v = Val::from_usize(&vm, 1 << (BITSIZE - 1 - TAG_BITSIZE) - 1).unwrap();
        assert_eq!(v.valkind(), ValKind::INT);
        assert_eq!(
            v.as_usize(&vm).unwrap(),
            1 << (BITSIZE - 1 - TAG_BITSIZE) - 1
        );
        assert_eq!(
            v.as_isize(&vm).unwrap(),
            1 << (BITSIZE - 1 - TAG_BITSIZE) - 1
        );

        assert!(Val::from_usize(&vm, 1 << (BITSIZE - 1))
            .unwrap()
            .try_downcast::<ArbInt>(&vm)
            .is_some());

        let v = Val::from_usize(&vm, 1 << (BITSIZE - 2)).unwrap();
        assert_eq!(v.valkind(), ValKind::GCBOX);
        assert_eq!(v.as_usize(&vm).unwrap(), 1 << (BITSIZE - 2));
        assert_eq!(v.as_isize(&vm).unwrap(), 1 << (BITSIZE - 2));
    }

    #[test]
    fn test_recovery() {
        let vm = VM::new_no_bootstrap();

        let v = {
            let v = String_::new(&vm, "s".to_owned());
            let v_tobj = v.tobj(&vm).unwrap();
            let v_int: &dyn Obj = v_tobj.deref().deref();
            let v_recovered = Val::recover(v_int);
            assert_eq!(v_recovered.val, v.val);
            v_recovered
        };
        // At this point, we will have dropped one of the references to the String above so the
        // assertion below is really checking that we're not doing a read after free.
        assert_eq!(v.downcast::<String_>(&vm).unwrap().as_str(), "s");
    }

    #[test]
    fn test_cast() {
        let vm = VM::new_no_bootstrap();
        let v = String_::new(&vm, "s".to_owned());
        assert!(v.downcast::<String_>(&vm).is_ok());
        assert_eq!(
            *v.downcast::<Class>(&vm).unwrap_err(),
            VMError::TypeError {
                expected: ObjType::Class,
                got: ObjType::String_
            }
        );
    }

    #[test]
    fn test_downcast() {
        let vm = VM::new_no_bootstrap();
        let v = String_::new(&vm, "s".to_owned());
        assert!(v.downcast::<String_>(&vm).is_ok());
        assert!(v.downcast::<Class>(&vm).is_err());
        assert!(v.try_downcast::<String_>(&vm).is_some());
        assert!(v.try_downcast::<Class>(&vm).is_none());

        let v = Val::from_isize(&vm, 0).unwrap();
        assert!(v.downcast::<String_>(&vm).is_err());
        assert!(v.try_downcast::<String_>(&vm).is_none());
    }
}
