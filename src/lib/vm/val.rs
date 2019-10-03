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
    mem::{forget, size_of, transmute},
    ops::Deref,
};

use abgc::{self, Gc};
use num_bigint::BigInt;
use num_enum::{IntoPrimitive, UnsafeFromPrimitive};
use num_traits::FromPrimitive;

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
pub const TAG_BITSIZE: usize = 3; // Number of bits
#[cfg(target_pointer_width = "64")]
pub const TAG_BITMASK: usize = (1 << 3) - 1;
#[cfg(target_pointer_width = "64")]
pub const INT_BITMASK: usize = (1 << 4) - 1;

#[cfg(target_pointer_width = "64")]
/// If a member of ValResult has this bit set, it is a `Box<VMError>`.
const VALRESULT_ERR_BIT: usize = 0b010;

#[cfg(target_pointer_width = "64")]
#[derive(Debug, PartialEq, IntoPrimitive, UnsafeFromPrimitive)]
#[repr(usize)]
// All of the values here must:
//   1) Fit inside TAG_BITSIZE bits
//   2) Safely convert to usize using `as`
//   3) Not have the VALRESULT_ERR_BIT bit set or else `ValResult` will do weird things.
pub enum ValKind {
    GCBOX = 0b000,
    // Anything which can be stored unboxed *must* not have the `NotUnboxable` trait implemented
    // for them. In other words, if an existing type is added to the list of unboxable things, you
    // need to check whether it implemented `NotUnboxable` and, if so, remove that implementation.
    INT = 0b001,
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
    pub(crate) val: usize,
}

impl Val {
    /// Create a `Val` from a given instance of the `Obj` trait.
    ///
    /// [In an ideal world, this would be a function on `Obj` itself, but that would mean that
    /// `Obj` couldn't be a trait object. Oh well.]
    pub fn from_obj<T: Obj + 'static>(_: &VM, obj: T) -> Self {
        debug_assert_eq!(ValKind::GCBOX as usize, 0);
        debug_assert_eq!(size_of::<*const ThinObj>(), size_of::<usize>());
        let ptr = ThinObj::new(obj).into_raw();
        Val {
            val: unsafe { transmute::<*const ThinObj, usize>(ptr) },
        }
    }

    /// Convert `obj` into a `Val`. `Obj` must previously have been created via `Val::from_obj` and
    /// then turned into an actual object with `tobj`: failure to follow these steps will result in
    /// undefined behaviour.
    pub fn recover(obj: &dyn Obj) -> Self {
        unsafe {
            let ptr = ThinObj::recover(obj).into_raw();
            Val {
                val: transmute::<*const ThinObj, usize>(ptr),
            }
        }
    }

    /// Create a value upon which all operations are invalid. This can be used as a sentinel or
    /// while initialising part of the system.
    pub fn illegal() -> Val {
        Val { val: 0 }
    }

    /// Is this `Var` illegal i.e. is it an empty placeholder waiting for a "proper" value?
    pub fn is_illegal(&self) -> bool {
        self.val == 0
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
                let tobj = unsafe { &*(self.val as *const ThinObj) };
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
        match self.valkind() {
            ValKind::INT => None,
            ValKind::GCBOX => unsafe { &*(self.val as *const ThinObj) }.downcast(),
        }
    }

    /// Return this `Val`'s box. If the `Val` refers to an unboxed value, this will box it.
    pub fn tobj(&self, vm: &VM) -> Result<Gc<ThinObj>, Box<VMError>> {
        match self.valkind() {
            ValKind::GCBOX => {
                debug_assert_eq!(ValKind::GCBOX as usize, 0);
                debug_assert_eq!(size_of::<*const ThinObj>(), size_of::<usize>());
                debug_assert_ne!(self.val, 0);
                Ok(unsafe { Gc::clone_from_raw(self.val as *const _) })
            }
            ValKind::INT => {
                let vr = Int::boxed_isize(vm, self.as_isize(vm).unwrap());
                if vr.is_val() {
                    vr.unwrap().tobj(vm)
                } else {
                    Err(vr.unwrap_err())
                }
            }
        }
    }

    /// Create a (possibly boxed) `Val` representing the `isize` integer `i`.
    pub fn from_isize(vm: &VM, i: isize) -> ValResult {
        let top_bits = i as usize & (INT_BITMASK << (BITSIZE - TAG_BITSIZE - 1));
        if top_bits == 0 || top_bits == INT_BITMASK << (BITSIZE - TAG_BITSIZE - 1) {
            // top_bits == 0: A positive integer that fits in our tagging scheme
            // top_bits all set to 1: A negative integer that fits in our tagging scheme
            ValResult::from_val(Val {
                val: ((i as usize) << TAG_BITSIZE) | (ValKind::INT as usize),
            })
        } else {
            Int::boxed_isize(vm, i)
        }
    }

    /// Create a (possibly boxed) `Val` representing the `usize` integer `i`. Notice that this can
    /// fail if `i` is too big (since we don't have BigNum support and ints are internally
    /// represented as `isize`).
    pub fn from_usize(vm: &VM, i: usize) -> ValResult {
        if i & (INT_BITMASK << (BITSIZE - TAG_BITSIZE - 1)) == 0 {
            // The top TAG_BITSIZE bits aren't set, so this fits within our pointer tagging scheme.
            ValResult::from_val(Val {
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

    /// Produce a new `Val` which adds `other` to this.
    pub fn add(&self, vm: &VM, other: Val) -> ValResult {
        if let Some(lhs) = self.as_isize(vm) {
            if let Some(rhs) = other.as_isize(vm) {
                match lhs.checked_add(rhs) {
                    Some(i) => return Val::from_isize(vm, i),
                    None => {
                        return ArbInt::new(vm, BigInt::from_isize(lhs).unwrap() + rhs);
                    }
                }
            } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
                // The "obvious" way of implementing this is as:
                //   ArbInt::new(vm, BigInt::from_isize(lhs).unwrap() + rhs.bigint())
                // but because `+` is commutative, we can avoid creating a
                // temporary BigInt.
                return ArbInt::new(vm, rhs.bigint() + lhs);
            } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
                return ValResult::from_val(Double::new(vm, (lhs as f64) + rhs.double()));
            }
            return ValResult::from_vmerror(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            });
        }
        self.tobj(vm).unwrap().add(vm, other)
    }

    /// Produce a new `Val` which subtracts `other` from this.
    pub fn sub(&self, vm: &VM, other: Val) -> ValResult {
        if let Some(lhs) = self.as_isize(vm) {
            if let Some(rhs) = other.as_isize(vm) {
                match lhs.checked_sub(rhs) {
                    Some(i) => return Val::from_isize(vm, i),
                    None => {
                        return ArbInt::new(vm, BigInt::from_isize(lhs).unwrap() - rhs);
                    }
                }
            } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
                return ArbInt::new(vm, BigInt::from_isize(lhs).unwrap() - rhs.bigint());
            } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
                return ValResult::from_val(Double::new(vm, (lhs as f64) - rhs.double()));
            }
            return ValResult::from_vmerror(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            });
        }
        self.tobj(vm).unwrap().sub(vm, other)
    }

    /// Produce a new `Val` which multiplies `other` to this.
    pub fn mul(&self, vm: &VM, other: Val) -> ValResult {
        if let Some(lhs) = self.as_isize(vm) {
            if let Some(rhs) = other.as_isize(vm) {
                match lhs.checked_mul(rhs) {
                    Some(i) => return Val::from_isize(vm, i),
                    None => {
                        return ArbInt::new(vm, BigInt::from_isize(lhs).unwrap() * rhs);
                    }
                }
            } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
                // The "obvious" way of implementing this is as:
                //   ArbInt::new(vm, BigInt::from_isize(lhs).unwrap() * rhs.bigint())
                // but because `*` is commutative, we can avoid creating a
                // temporary BigInt.
                return ArbInt::new(vm, rhs.bigint() * lhs);
            } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
                return ValResult::from_val(Double::new(vm, (lhs as f64) * rhs.double()));
            }
            return ValResult::from_vmerror(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            });
        }
        self.tobj(vm).unwrap().mul(vm, other)
    }

    /// Produce a new `Val` which divides `other` from this.
    pub fn div(&self, vm: &VM, other: Val) -> ValResult {
        if let Some(lhs) = self.as_isize(vm) {
            if let Some(rhs) = other.as_isize(vm) {
                match lhs.checked_div(rhs) {
                    Some(i) => return Val::from_isize(vm, i),
                    None => return ValResult::from_vmerror(VMError::DivisionByZero),
                }
            } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
                match BigInt::from_isize(lhs).unwrap().checked_div(rhs.bigint()) {
                    Some(i) => return ArbInt::new(vm, i),
                    None => return ValResult::from_vmerror(VMError::DivisionByZero),
                }
            } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
                if rhs.double() == 0f64 {
                    return ValResult::from_vmerror(VMError::DivisionByZero);
                } else {
                    // Note that converting an f64 to an isize in Rust can lead to undefined
                    // behaviour https://github.com/rust-lang/rust/issues/10184 -- it's not obvious
                    // that we can do anything about this other than wait for it to be fixed in
                    // LLVM and Rust.
                    return Val::from_isize(vm, ((lhs as f64) / rhs.double()) as isize);
                }
            }
            return ValResult::from_vmerror(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            });
        }
        self.tobj(vm).unwrap().div(vm, other)
    }

    /// Produce a new `Val` which shifts `self` `other` bits to the left.
    pub fn shl(&self, vm: &VM, other: Val) -> ValResult {
        if let Some(lhs) = self.as_isize(vm) {
            if let Some(rhs) = other.as_isize(vm) {
                if rhs < 0 {
                    return ValResult::from_vmerror(VMError::NegativeShift);
                } else {
                    let rhs_i =
                        rtry!(u32::try_from(rhs).map_err(|_| Box::new(VMError::ShiftTooBig)));
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
                return ValResult::from_vmerror(VMError::ShiftTooBig);
            }
            return ValResult::from_vmerror(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            });
        }
        self.tobj(vm).unwrap().shl(vm, other)
    }

    pub fn to_strval(&self, vm: &VM) -> ValResult {
        debug_assert!(!self.is_illegal());
        match self.valkind() {
            ValKind::INT => {
                ValResult::from_val(String_::new(vm, self.as_isize(vm).unwrap().to_string()))
            }
            ValKind::GCBOX => self.tobj(vm).unwrap().to_strval(vm),
        }
    }
}

macro_rules! binop_all {
    ($name:ident, $op:tt, $tf:ident) => {
        impl Val {
            pub fn $name(&self, vm: &VM, other: Val) -> ValResult {
                if let Some(lhs) = self.as_isize(vm) {
                    if let Some(rhs) = other.as_isize(vm) {
                        ValResult::from_val(Val::from_bool(vm, lhs $op rhs))
                    } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
                        ValResult::from_val(Val::from_bool(vm,
                            &BigInt::from_isize(lhs).unwrap() $op rhs.bigint()))
                    } else {
                        ValResult::from_val(vm.$tf.clone())
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
            pub fn $name(&self, vm: &VM, other: Val) -> ValResult {
                if let Some(lhs) = self.as_isize(vm) {
                    if let Some(rhs) = other.as_isize(vm) {
                        ValResult::from_val(Val::from_bool(vm, lhs $op rhs))
                    } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
                        ValResult::from_val(Val::from_bool(vm,
                            &BigInt::from_isize(lhs).unwrap() $op rhs.bigint()))
                    } else {
                        ValResult::from_vmerror(VMError::NotANumber {
                          got: other.dyn_objtype(vm),
                        })
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
        let val = match self.valkind() {
            ValKind::GCBOX => {
                if self.val != 0 {
                    unsafe {
                        transmute::<*const ThinObj, usize>(
                            Gc::<ThinObj>::clone_from_raw(self.val as *const _).into_raw(),
                        )
                    }
                } else {
                    0
                }
            }
            ValKind::INT => self.val,
        };
        Val { val }
    }
}

impl Drop for Val {
    fn drop(&mut self) {
        match self.valkind() {
            ValKind::GCBOX => {
                if self.val != 0 {
                    drop(unsafe { Gc::<ThinObj>::from_raw(self.val as *const _) });
                }
            }
            ValKind::INT => (),
        }
    }
}

/// A compact representation of a `Val` or a `Box<VMError>`.
#[derive(Debug, PartialEq)]
pub struct ValResult {
    // If VALRESULT_ERR_BIT is set, this is a `Box<VMError>`, otherwise it is a `Val`.
    val: usize,
}

impl ValResult {
    /// Construct a `ValResult` from a `Val`.
    pub fn from_val(val: Val) -> ValResult {
        let vr = ValResult { val: val.val };
        std::mem::forget(val);
        vr
    }

    /// Construct a `ValResult` from a `VMError`.
    pub fn from_vmerror(err: VMError) -> ValResult {
        let b = Box::new(err);
        let ptr = Box::into_raw(b) as *const usize as usize;
        ValResult {
            val: ptr | VALRESULT_ERR_BIT,
        }
    }

    /// Construct a `ValResult` from a `Box<VMError>`.
    pub fn from_boxvmerror(err: Box<VMError>) -> ValResult {
        let ptr = Box::into_raw(err) as *const usize as usize;
        ValResult {
            val: ptr | VALRESULT_ERR_BIT,
        }
    }

    /// Is this `ValResult` a `Val`? If not, it is one of the extra kinds defined in
    /// `ValResultKind`.
    pub fn is_val(&self) -> bool {
        (self.val & VALRESULT_ERR_BIT) == 0
    }

    /// Is this `ValResult` a `Box<VMError>`? If not, it is a `Val`.
    pub fn is_err(&self) -> bool {
        (self.val & VALRESULT_ERR_BIT) != 0
    }

    /// Unwraps a `ValResult`, yielding a `Val`.
    ///
    /// # Panics
    ///
    /// If the `ValResult` represents a `Box<VMError>`.
    pub fn unwrap(self) -> Val {
        if !self.is_val() {
            panic!("Trying to unwrap non-Val.");
        }
        unsafe { self.unwrap_unsafe() }
    }

    /// Unwraps a `ValResult`, yielding a `Val` without checking whether this `ValResult` actually
    /// represents a `Val` or not.
    #[doc(hidden)]
    pub unsafe fn unwrap_unsafe(self) -> Val {
        let v = Val { val: self.val };
        forget(self);
        v
    }

    /// Unwraps a `ValResult`, yielding a `Val`. If the value is a `Box<VMError>` then it calls
    /// `op` with its value.
    pub fn unwrap_or_else<F: FnOnce(Box<VMError>) -> Val>(self, op: F) -> Val {
        if self.is_val() {
            unsafe { self.unwrap_unsafe() }
        } else {
            op(self.unwrap_err())
        }
    }

    /// Unwraps a `ValResult`, yielding a `Box<VMError>`.
    ///
    /// # Panics
    ///
    /// If the `ValResult` represents a `Val`.
    pub fn unwrap_err(self) -> Box<VMError> {
        if !self.is_err() {
            panic!("Trying to unwrap non-VMError.");
        }
        let ptr = (self.val & !VALRESULT_ERR_BIT) as *mut VMError;
        forget(self);
        unsafe { Box::from_raw(ptr) }
    }

    pub fn as_result(self) -> Result<Val, Box<VMError>> {
        if self.is_val() {
            Ok(unsafe { self.unwrap_unsafe() })
        } else {
            Err(self.unwrap_err())
        }
    }
}

impl Drop for ValResult {
    fn drop(&mut self) {
        if self.is_val() {
            drop(Val { val: self.val });
        } else {
            let ptr = (self.val & !TAG_BITMASK) as *mut VMError;
            drop(*unsafe { Box::from_raw(ptr) });
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
