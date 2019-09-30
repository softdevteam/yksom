// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

//! yksom has three ways of representing integers: as tagged integer (inside a `Val`); boxed
//! `isize`'s (the `Int` struct); and arbitrary sized integers (the `ArbInt` struct). This module
//! contains the implementations of [`Int`](Int) and [`ArbInt`](ArbInt).

#![allow(clippy::new_ret_no_self)]

use std::convert::TryFrom;

use abgc_derive::GcLayout;
use num_bigint::BigInt;
use num_traits::{FromPrimitive, ToPrimitive};

use crate::vm::{
    objects::{Double, Obj, ObjType, StaticObjType, String_},
    val::{NotUnboxable, Val, ValResult},
    vm::{VMError, VM},
};

#[derive(Debug, GcLayout)]
/// A boxed arbitrary sized `BigInt`.
pub struct ArbInt {
    val: BigInt,
}

impl NotUnboxable for ArbInt {}

impl Obj for ArbInt {
    fn dyn_objtype(&self) -> ObjType {
        ObjType::ArbInt
    }

    fn get_class(&self, vm: &VM) -> Val {
        vm.int_cls.clone()
    }

    fn to_strval(&self, vm: &VM) -> ValResult {
        ValResult::from_val(String_::new(vm, self.val.to_string()))
    }

    fn add(&self, vm: &VM, other: Val) -> ValResult {
        if let Some(rhs) = other.as_isize(vm) {
            ArbInt::new(vm, &self.val + rhs)
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            ArbInt::new(vm, &self.val + &rhs.val)
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            match self.val.to_f64() {
                Some(i) => ValResult::from_val(Double::new(vm, i + rhs.double())),
                None => ValResult::from_vmerror(VMError::CantRepresentAsDouble),
            }
        } else {
            ValResult::from_vmerror(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            })
        }
    }

    fn sub(&self, vm: &VM, other: Val) -> ValResult {
        if let Some(rhs) = other.as_isize(vm) {
            ArbInt::new(vm, &self.val - &rhs)
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            ArbInt::new(vm, &self.val - &rhs.val)
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            match self.val.to_f64() {
                Some(i) => ValResult::from_val(Double::new(vm, i - rhs.double())),
                None => ValResult::from_vmerror(VMError::CantRepresentAsDouble),
            }
        } else {
            ValResult::from_vmerror(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            })
        }
    }

    fn mul(&self, vm: &VM, other: Val) -> ValResult {
        if let Some(rhs) = other.as_isize(vm) {
            ArbInt::new(vm, &self.val * rhs)
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            ArbInt::new(vm, &self.val * &rhs.val)
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            match self.val.to_f64() {
                Some(i) => ValResult::from_val(Double::new(vm, i * rhs.double())),
                None => ValResult::from_vmerror(VMError::CantRepresentAsDouble),
            }
        } else {
            ValResult::from_vmerror(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            })
        }
    }

    fn div(&self, vm: &VM, other: Val) -> ValResult {
        if let Some(rhs) = other.as_isize(vm) {
            if rhs == 0 {
                ValResult::from_vmerror(VMError::DivisionByZero)
            } else {
                ArbInt::new(vm, &self.val / rhs)
            }
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            match self.val.checked_div(&rhs.val) {
                Some(i) => ArbInt::new(vm, i),
                None => ValResult::from_vmerror(VMError::DivisionByZero),
            }
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            if rhs.double() == 0f64 {
                ValResult::from_vmerror(VMError::DivisionByZero)
            } else {
                match self.val.to_f64() {
                    Some(i) => ValResult::from_val(Double::new(vm, i / rhs.double())),
                    None => ValResult::from_vmerror(VMError::CantRepresentAsDouble),
                }
            }
        } else {
            ValResult::from_vmerror(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            })
        }
    }

    fn shl(&self, vm: &VM, other: Val) -> ValResult {
        if let Some(rhs) = other.as_isize(vm) {
            if rhs < 0 {
                ValResult::from_vmerror(VMError::NegativeShift)
            } else {
                let rhs_i = rtry!(usize::try_from(rhs).map_err(|_| Box::new(VMError::ShiftTooBig)));
                ArbInt::new(vm, &self.val << rhs_i)
            }
        } else if let Some(_) = other.try_downcast::<ArbInt>(vm) {
            ValResult::from_vmerror(VMError::ShiftTooBig)
        } else {
            ValResult::from_vmerror(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            })
        }
    }

    fn equals(&self, vm: &VM, other: Val) -> ValResult {
        let b = if other.dyn_objtype(vm) == ObjType::Int {
            debug_assert!(self.val != BigInt::from_isize(other.as_isize(vm).unwrap()).unwrap());
            false
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            self.val == rhs.val
        } else {
            false
        };
        ValResult::from_val(Val::from_bool(vm, b))
    }

    fn not_equals(&self, vm: &VM, other: Val) -> ValResult {
        let b = if other.dyn_objtype(vm) == ObjType::Int {
            debug_assert!(self.val != BigInt::from_isize(other.as_isize(vm).unwrap()).unwrap());
            true
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            self.val != rhs.val
        } else {
            true
        };
        ValResult::from_val(Val::from_bool(vm, b))
    }

    fn greater_than(&self, vm: &VM, other: Val) -> ValResult {
        let b = if other.dyn_objtype(vm) == ObjType::Int {
            debug_assert!(self.val > BigInt::from_isize(other.as_isize(vm).unwrap()).unwrap());
            true
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            self.val > rhs.val
        } else {
            return ValResult::from_vmerror(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            });
        };
        ValResult::from_val(Val::from_bool(vm, b))
    }

    fn greater_than_equals(&self, vm: &VM, other: Val) -> ValResult {
        let b = if other.dyn_objtype(vm) == ObjType::Int {
            debug_assert!(self.val >= BigInt::from_isize(other.as_isize(vm).unwrap()).unwrap());
            true
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            self.val >= rhs.val
        } else {
            return ValResult::from_vmerror(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            });
        };
        ValResult::from_val(Val::from_bool(vm, b))
    }

    fn less_than(&self, vm: &VM, other: Val) -> ValResult {
        let b = if other.dyn_objtype(vm) == ObjType::Int {
            debug_assert!(self.val < BigInt::from_isize(other.as_isize(vm).unwrap()).unwrap());
            false
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            self.val < rhs.val
        } else {
            return ValResult::from_vmerror(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            });
        };
        ValResult::from_val(Val::from_bool(vm, b))
    }

    fn less_than_equals(&self, vm: &VM, other: Val) -> ValResult {
        let b = if other.dyn_objtype(vm) == ObjType::Int {
            debug_assert!(self.val <= BigInt::from_isize(other.as_isize(vm).unwrap()).unwrap());
            false
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            self.val <= rhs.val
        } else {
            return ValResult::from_vmerror(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            });
        };
        ValResult::from_val(Val::from_bool(vm, b))
    }
}

impl StaticObjType for ArbInt {
    fn static_objtype() -> ObjType {
        ObjType::ArbInt
    }
}

impl ArbInt {
    /// Create a `Val` representing the `BigInt` integer `val`. Note that this will create the most
    /// efficient integer representation that can represent `val` (i.e. this might create a tagged
    /// `isize`, a boxed `isize`, or a boxed `BigInt`) -- the VM relies, in various places, on this
    /// property (e.g. an `ArbInt` with a value `1` would cause odd errors elsewhere).
    pub fn new(vm: &VM, val: BigInt) -> ValResult {
        if let Some(i) = val.to_isize() {
            Val::from_isize(vm, i)
        } else {
            ValResult::from_val(Val::from_obj(vm, ArbInt { val }))
        }
    }

    pub fn bigint(&self) -> &BigInt {
        &self.val
    }
}

#[derive(Debug, GcLayout)]
/// A boxed `isize`.
pub struct Int {
    val: isize,
}

impl Obj for Int {
    fn dyn_objtype(&self) -> ObjType {
        ObjType::Int
    }

    fn get_class(&self, vm: &VM) -> Val {
        vm.int_cls.clone()
    }

    fn to_strval(&self, vm: &VM) -> ValResult {
        ValResult::from_val(String_::new(vm, self.val.to_string()))
    }
}

impl StaticObjType for Int {
    fn static_objtype() -> ObjType {
        ObjType::Int
    }
}

impl Int {
    /// Create a `Val` representing the `usize` integer `i`. The `Val` is guaranteed to be boxed
    /// internally.
    pub fn boxed_isize(vm: &VM, i: isize) -> ValResult {
        ValResult::from_val(Val::from_obj(vm, Int { val: i }))
    }

    pub fn as_isize(&self) -> isize {
        self.val
    }

    pub fn as_usize(&self) -> Option<usize> {
        if self.val >= 0 {
            Some(self.val as usize)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm::val::{ValKind, BITSIZE, TAG_BITSIZE};
    use std::str::FromStr;

    #[test]
    fn test_boxed_int() {
        let vm = VM::new_no_bootstrap();

        assert_eq!(Val::from_isize(&vm, 12345).unwrap().valkind(), ValKind::INT);
        assert_eq!(
            Int::boxed_isize(&vm, 12345).unwrap().valkind(),
            ValKind::GCBOX
        );

        let v = Val::from_isize(&vm, 12345).unwrap();
        assert_eq!(
            v.tobj(&vm)
                .unwrap()
                .downcast::<Int>()
                .unwrap()
                .as_usize()
                .unwrap(),
            v.as_usize(&vm).unwrap()
        );
    }

    #[test]
    fn test_bint() {
        let vm = VM::new_no_bootstrap();

        assert_eq!(Val::from_isize(&vm, 0).unwrap().valkind(), ValKind::INT);
        assert_eq!(
            Val::from_isize(&vm, 1 << (BITSIZE - 1 - TAG_BITSIZE))
                .unwrap()
                .valkind(),
            ValKind::GCBOX
        );
        assert_eq!(
            Val::from_isize(&vm, -1 - 1 << (BITSIZE - 1 - TAG_BITSIZE))
                .unwrap()
                .valkind(),
            ValKind::GCBOX
        );
        assert_eq!(
            Val::from_isize(&vm, 1 << (BITSIZE - 1)).unwrap().valkind(),
            ValKind::GCBOX
        );
        assert_eq!(
            Val::from_isize(&vm, isize::min_value())
                .unwrap()
                .add(&vm, Val::from_isize(&vm, isize::min_value()).unwrap())
                .unwrap()
                .downcast::<ArbInt>(&vm)
                .unwrap()
                .val,
            BigInt::from_str("-18446744073709551616").unwrap()
        );
        // Check that sizes "downsize" from more expensive to cheaper types.
        assert_eq!(
            Val::from_isize(&vm, isize::max_value())
                .unwrap()
                .sub(&vm, Val::from_isize(&vm, isize::max_value()).unwrap())
                .unwrap()
                .valkind(),
            ValKind::INT
        );
        let bi = Val::from_isize(&vm, isize::max_value())
            .unwrap()
            .add(&vm, Val::from_isize(&vm, 10).unwrap())
            .unwrap();
        assert!(bi.downcast::<ArbInt>(&vm).is_ok());
        assert_eq!(
            bi.tobj(&vm)
                .unwrap()
                .sub(&vm, Val::from_isize(&vm, 1 << (TAG_BITSIZE + 2)).unwrap())
                .unwrap()
                .valkind(),
            ValKind::GCBOX
        );
        assert_eq!(
            bi.tobj(&vm)
                .unwrap()
                .sub(&vm, Val::from_isize(&vm, isize::max_value()).unwrap())
                .unwrap()
                .valkind(),
            ValKind::INT
        );
        // Different LHS and RHS types
        assert!(Val::from_isize(&vm, 1)
            .unwrap()
            .add(&vm, bi.clone())
            .unwrap()
            .downcast::<ArbInt>(&vm)
            .is_ok());
        assert!(Val::from_isize(&vm, 1)
            .unwrap()
            .sub(&vm, bi.clone())
            .unwrap()
            .downcast::<ArbInt>(&vm)
            .is_ok());
        assert!(Val::from_isize(&vm, 1)
            .unwrap()
            .mul(&vm, bi.clone())
            .unwrap()
            .downcast::<ArbInt>(&vm)
            .is_ok());
        assert_eq!(
            Val::from_isize(&vm, 1)
                .unwrap()
                .div(&vm, bi.clone())
                .unwrap()
                .valkind(),
            ValKind::INT
        );

        assert!(bi
            .clone()
            .add(&vm, Val::from_isize(&vm, 1).unwrap())
            .unwrap()
            .downcast::<ArbInt>(&vm)
            .is_ok());
        assert!(bi
            .clone()
            .sub(&vm, Val::from_isize(&vm, 1).unwrap())
            .unwrap()
            .downcast::<ArbInt>(&vm)
            .is_ok());
        assert!(bi
            .clone()
            .mul(&vm, Val::from_isize(&vm, 1).unwrap())
            .unwrap()
            .downcast::<ArbInt>(&vm)
            .is_ok());
        assert_eq!(
            bi.clone()
                .div(&vm, Val::from_isize(&vm, 99999999).unwrap())
                .unwrap()
                .valkind(),
            ValKind::INT
        );
    }
}
