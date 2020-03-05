//! yksom has three ways of representing integers: as tagged integer (inside a `Val`); boxed
//! `isize`'s (the `Int` struct); and arbitrary sized integers (the `ArbInt` struct). This module
//! contains the implementations of [`Int`](Int) and [`ArbInt`](ArbInt).
//!
//! There is an implicit constraint between `ArbInt` and the other two types of integers: an
//! `ArbInt` must never be small enough to fit in a boxed isize (or, by extension, in a tagged
//! integer). That means that any operations which might narrow an `ArbInt` need to check whether
//! the result is now small enough to fit in one of the smaller integer types. Note that there is
//! no such constraint between tagged and boxed integers: sometimes integers that are small enough
//! to be tagged are boxed (mostly for convenience).

#![allow(clippy::new_ret_no_self)]

use std::convert::TryFrom;

use abgc_derive::GcLayout;
use num_bigint::BigInt;
use num_traits::{FromPrimitive, ToPrimitive, Zero};

use crate::vm::{
    core::VM,
    error::{VMError, VMErrorKind},
    objects::{Double, Obj, ObjType, StaticObjType, String_},
    val::{NotUnboxable, Val},
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

    fn to_strval(&self, vm: &VM) -> Result<Val, Box<VMError>> {
        Ok(String_::new(vm, self.val.to_string(), true))
    }

    fn add(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Some(rhs) = other.as_isize(vm) {
            ArbInt::new(vm, &self.val + rhs)
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            ArbInt::new(vm, &self.val + &rhs.val)
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            match self.val.to_f64() {
                Some(i) => Ok(Double::new(vm, i + rhs.double())),
                None => Err(VMError::new(vm, VMErrorKind::CantRepresentAsDouble)),
            }
        } else {
            Err(VMError::new(
                vm,
                VMErrorKind::NotANumber {
                    got: other.dyn_objtype(vm),
                },
            ))
        }
    }

    fn and(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Some(rhs) = other.as_isize(vm) {
            ArbInt::new(vm, &self.val & BigInt::from_isize(rhs).unwrap())
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            ArbInt::new(vm, &self.val & &rhs.val)
        } else {
            Err(VMError::new(
                vm,
                VMErrorKind::TypeError {
                    expected: self.dyn_objtype(),
                    got: other.dyn_objtype(vm),
                },
            ))
        }
    }

    fn div(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Some(rhs) = other.as_isize(vm) {
            if rhs == 0 {
                Err(VMError::new(vm, VMErrorKind::DivisionByZero))
            } else {
                ArbInt::new(vm, &self.val / rhs)
            }
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            match self.val.checked_div(&rhs.val) {
                Some(i) => ArbInt::new(vm, i),
                None => Err(VMError::new(vm, VMErrorKind::DivisionByZero)),
            }
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            if rhs.double() == 0f64 {
                Err(VMError::new(vm, VMErrorKind::DivisionByZero))
            } else {
                match self.val.to_f64() {
                    Some(i) => ArbInt::new(vm, BigInt::from_f64(i / rhs.double()).unwrap()),
                    None => Err(VMError::new(vm, VMErrorKind::CantRepresentAsDouble)),
                }
            }
        } else {
            Err(VMError::new(
                vm,
                VMErrorKind::NotANumber {
                    got: other.dyn_objtype(vm),
                },
            ))
        }
    }

    fn double_div(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Some(rhs) = other.as_isize(vm) {
            if rhs == 0 {
                Err(VMError::new(vm, VMErrorKind::DivisionByZero))
            } else if let Some(lhs) = self.val.to_f64() {
                Ok(Double::new(vm, lhs / (rhs as f64)))
            } else {
                Err(VMError::new(vm, VMErrorKind::CantRepresentAsDouble))
            }
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            if Zero::is_zero(rhs.bigint()) {
                Err(VMError::new(vm, VMErrorKind::DivisionByZero))
            } else if let Some(lhs) = self.val.to_f64() {
                if let Some(i) = rhs.bigint().to_f64() {
                    Ok(Double::new(vm, lhs / i))
                } else {
                    Err(VMError::new(vm, VMErrorKind::CantRepresentAsDouble))
                }
            } else {
                Err(VMError::new(vm, VMErrorKind::CantRepresentAsDouble))
            }
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            if rhs.double() == 0f64 {
                Err(VMError::new(vm, VMErrorKind::DivisionByZero))
            } else if let Some(lhs) = self.val.to_f64() {
                Ok(Double::new(vm, lhs / rhs.double()))
            } else {
                Err(VMError::new(vm, VMErrorKind::CantRepresentAsDouble))
            }
        } else {
            Err(VMError::new(
                vm,
                VMErrorKind::NotANumber {
                    got: other.dyn_objtype(vm),
                },
            ))
        }
    }

    fn modulus(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Some(rhs) = other.as_isize(vm) {
            ArbInt::new(vm, &self.val % rhs)
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            ArbInt::new(vm, &self.val % &rhs.val)
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            match self.val.to_f64() {
                Some(i) => Ok(Double::new(vm, i % rhs.double())),
                None => Err(VMError::new(vm, VMErrorKind::CantRepresentAsDouble)),
            }
        } else {
            Err(VMError::new(
                vm,
                VMErrorKind::NotANumber {
                    got: other.dyn_objtype(vm),
                },
            ))
        }
    }

    fn mul(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Some(rhs) = other.as_isize(vm) {
            ArbInt::new(vm, &self.val * rhs)
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            ArbInt::new(vm, &self.val * &rhs.val)
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            match self.val.to_f64() {
                Some(i) => Ok(Double::new(vm, i * rhs.double())),
                None => Err(VMError::new(vm, VMErrorKind::CantRepresentAsDouble)),
            }
        } else {
            Err(VMError::new(
                vm,
                VMErrorKind::NotANumber {
                    got: other.dyn_objtype(vm),
                },
            ))
        }
    }

    fn shl(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Some(rhs) = other.as_isize(vm) {
            if rhs < 0 {
                Err(VMError::new(vm, VMErrorKind::NegativeShift))
            } else {
                let rhs_i =
                    usize::try_from(rhs).map_err(|_| VMError::new(vm, VMErrorKind::ShiftTooBig))?;
                ArbInt::new(vm, &self.val << rhs_i)
            }
        } else if other.try_downcast::<ArbInt>(vm).is_some() {
            Err(VMError::new(vm, VMErrorKind::ShiftTooBig))
        } else {
            Err(VMError::new(
                vm,
                VMErrorKind::NotANumber {
                    got: other.dyn_objtype(vm),
                },
            ))
        }
    }

    fn sqrt(&self, vm: &VM) -> Result<Val, Box<VMError>> {
        if self.val < Zero::zero() {
            Err(VMError::new(vm, VMErrorKind::DomainError))
        } else {
            let result = self.val.sqrt();
            if let Some(i) = result.to_isize() {
                Val::from_isize(vm, i)
            } else {
                ArbInt::new(vm, result)
            }
        }
    }

    fn sub(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Some(rhs) = other.as_isize(vm) {
            ArbInt::new(vm, &self.val - rhs)
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            ArbInt::new(vm, &self.val - &rhs.val)
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            match self.val.to_f64() {
                Some(i) => Ok(Double::new(vm, i - rhs.double())),
                None => Err(VMError::new(vm, VMErrorKind::CantRepresentAsDouble)),
            }
        } else {
            Err(VMError::new(
                vm,
                VMErrorKind::NotANumber {
                    got: other.dyn_objtype(vm),
                },
            ))
        }
    }

    fn xor(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Some(rhs) = other.as_isize(vm) {
            ArbInt::new(vm, &self.val ^ BigInt::from_isize(rhs).unwrap())
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            ArbInt::new(vm, &self.val ^ &rhs.val)
        } else {
            Err(VMError::new(
                vm,
                VMErrorKind::TypeError {
                    expected: self.dyn_objtype(),
                    got: other.dyn_objtype(vm),
                },
            ))
        }
    }

    fn ref_equals(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        let b = if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            self.val == rhs.val
        } else {
            false
        };
        Ok(Val::from_bool(vm, b))
    }

    fn equals(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        let b = if other.dyn_objtype(vm) == ObjType::Int {
            debug_assert!(self.val != BigInt::from_isize(other.as_isize(vm).unwrap()).unwrap());
            false
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            self.val == rhs.val
        } else {
            false
        };
        Ok(Val::from_bool(vm, b))
    }

    fn not_equals(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        let b = if other.dyn_objtype(vm) == ObjType::Int {
            debug_assert!(self.val != BigInt::from_isize(other.as_isize(vm).unwrap()).unwrap());
            true
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            self.val != rhs.val
        } else {
            true
        };
        Ok(Val::from_bool(vm, b))
    }

    fn greater_than(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        let b = if other.dyn_objtype(vm) == ObjType::Int {
            debug_assert!(self.val > BigInt::from_isize(other.as_isize(vm).unwrap()).unwrap());
            true
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            self.val > rhs.val
        } else {
            return Err(VMError::new(
                vm,
                VMErrorKind::NotANumber {
                    got: other.dyn_objtype(vm),
                },
            ));
        };
        Ok(Val::from_bool(vm, b))
    }

    fn greater_than_equals(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        let b = if other.dyn_objtype(vm) == ObjType::Int {
            debug_assert!(self.val >= BigInt::from_isize(other.as_isize(vm).unwrap()).unwrap());
            true
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            self.val >= rhs.val
        } else {
            return Err(VMError::new(
                vm,
                VMErrorKind::NotANumber {
                    got: other.dyn_objtype(vm),
                },
            ));
        };
        Ok(Val::from_bool(vm, b))
    }

    fn less_than(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        let b = if other.dyn_objtype(vm) == ObjType::Int {
            debug_assert!(self.val < BigInt::from_isize(other.as_isize(vm).unwrap()).unwrap());
            false
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            self.val < rhs.val
        } else {
            return Err(VMError::new(
                vm,
                VMErrorKind::NotANumber {
                    got: other.dyn_objtype(vm),
                },
            ));
        };
        Ok(Val::from_bool(vm, b))
    }

    fn less_than_equals(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        let b = if other.dyn_objtype(vm) == ObjType::Int {
            debug_assert!(self.val <= BigInt::from_isize(other.as_isize(vm).unwrap()).unwrap());
            false
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            self.val <= rhs.val
        } else {
            return Err(VMError::new(
                vm,
                VMErrorKind::NotANumber {
                    got: other.dyn_objtype(vm),
                },
            ));
        };
        Ok(Val::from_bool(vm, b))
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
    pub fn new(vm: &VM, val: BigInt) -> Result<Val, Box<VMError>> {
        if let Some(i) = val.to_isize() {
            Val::from_isize(vm, i)
        } else {
            Ok(Val::from_obj(vm, ArbInt { val }))
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

    fn to_strval(&self, vm: &VM) -> Result<Val, Box<VMError>> {
        Ok(String_::new(vm, self.val.to_string(), true))
    }

    fn add(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Some(rhs) = other.as_isize(vm) {
            match self.val.checked_add(rhs) {
                Some(i) => Val::from_isize(vm, i),
                None => ArbInt::new(vm, BigInt::from_isize(self.val).unwrap() + rhs),
            }
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            ArbInt::new(vm, self.val + &rhs.val)
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            match self.val.to_f64() {
                Some(i) => Ok(Double::new(vm, i + rhs.double())),
                None => Err(VMError::new(vm, VMErrorKind::CantRepresentAsDouble)),
            }
        } else {
            Err(VMError::new(
                vm,
                VMErrorKind::NotANumber {
                    got: other.dyn_objtype(vm),
                },
            ))
        }
    }

    fn div(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Some(rhs) = other.as_isize(vm) {
            if rhs == 0 {
                Err(VMError::new(vm, VMErrorKind::DivisionByZero))
            } else {
                Val::from_isize(vm, self.val / rhs)
            }
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            match BigInt::from_isize(self.val).unwrap().checked_div(&rhs.val) {
                Some(i) => ArbInt::new(vm, i),
                None => Err(VMError::new(vm, VMErrorKind::DivisionByZero)),
            }
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            if rhs.double() == 0f64 {
                Err(VMError::new(vm, VMErrorKind::DivisionByZero))
            } else {
                // Note that converting an f64 to an isize in Rust can lead to undefined behaviour
                // https://github.com/rust-lang/rust/issues/10184 -- it's not obvious that we can
                // do anything about this other than wait for it to be fixed in LLVM and Rust.
                match self.val.to_f64() {
                    Some(i) => Val::from_isize(vm, (i / rhs.double()) as isize),
                    None => Err(VMError::new(vm, VMErrorKind::CantRepresentAsDouble)),
                }
            }
        } else {
            Err(VMError::new(
                vm,
                VMErrorKind::NotANumber {
                    got: other.dyn_objtype(vm),
                },
            ))
        }
    }

    fn mul(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Some(rhs) = other.as_isize(vm) {
            match self.val.checked_mul(rhs) {
                Some(i) => Val::from_isize(vm, i),
                None => ArbInt::new(vm, BigInt::from_isize(self.val).unwrap() * rhs),
            }
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            ArbInt::new(vm, self.val * &rhs.val)
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            match self.val.to_f64() {
                Some(i) => Ok(Double::new(vm, i * rhs.double())),
                None => Err(VMError::new(vm, VMErrorKind::CantRepresentAsDouble)),
            }
        } else {
            Err(VMError::new(
                vm,
                VMErrorKind::NotANumber {
                    got: other.dyn_objtype(vm),
                },
            ))
        }
    }

    fn sub(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Some(rhs) = other.as_isize(vm) {
            match self.val.checked_sub(rhs) {
                Some(i) => Val::from_isize(vm, i),
                None => ArbInt::new(vm, BigInt::from_isize(self.val).unwrap() - rhs),
            }
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            ArbInt::new(vm, self.val - &rhs.val)
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            match self.val.to_f64() {
                Some(i) => Ok(Double::new(vm, i - rhs.double())),
                None => Err(VMError::new(vm, VMErrorKind::CantRepresentAsDouble)),
            }
        } else {
            Err(VMError::new(
                vm,
                VMErrorKind::NotANumber {
                    got: other.dyn_objtype(vm),
                },
            ))
        }
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
    pub fn boxed_isize(vm: &VM, i: isize) -> Result<Val, Box<VMError>> {
        Ok(Val::from_obj(vm, Int { val: i }))
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
