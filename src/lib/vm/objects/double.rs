// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

#![allow(clippy::new_ret_no_self)]

use abgc_derive::GcLayout;
use num_traits::ToPrimitive;

use crate::vm::{
    core::{VMError, VM},
    objects::{ArbInt, Obj, ObjType, StaticObjType, String_},
    val::{NotUnboxable, Val},
};

#[derive(Debug, GcLayout)]
/// A boxed Double (which is synonymous with a f64 in yksom).
pub struct Double {
    val: f64,
}

impl NotUnboxable for Double {}

impl Obj for Double {
    fn dyn_objtype(&self) -> ObjType {
        ObjType::Double
    }

    fn get_class(&self, vm: &VM) -> Val {
        vm.double_cls.clone()
    }

    fn to_strval(&self, vm: &VM) -> Result<Val, Box<VMError>> {
        let mut buf = ryu::Buffer::new();
        Ok(String_::new(vm, buf.format(self.val).to_owned()))
    }

    fn add(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Some(rhs) = other.as_isize(vm) {
            Ok(Double::new(vm, self.val + (rhs as f64)))
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            Ok(Double::new(vm, self.val + rhs.val))
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            match rhs.bigint().to_f64() {
                Some(i) => Ok(Double::new(vm, self.val + i)),
                None => Err(Box::new(VMError::CantRepresentAsDouble)),
            }
        } else {
            Err(Box::new(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            }))
        }
    }

    fn sub(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Some(rhs) = other.as_isize(vm) {
            Ok(Double::new(vm, self.val - (rhs as f64)))
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            Ok(Double::new(vm, self.val - rhs.val))
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            match rhs.bigint().to_f64() {
                Some(i) => Ok(Double::new(vm, self.val - i)),
                None => Err(Box::new(VMError::CantRepresentAsDouble)),
            }
        } else {
            Err(Box::new(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            }))
        }
    }

    fn mul(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Some(rhs) = other.as_isize(vm) {
            Ok(Double::new(vm, self.val * (rhs as f64)))
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            Ok(Double::new(vm, self.val * rhs.val))
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            match rhs.bigint().to_f64() {
                Some(i) => Ok(Double::new(vm, self.val * i)),
                None => Err(Box::new(VMError::CantRepresentAsDouble)),
            }
        } else {
            Err(Box::new(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            }))
        }
    }

    fn ref_equals(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        let b = if let Some(rhs) = other.try_downcast::<Double>(vm) {
            self.val == rhs.double()
        } else {
            false
        };
        Ok(Val::from_bool(vm, b))
    }

    fn equals(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        let b = if let Some(rhs) = other.as_isize(vm) {
            self.val == (rhs as f64)
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            self.val == rhs.double()
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            match rhs.bigint().to_f64() {
                Some(i) => self.val == i,
                None => false,
            }
        } else {
            false
        };

        Ok(Val::from_bool(vm, b))
    }

    fn less_than(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        let b = if let Some(rhs) = other.as_isize(vm) {
            self.val < (rhs as f64)
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            self.val < rhs.double()
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            match rhs.bigint().to_f64() {
                Some(i) => self.val < i,
                None => false,
            }
        } else {
            return Err(Box::new(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            }));
        };

        Ok(Val::from_bool(vm, b))
    }
}

impl StaticObjType for Double {
    fn static_objtype() -> ObjType {
        ObjType::Double
    }
}

impl Double {
    pub fn new(vm: &VM, val: f64) -> Val {
        Val::from_obj(vm, Double { val })
    }

    pub fn double(&self) -> f64 {
        self.val
    }
}
