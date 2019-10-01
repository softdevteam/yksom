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
    objects::{ArbInt, Obj, ObjType, StaticObjType, String_},
    val::{NotUnboxable, Val, ValResult},
    vm::{VMError, VM},
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

    fn to_strval(&self, vm: &VM) -> ValResult {
        let mut buf = ryu::Buffer::new();
        ValResult::from_val(String_::new(vm, buf.format(self.val).to_owned()))
    }

    fn add(&self, vm: &VM, other: Val) -> ValResult {
        if let Some(rhs) = other.as_isize(vm) {
            ValResult::from_val(Double::new(vm, self.val + (rhs as f64)))
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            ValResult::from_val(Double::new(vm, self.val + rhs.val))
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            match rhs.bigint().to_f64() {
                Some(i) => ValResult::from_val(Double::new(vm, self.val + i)),
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
            ValResult::from_val(Double::new(vm, self.val - (rhs as f64)))
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            ValResult::from_val(Double::new(vm, self.val - rhs.val))
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            match rhs.bigint().to_f64() {
                Some(i) => ValResult::from_val(Double::new(vm, self.val - i)),
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
            ValResult::from_val(Double::new(vm, self.val * (rhs as f64)))
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            ValResult::from_val(Double::new(vm, self.val * rhs.val))
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            match rhs.bigint().to_f64() {
                Some(i) => ValResult::from_val(Double::new(vm, self.val * i)),
                None => ValResult::from_vmerror(VMError::CantRepresentAsDouble),
            }
        } else {
            ValResult::from_vmerror(VMError::NotANumber {
                got: other.dyn_objtype(vm),
            })
        }
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
