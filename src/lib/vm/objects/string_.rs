// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

#![allow(clippy::new_ret_no_self)]

use std::str;

use abgc_derive::GcLayout;

use crate::vm::{
    core::VM,
    objects::{Obj, ObjType, StaticObjType},
    val::{NotUnboxable, Val, ValResult},
};

#[derive(Debug, GcLayout)]
pub struct String_ {
    s: String,
}

impl Obj for String_ {
    fn dyn_objtype(&self) -> ObjType {
        ObjType::String_
    }

    fn get_class(&self, vm: &VM) -> Val {
        vm.str_cls.clone()
    }
}

impl NotUnboxable for String_ {}

impl StaticObjType for String_ {
    fn static_objtype() -> ObjType {
        ObjType::String_
    }
}

impl String_ {
    pub fn new(vm: &VM, s: String) -> Val {
        Val::from_obj(vm, String_ { s })
    }

    pub fn as_str(&self) -> &str {
        &self.s
    }

    /// Concatenate this string with another string and return the result.
    pub fn concatenate(&self, vm: &VM, other: Val) -> ValResult {
        let other_str: &String_ = rtry!(other.downcast(vm));

        // Since strings are immutable, concatenating an empty string means we don't need to
        // make a new string.
        if self.s.is_empty() {
            return ValResult::from_val(other);
        } else if other_str.s.is_empty() {
            return ValResult::from_val(Val::recover(self));
        }

        let mut new = String::with_capacity(self.s.len() + other_str.s.len());
        new.push_str(&self.s);
        new.push_str(&other_str.s);
        ValResult::from_val(String_::new(vm, new))
    }
}
