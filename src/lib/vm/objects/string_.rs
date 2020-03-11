#![allow(clippy::new_ret_no_self)]

use std::str;

use crate::vm::{
    core::VM,
    error::VMError,
    objects::{Obj, ObjType, StaticObjType},
    val::{NotUnboxable, Val},
};

#[derive(Debug)]
pub struct String_ {
    s: String,
    pub is_str: bool,
}

impl Obj for String_ {
    fn dyn_objtype(&self) -> ObjType {
        ObjType::String_
    }

    fn get_class(&self, vm: &mut VM) -> Val {
        // FIXME This is a temporary hack until we sort out bootstrapping of the String_ class
        if self.is_str {
            vm.str_cls.clone()
        } else {
            vm.sym_cls.clone()
        }
    }

    fn to_strval(&self, vm: &mut VM) -> Result<Val, Box<VMError>> {
        Ok(String_::new(vm, self.s.to_string(), true))
    }

    fn ref_equals(&self, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        let other_str: &String_ = other.downcast(vm)?;

        Ok(Val::from_bool(
            vm,
            (self.is_str == other_str.is_str) && (self.s == other_str.s),
        ))
    }
}

impl NotUnboxable for String_ {}

impl StaticObjType for String_ {
    fn static_objtype() -> ObjType {
        ObjType::String_
    }
}

impl String_ {
    pub fn new(vm: &mut VM, s: String, is_str: bool) -> Val {
        Val::from_obj(vm, String_ { s, is_str })
    }

    pub fn as_str(&self) -> &str {
        &self.s
    }

    /// Concatenate this string with another string and return the result.
    pub fn concatenate(&self, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        let other_str: &String_ = other.downcast(vm)?;

        // Since strings are immutable, concatenating an empty string means we don't need to
        // make a new string.
        if self.s.is_empty() {
            return Ok(other);
        } else if other_str.s.is_empty() {
            return Ok(Val::recover(self));
        }

        let mut new = String::with_capacity(self.s.len() + other_str.s.len());
        new.push_str(&self.s);
        new.push_str(&other_str.s);
        Ok(String_::new(vm, new, true))
    }

    pub fn to_symbol(&self, vm: &mut VM) -> Result<Val, Box<VMError>> {
        Ok(String_::new(vm, self.s.to_string(), false))
    }
}
