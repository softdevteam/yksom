#![allow(clippy::new_ret_no_self)]

use std::{cell::Cell, str};

use crate::vm::{
    core::VM,
    error::{VMError, VMErrorKind},
    objects::{Obj, ObjType, StaticObjType},
    val::{NotUnboxable, Val},
};

#[derive(Debug)]
pub struct String_ {
    cls: Cell<Val>,
    s: String,
}

impl Obj for String_ {
    fn dyn_objtype(&self) -> ObjType {
        ObjType::String_
    }

    fn get_class(&self, _: &mut VM) -> Val {
        debug_assert!(
            self.cls.get().valkind() != crate::vm::val::ValKind::ILLEGAL,
            "{}",
            self.s
        );
        self.cls.get()
    }

    fn to_strval(&self, vm: &mut VM) -> Result<Val, Box<VMError>> {
        Ok(Val::from_obj(
            vm,
            String_ {
                cls: self.cls.clone(),
                s: self.s.clone(),
            },
        ))
    }

    fn ref_equals(&self, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        let other_str: &String_ = other.downcast(vm)?;

        Ok(Val::from_bool(
            vm,
            (self.cls == other_str.cls) && (self.s == other_str.s),
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
    pub fn new_str(vm: &mut VM, s: String) -> Val {
        Val::from_obj(
            vm,
            String_ {
                cls: Cell::new(vm.str_cls),
                s,
            },
        )
    }

    pub fn new_sym(vm: &mut VM, s: String) -> Val {
        Val::from_obj(
            vm,
            String_ {
                cls: Cell::new(vm.sym_cls),
                s,
            },
        )
    }

    /// If the value `v` represents a `String_` which is an instance of the SOM `Symbol` class (and
    /// not the SOM `String` class!), return a reference to the underlying `String_` or an
    /// `InstanceTypeError` otherwise.
    pub fn symbol_to_string_<'a>(vm: &mut VM, v: &'a Val) -> Result<&'a String_, Box<VMError>> {
        if v.get_class(vm) == vm.sym_cls {
            Ok(v.downcast(vm)?)
        } else {
            let got_cls = v.get_class(vm);
            Err(VMError::new(
                vm,
                VMErrorKind::InstanceTypeError {
                    expected_cls: vm.sym_cls,
                    got_cls,
                },
            ))
        }
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
        Ok(String_::new_str(vm, new))
    }

    pub fn to_string_(&self, vm: &mut VM) -> Result<Val, Box<VMError>> {
        Ok(String_::new_str(vm, self.s.to_string()))
    }

    pub fn to_symbol(&self, vm: &mut VM) -> Result<Val, Box<VMError>> {
        Ok(String_::new_sym(vm, self.s.to_string()))
    }

    pub fn set_cls(&self, cls: Val) {
        self.cls.set(cls);
    }
}
