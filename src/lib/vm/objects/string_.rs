#![allow(clippy::new_ret_no_self)]

use std::{
    cell::Cell,
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
    str,
};

#[cfg(feature = "rustgc")]
use std::gc::NoFinalize;

use libgc::Gc;
use smartstring::alias::String as SmartString;

use crate::vm::{
    core::VM,
    error::{VMError, VMErrorKind},
    objects::{Obj, ObjType, StaticObjType},
    val::{NotUnboxable, Val},
};

#[derive(Debug)]
pub struct String_ {
    cls: Cell<Val>,
    /// The number of Unicode characters in this string. This is initialised lazily: usize::MAX is
    /// the marker that means both `this string contains usize::MAX characters` and `we don't know
    /// how many characters this string has`. The former condition is rather unlikely, so we accept
    /// that if anyone ever manages to make a string of usize::MAX characters, we won't cache its
    /// length correctly, but will recalculate it each time.
    chars_len: Cell<usize>,
    s: SmartString,
}

#[cfg(feature = "rustgc")]
impl NoFinalize for String_ {}

impl Obj for String_ {
    fn dyn_objtype(self: Gc<Self>) -> ObjType {
        ObjType::String_
    }

    fn get_class(self: Gc<Self>, _: &mut VM) -> Val {
        debug_assert!(
            self.cls.get().valkind() != crate::vm::val::ValKind::ILLEGAL,
            "{}",
            self.s.as_str()
        );
        self.cls.get()
    }

    fn to_strval(self: Gc<Self>, _: &mut VM) -> Result<Val, Box<VMError>> {
        Ok(Val::from_obj(String_ {
            cls: self.cls.clone(),
            chars_len: self.chars_len.clone(),
            s: self.s.clone(),
        }))
    }

    fn hashcode(self: Gc<Self>) -> u64 {
        let mut s = DefaultHasher::new();
        self.s.hash(&mut s);
        s.finish()
    }

    fn length(self: Gc<Self>) -> usize {
        if self.chars_len.get() < usize::MAX {
            return self.chars_len.get();
        }
        let chars_len = self.s.chars().count();
        self.chars_len.set(chars_len);
        chars_len
    }

    fn ref_equals(self: Gc<Self>, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        self.equals(vm, other)
    }

    fn equals(self: Gc<Self>, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        let b = match other.downcast::<String_>(vm) {
            Ok(other_str) => (self.cls == other_str.cls) && (self.s == other_str.s),
            Err(_) => false,
        };
        Ok(Val::from_bool(vm, b))
    }
}

impl NotUnboxable for String_ {}

impl StaticObjType for String_ {
    fn static_objtype() -> ObjType {
        ObjType::String_
    }
}

impl String_ {
    pub fn new_str(vm: &mut VM, s: SmartString) -> Val {
        String_::new_str_chars_len(vm, s, usize::MAX)
    }

    /// Create a new `String_` whose number of Unicode characters is already known. Note that it is
    /// safe to pass `usize::MAX` for `chars_len`.
    fn new_str_chars_len(vm: &mut VM, s: SmartString, chars_len: usize) -> Val {
        Val::from_obj(String_ {
            cls: Cell::new(vm.str_cls),
            chars_len: Cell::new(chars_len),
            s,
        })
    }

    pub fn new_sym(vm: &mut VM, s: SmartString) -> Val {
        Val::from_obj(String_ {
            cls: Cell::new(vm.sym_cls),
            chars_len: Cell::new(usize::MAX),
            s,
        })
    }

    /// If the value `v` represents a `String_` which is an instance of the SOM `Symbol` class (and
    /// not the SOM `String` class!), return a reference to the underlying `String_` or an
    /// `InstanceTypeError` otherwise.
    pub fn symbol_to_string_(vm: &mut VM, v: Val) -> Result<Gc<String_>, Box<VMError>> {
        if v.get_class(vm) == vm.sym_cls {
            v.downcast(vm)
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
    pub fn concatenate(self: Gc<Self>, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        let other_str: Gc<String_> = other.downcast(vm)?;

        // Since strings are immutable, concatenating an empty string means we don't need to
        // make a new string.
        if self.s.is_empty() {
            return Ok(other);
        } else if other_str.s.is_empty() {
            return Ok(Val::recover(self));
        }

        let mut new = String::new();
        new.push_str(&self.s);
        new.push_str(&other_str.s);
        let chars_len = self
            .chars_len
            .get()
            .saturating_add(other_str.chars_len.get());
        Ok(String_::new_str_chars_len(vm, new.into(), chars_len))
    }

    pub fn substring(&self, vm: &mut VM, start: usize, end: usize) -> Result<Val, Box<VMError>> {
        if start == 0 || end == 0 {
            todo!();
        }
        if end < start {
            return Ok(String_::new_str(vm, SmartString::new()));
        }
        if start > self.s.len() || end > self.s.len() {
            todo!();
        }
        let substr = self
            .s
            .chars()
            .skip(start - 1)
            .take(end - start + 1)
            .collect::<String>()
            .into();
        Ok(String_::new_str_chars_len(vm, substr, end - start))
    }

    pub fn to_string_(&self, vm: &mut VM) -> Result<Val, Box<VMError>> {
        Ok(String_::new_str_chars_len(
            vm,
            self.s.clone(),
            self.chars_len.get(),
        ))
    }

    pub fn to_symbol(&self, vm: &mut VM) -> Result<Val, Box<VMError>> {
        Ok(String_::new_sym(vm, self.s.clone()))
    }

    pub fn set_cls(&self, cls: Val) {
        self.cls.set(cls);
    }
}
