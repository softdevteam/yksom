// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

#![allow(clippy::new_ret_no_self)]

use std::{
    alloc::Layout,
    any::Any,
    collections::HashMap,
    fmt::Debug,
    mem::{forget, size_of, transmute},
    ops::{CoerceUnsized, Deref},
    path::PathBuf,
    ptr,
};

use enum_primitive_derive::Primitive;

use super::{
    gc::{Gc, GcBox, GcLayout},
    vm::{VMError, VM},
};
use crate::compiler::{
    cobjects,
    instrs::{Instr, Primitive},
};

// We use a fairly standard pointer tagging model where the low `TAG_BITSIZE` bits of a machine
// word (represented as a Rust `usize`) are used to store the type of the value (with the
// possibilities enumerated in `ValKind` below).

#[cfg(target_pointer_width = "64")]
const BITSIZE: usize = 64;
#[cfg(target_pointer_width = "64")]
const TAG_BITSIZE: usize = 3; // Number of bits
#[cfg(target_pointer_width = "64")]
const TAG_BITMASK: usize = (1 << 3) - 1;

#[cfg(target_pointer_width = "64")]
#[derive(Debug, PartialEq, Primitive)]
enum ValKind {
    // All of the values here must fit inside TAG_BITSIZE bits and be safely convert to usize
    // using "as".
    GCBOX = 0b000,
    INT = 0b001,
}

/// The core struct representing values in the language runtime: boxed and unboxed values are
/// hidden behind this, such that they can be treated in exactly the same way. The contents of this
/// struct are deliberately opaque, and may change, but it is guaranteed that this struct will
/// always be `Copy`able.
#[derive(Debug)]
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
        debug_assert_eq!(ValKind::GCBOX as usize, 0);
        debug_assert_eq!(size_of::<*const GcBox<ThinObj>>(), size_of::<usize>());
        let ptr = ThinObj::new(obj).into_raw();
        Val {
            val: unsafe { transmute(ptr) },
        }
    }

    /// Create a value upon which all operations are invalid. This can be used as a sentinel or
    /// while initialising part of the system.
    pub fn illegal() -> Val {
        Val { val: 0 }
    }

    fn valkind(&self) -> ValKind {
        match self.val & TAG_BITMASK {
            x if x == ValKind::GCBOX as usize => ValKind::GCBOX,
            x if x == ValKind::INT as usize => ValKind::INT,
            _ => unreachable!(),
        }
    }

    /// Return this `Val`'s box. If the `Val` refers to an unboxed value, this will box it.
    pub fn gc_obj(&self, vm: &VM) -> Gc<ThinObj> {
        match self.valkind() {
            ValKind::GCBOX => {
                debug_assert_eq!(ValKind::GCBOX as usize, 0);
                debug_assert_eq!(size_of::<*const GcBox<ThinObj>>(), size_of::<usize>());
                debug_assert_ne!(self.val, 0);
                unsafe { Gc::clone_from_raw(self.val as *const _) }
            }
            ValKind::INT => Int::boxed_isize(vm, self.as_isize(vm).unwrap()).gc_obj(vm),
        }
    }

    /// If possible, return this `Val` as an `isize` or `Err(())` otherwise.
    pub fn as_isize(&self, vm: &VM) -> Result<isize, ()> {
        match self.valkind() {
            ValKind::GCBOX => self.gc_obj(vm).as_isize(),
            ValKind::INT => {
                if self.val & 1 << (BITSIZE - 1) == 0 {
                    Ok((self.val >> TAG_BITSIZE) as isize)
                } else {
                    // For negative integers we need to pad the top TAG_BITSIZE bits with 1s.
                    Ok(
                        ((self.val >> TAG_BITSIZE) | (TAG_BITMASK << (BITSIZE - TAG_BITSIZE)))
                            as isize,
                    )
                }
            }
        }
    }

    /// If possible, return this `Val` as an `usize` or `Err(())` otherwise.
    pub fn as_usize(&self, vm: &VM) -> Result<usize, ()> {
        match self.valkind() {
            ValKind::GCBOX => self.gc_obj(vm).as_usize(),
            ValKind::INT => {
                if self.val & 1 << (BITSIZE - 1) == 0 {
                    Ok(self.val >> TAG_BITSIZE)
                } else {
                    Err(())
                }
            }
        }
    }
}

impl Clone for Val {
    fn clone(&self) -> Self {
        let val = match self.valkind() {
            ValKind::GCBOX => {
                if self.val != 0 {
                    unsafe {
                        transmute(Gc::<ThinObj>::clone_from_raw(self.val as *const _).into_raw())
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

pub trait Obj: Debug + GcLayout {
    /// Return this object as an `Any` that can then be safely turned into a specific struct.
    fn as_any(&self) -> &Any;
    /// If possible, return this `Obj` as an `isize` or `Err(())` otherwise.
    fn as_isize(&self) -> Result<isize, ()>;
    /// If possible, return this `Obj` as an `usize` or `Err(())` otherwise.
    fn as_usize(&self) -> Result<usize, ()>;
    /// What class is this object an instance of?
    fn get_class(&self, vm: &VM) -> Val;
}

macro_rules! gclayout {
    ($(#[$attr:meta])* $n: ident) => {
        impl GcLayout for $n {
            fn layout(&self) -> std::alloc::Layout {
                std::alloc::Layout::new::<$n>()
            }
        }
    };
}

gclayout!(Class);
gclayout!(Method);
gclayout!(Inst);
gclayout!(Int);
gclayout!(String_);

/// A GCable object that stores the vtable pointer alongside the object, meaning that a thin
/// pointer can be used to store to the ThinCell itself.
#[repr(C)]
pub struct ThinObj {
    vtable: usize,
}

impl ThinObj {
    pub fn new<U>(v: U) -> Gc<ThinObj>
    where
        *const U: CoerceUnsized<*const Obj>,
        U: Obj,
    {
        let (layout, uoff) = Layout::new::<ThinObj>().extend(Layout::new::<U>()).unwrap();
        debug_assert_eq!(uoff, size_of::<ThinObj>());
        let (gcbptr, objptr) = GcBox::<ThinObj>::alloc_blank(layout);
        let t: &Obj = &v;
        unsafe {
            (*objptr).vtable = transmute::<_, (usize, usize)>(t).1;
            let buf_v = (objptr as *mut u8).add(uoff);
            if size_of::<U>() != 0 {
                buf_v.copy_from_nonoverlapping(&v as *const U as *const u8, size_of::<U>());
            }
        }
        forget(v);
        unsafe { Gc::from_raw(gcbptr) }
    }
}

impl GcLayout for ThinObj {
    fn layout(&self) -> Layout {
        Layout::new::<ThinObj>()
            .extend(self.deref().layout())
            .unwrap()
            .0
    }
}

impl Deref for ThinObj {
    type Target = Obj;

    fn deref(&self) -> &(dyn Obj + 'static) {
        unsafe {
            let self_ptr = self as *const Self;
            let obj_ptr = self_ptr.add(1);
            transmute((obj_ptr, self.vtable))
        }
    }
}

impl Drop for ThinObj {
    fn drop(&mut self) {
        let self_ptr = self as *const Self;
        unsafe {
            let obj_ptr = self_ptr.add(1);
            ptr::drop_in_place::<Obj>(transmute((obj_ptr, self.vtable)));
        }
    }
}

#[derive(Debug)]
pub struct Class {
    pub path: PathBuf,
    pub methods: HashMap<String, Method>,
    pub instrs: Vec<Instr>,
    pub consts: Vec<Val>,
    pub sends: Vec<(String, usize)>,
}

impl Obj for Class {
    fn as_any(&self) -> &Any {
        self
    }

    fn as_isize(&self) -> Result<isize, ()> {
        Err(())
    }

    fn as_usize(&self) -> Result<usize, ()> {
        Err(())
    }

    fn get_class(&self, vm: &VM) -> Val {
        vm.cls_cls.clone()
    }
}

impl Class {
    pub fn from_ccls(vm: &VM, ccls: cobjects::Class) -> Self {
        let mut methods = HashMap::with_capacity(ccls.methods.len());
        for cmeth in ccls.methods.into_iter() {
            let body = match cmeth.body {
                cobjects::MethodBody::Primitive(p) => MethodBody::Primitive(p),
                cobjects::MethodBody::User(idx) => MethodBody::User(idx),
            };
            let meth = Method {
                name: cmeth.name.clone(),
                body,
            };
            methods.insert(cmeth.name, meth);
        }
        let consts = ccls
            .consts
            .into_iter()
            .map(|c| match c {
                cobjects::Const::String(s) => String_::new(vm, s),
            })
            .collect();
        Class {
            path: ccls.path,
            methods,
            instrs: ccls.instrs,
            consts,
            sends: ccls.sends,
        }
    }

    pub fn get_method(&self, _: &VM, msg: &str) -> Result<&Method, VMError> {
        self.methods
            .get(msg)
            .ok_or_else(|| VMError::UnknownMethod(msg.to_owned()))
    }
}

#[derive(Debug)]
pub struct Method {
    pub name: String,
    pub body: MethodBody,
}

#[derive(Debug)]
pub enum MethodBody {
    /// A built-in primitive.
    Primitive(Primitive),
    /// User bytecode: the `usize` gives the starting offset of this method's bytecode in the
    /// parent class.
    User(usize),
}

impl Obj for Method {
    fn as_any(&self) -> &Any {
        self
    }

    fn as_isize(&self) -> Result<isize, ()> {
        Err(())
    }

    fn as_usize(&self) -> Result<usize, ()> {
        Err(())
    }

    fn get_class(&self, _: &VM) -> Val {
        unimplemented!();
    }
}

/// An instance of a user class.
#[derive(Debug)]
pub struct Inst {
    class: Val,
}

impl Obj for Inst {
    fn as_any(&self) -> &Any {
        self
    }

    fn as_isize(&self) -> Result<isize, ()> {
        unimplemented!()
    }

    fn as_usize(&self) -> Result<usize, ()> {
        unimplemented!()
    }

    fn get_class(&self, _: &VM) -> Val {
        self.class.clone()
    }
}

impl Inst {
    pub fn new(vm: &VM, class: Val) -> Val {
        Val::from_obj(vm, Inst { class })
    }
}

#[derive(Debug)]
pub struct Int {
    val: isize,
}

impl Obj for Int {
    fn as_any(&self) -> &Any {
        self
    }

    fn as_isize(&self) -> Result<isize, ()> {
        Ok(self.val)
    }

    fn as_usize(&self) -> Result<usize, ()> {
        if self.val > 0 {
            Ok(self.val as usize)
        } else {
            Err(())
        }
    }

    fn get_class(&self, _: &VM) -> Val {
        unimplemented!();
    }
}

impl Int {
    /// Create a `Val` representing the `isize` integer `i`.
    pub fn from_isize(vm: &VM, i: isize) -> Val {
        let top_bits = i as usize & (TAG_BITMASK << (BITSIZE - TAG_BITSIZE));
        if top_bits == 0 || top_bits == TAG_BITMASK << (BITSIZE - TAG_BITSIZE) {
            // top_bits == 0: A positive integer that fits in our tagging scheme
            // top_bits all set to 1: A negative integer that fits in our tagging scheme
            Val {
                val: ((i as usize) << TAG_BITSIZE) | (ValKind::INT as usize),
            }
        } else {
            Val::from_obj(vm, Int { val: i })
        }
    }

    /// Create a `Val` representing the `usize` integer `i`. The `Val` is guaranteed to be boxed
    /// internally.
    pub fn boxed_isize(vm: &VM, i: isize) -> Val {
        Val::from_obj(vm, Int { val: i })
    }

    /// Create a `Val` representing the `usize` integer `i`. If `i` is too big to be stored (in
    /// practice, meaning that it can't be stored in an `isize`), `Err(())` is returned.
    pub fn from_usize(vm: &VM, i: usize) -> Result<Val, ()> {
        if i & (TAG_BITMASK << (BITSIZE - TAG_BITSIZE)) == 0 {
            // The top TAG_BITSIZE bits aren't set, so this fits within our pointer tagging scheme.
            Ok(Val {
                val: (i << TAG_BITSIZE) | (ValKind::INT as usize),
            })
        } else if i & (1 << (BITSIZE - 1)) == 0 {
            // One of the top TAG_BITSIZE bits is set, but not the topmost bit itself, so we can
            // box this as an isize.
            Ok(Int::from_isize(vm, i as isize))
        } else {
            // Too big for a boxed isize.
            Err(())
        }
    }
}

#[derive(Debug)]
pub struct String_ {
    s: String,
}

impl Obj for String_ {
    fn as_any(&self) -> &Any {
        self
    }

    fn as_isize(&self) -> Result<isize, ()> {
        Err(())
    }

    fn as_usize(&self) -> Result<usize, ()> {
        Err(())
    }

    fn get_class(&self, vm: &VM) -> Val {
        vm.str_cls.clone()
    }
}

impl String_ {
    pub fn new(vm: &VM, s: String) -> Val {
        Val::from_obj(vm, String_ { s })
    }

    pub fn as_str(&self) -> &str {
        &self.s
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_isize() {
        let vm = VM::new_no_bootstrap();

        let v = Int::from_isize(&vm, 0);
        assert_eq!(v.valkind(), ValKind::INT);
        assert_eq!(v.as_usize(&vm).unwrap(), 0);
        assert_eq!(v.as_isize(&vm).unwrap(), 0);

        let v = Int::from_isize(&vm, -1);
        assert_eq!(v.valkind(), ValKind::INT);
        assert!(v.as_usize(&vm).is_err());
        assert_eq!(v.as_isize(&vm).unwrap(), -1);

        let v = Int::from_isize(&vm, isize::min_value());
        assert_eq!(v.valkind(), ValKind::GCBOX);
        assert_eq!(v.as_isize(&vm).unwrap(), isize::min_value());
        let v = Int::from_isize(&vm, isize::max_value());
        assert_eq!(v.valkind(), ValKind::GCBOX);
        assert_eq!(v.as_isize(&vm).unwrap(), isize::max_value());

        let v = Int::from_isize(&vm, 1 << (BITSIZE - 1 - TAG_BITSIZE) - 1);
        assert_eq!(v.valkind(), ValKind::INT);
        assert_eq!(v.as_usize(&vm), Ok(1 << (BITSIZE - 1 - TAG_BITSIZE) - 1));
        assert_eq!(v.as_isize(&vm), Ok(1 << (BITSIZE - 1 - TAG_BITSIZE) - 1));

        let v = Int::from_isize(&vm, 1 << (BITSIZE - 2));
        assert_eq!(v.valkind(), ValKind::GCBOX);
        assert_eq!(v.as_usize(&vm), Ok(1 << (BITSIZE - 2)));
        assert_eq!(v.as_isize(&vm), Ok(1 << (BITSIZE - 2)));
    }

    #[test]
    fn test_usize() {
        let vm = VM::new_no_bootstrap();

        let v = Int::from_usize(&vm, 0).unwrap();
        assert_eq!(v.valkind(), ValKind::INT);
        assert_eq!(v.as_usize(&vm).unwrap(), 0);
        assert_eq!(v.as_isize(&vm).unwrap(), 0);

        let v = Int::from_usize(&vm, 1 << (BITSIZE - 1 - TAG_BITSIZE) - 1).unwrap();
        assert_eq!(v.valkind(), ValKind::INT);
        assert_eq!(v.as_usize(&vm), Ok(1 << (BITSIZE - 1 - TAG_BITSIZE) - 1));
        assert_eq!(v.as_isize(&vm), Ok(1 << (BITSIZE - 1 - TAG_BITSIZE) - 1));

        assert!(Int::from_usize(&vm, 1 << (BITSIZE - 1)).is_err());

        let v = Int::from_usize(&vm, 1 << (BITSIZE - 2)).unwrap();
        assert_eq!(v.valkind(), ValKind::GCBOX);
        assert_eq!(v.as_usize(&vm), Ok(1 << (BITSIZE - 2)));
        assert_eq!(v.as_isize(&vm), Ok(1 << (BITSIZE - 2)));
    }

    #[test]
    fn test_boxed_int() {
        let vm = VM::new_no_bootstrap();

        assert_eq!(Int::from_isize(&vm, 12345).valkind(), ValKind::INT);
        assert_eq!(Int::boxed_isize(&vm, 12345).valkind(), ValKind::GCBOX);

        let v = Int::from_isize(&vm, 12345);
        assert_eq!(v.gc_obj(&vm).as_usize(), v.as_usize(&vm));
    }
}
