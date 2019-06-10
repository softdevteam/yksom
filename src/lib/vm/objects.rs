// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

#![allow(clippy::new_ret_no_self)]

//! This file contains the core SOM objects. Note that there is a fundamental constraint that
//! *must* be obeyed by the programmer at all times: upon their creation, instances of the `Obj`
//! trait must immediately be passed to `Val::from_obj`. In other words this is safe:
//!
//! ```rust,ignore
//! let x = Val::from_obj(vm, String_{ s: "a".to_owned() });
//! dbg!(x.tobj().as_str());
//! ```
//!
//! but this leads to undefined behaviour:
//!
//! ```rust,ignore
//! let x = String_{ s: "a".to_owned() };
//! dbg!(x.tobj().as_str());
//! ```
//!
//! The reason for this is that methods on `Obj`s can call `Val::restore` which converts an `Obj`
//! reference back into a `Val`.
//!
//! Although this constraint is not enforced through the type system, it is not hard to obey: as
//! soon as you create an `Obj` instance, pass it to `Val::from_obj`.

use std::{
    alloc::Layout,
    cell::UnsafeCell,
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
/// hidden behind this, such that they can be treated in exactly the same way.
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
    pub fn from_obj<T: Obj>(_: &VM, obj: T) -> Self {
        debug_assert_eq!(ValKind::GCBOX as usize, 0);
        debug_assert_eq!(size_of::<*const GcBox<ThinObj>>(), size_of::<usize>());
        let ptr = ThinObj::new(obj).into_raw();
        Val {
            val: unsafe { transmute::<*const GcBox<ThinObj>, usize>(ptr) },
        }
    }

    /// Convert `obj` into a `Val`. `Obj` must previously have been created via `Obj::from_off` and
    /// then turned into an actual object with `tobj`: failure to follow these steps results in
    /// undefined behaviour.
    pub fn recover(obj: &dyn Obj) -> Self {
        unsafe {
            let ptr = ThinObj::recover(obj).into_raw();
            Val {
                val: transmute::<*const GcBox<ThinObj>, usize>(ptr),
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

    fn valkind(&self) -> ValKind {
        match self.val & TAG_BITMASK {
            x if x == ValKind::GCBOX as usize => ValKind::GCBOX,
            x if x == ValKind::INT as usize => ValKind::INT,
            _ => unreachable!(),
        }
    }

    /// If this `Val` is a `GCBOX`, and that `GCBOX` is of type `T`, cast the `Val` to `&T`. If
    /// this `Val` is not a `GCBOX` or the `GCBOX` is not of type `T`, `VMError` will be returned.
    /// Note that, in general, you should use `Val::tobj()` as that can box values as needed
    /// whereas `gcbox_cast` cannot.
    pub fn gcbox_cast<T: Obj + StaticObjType>(&self, _: &VM) -> Result<&T, VMError> {
        match self.valkind() {
            ValKind::GCBOX => {
                debug_assert_eq!(ValKind::GCBOX as usize, 0);
                debug_assert_eq!(size_of::<*const GcBox<ThinObj>>(), size_of::<usize>());
                debug_assert_ne!(self.val, 0);
                let tobj = unsafe { &*transmute::<usize, *const GcBox<ThinObj>>(self.val) };
                tobj.deref().cast()
            }
            ValKind::INT => Err(VMError::GcBoxTypeError {
                expected: T::static_objtype(),
                got: Int::static_objtype(),
            }),
        }
    }

    /// Return this `Val`'s box. If the `Val` refers to an unboxed value, this will box it.
    pub fn tobj(&self, vm: &VM) -> Result<Gc<ThinObj>, VMError> {
        match self.valkind() {
            ValKind::GCBOX => {
                debug_assert_eq!(ValKind::GCBOX as usize, 0);
                debug_assert_eq!(size_of::<*const GcBox<ThinObj>>(), size_of::<usize>());
                debug_assert_ne!(self.val, 0);
                Ok(unsafe { Gc::clone_from_raw(self.val as *const _) })
            }
            ValKind::INT => Int::boxed_isize(vm, self.as_isize(vm).unwrap())?.tobj(vm),
        }
    }

    /// If possible, return this `Val` as an `isize`.
    pub fn as_isize(&self, vm: &VM) -> Result<isize, VMError> {
        match self.valkind() {
            ValKind::GCBOX => Ok(self.tobj(vm)?.as_isize()?),
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

    /// If possible, return this `Val` as an `usize`.
    pub fn as_usize(&self, vm: &VM) -> Result<usize, VMError> {
        match self.valkind() {
            ValKind::GCBOX => Ok(self.tobj(vm)?.as_usize()?),
            ValKind::INT => {
                if self.val & 1 << (BITSIZE - 1) == 0 {
                    Ok(self.val >> TAG_BITSIZE)
                } else {
                    Err(VMError::CantRepresentAsUsize)
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
                        transmute::<*const GcBox<ThinObj>, usize>(
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

/// The SOM type of objects.
///
/// It might seem that we should use `TypeId` for this, but that requires types to have a 'static
/// lifetime, which is an annoying restriction.
#[derive(Debug, PartialEq)]
pub enum ObjType {
    Class,
    Method,
    Inst,
    Int,
    String_,
}

/// The main SOM Object trait.
pub trait Obj: Debug + GcLayout {
    /// Return the `ObjType` of this object.
    fn dyn_objtype(&self) -> ObjType;
    /// If possible, return this `Obj` as an `isize`.
    fn as_isize(&self) -> Result<isize, VMError>;
    /// If possible, return this `Obj` as an `usize`.
    fn as_usize(&self) -> Result<usize, VMError>;
    /// What class is this object an instance of?
    fn get_class(&self, vm: &VM) -> Val;
}

pub trait StaticObjType {
    /// Return this trait type's static `ObjType`
    fn static_objtype() -> ObjType;
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

macro_rules! gclayout_lifetime {
    ($(#[$attr:meta])* $n: ident) => {
        impl<'a> GcLayout for $n<'a> {
            fn layout(&self) -> std::alloc::Layout {
                std::alloc::Layout::new::<$n>()
            }
        }
    };
}

gclayout_lifetime!(Class);
gclayout!(Method);
gclayout!(Inst);
gclayout!(Int);
gclayout!(String_);

/// A GCable object that stores the vtable pointer alongside the object, meaning that a thin
/// pointer can be used to store to the ThinCell itself.
#[repr(C)]
pub struct ThinObj {
    vtable: usize,
    // The ThinObj `vtable` is followed by the actual contents of the object itself. In other
    // words, on a 64 bit machine the layout is:
    //   0..7: vtable
    //   8..: object
}

impl ThinObj {
    pub fn new<'a, U>(v: U) -> Gc<ThinObj>
    where
        *const U: CoerceUnsized<*const (dyn Obj + 'a)>,
        U: Obj + 'a,
    {
        let (layout, uoff) = Layout::new::<ThinObj>().extend(Layout::new::<U>()).unwrap();
        debug_assert_eq!(uoff, size_of::<ThinObj>());
        let (gcbptr, objptr) = GcBox::<ThinObj>::alloc_blank(layout);
        let t: &dyn Obj = &v;
        unsafe {
            (*objptr).vtable = transmute::<*const dyn Obj, (usize, usize)>(t).1;
            let buf_v = (objptr as *mut u8).add(uoff);
            if size_of::<U>() != 0 {
                buf_v.copy_from_nonoverlapping(&v as *const U as *const u8, size_of::<U>());
            }
        }
        forget(v);
        unsafe { Gc::from_raw(gcbptr) }
    }

    /// Turn an `Obj` pointer into a `Gc<ThinObj>`.
    pub unsafe fn recover(o: &dyn Obj) -> Gc<ThinObj> {
        let thinptr = (o as *const _ as *const u8).sub(size_of::<ThinObj>()) as *const ThinObj;
        Gc::recover(thinptr)
    }

    /// Cast this `ThinObj` to a concrete `Obj` instance.
    pub fn cast<T: Obj + StaticObjType>(&self) -> Result<&T, VMError> {
        // This is a cunning hack based on the fact that vtable pointers are a proxy for a type
        // identifier. In other words, if two distinct objects have the same vtable pointer, they
        // are instances of the same type; if their vtable pointers are different, they are
        // instances of different types. We can thus use vtable pointers as a proxy for type
        // equality.

        // We need to get `T`'s vtable. We cheat, creating a dummy pointer that forces the compiler
        // to create a trait object, from which we can then fish out the vtable pointer.
        let t_vtable = {
            let t: &dyn Obj = unsafe { &*(0 as *const T) };
            unsafe { transmute::<&dyn Obj, (usize, usize)>(t) }.1
        };

        if t_vtable == self.vtable {
            let self_ptr = self as *const Self as *const u8;
            let obj_ptr = unsafe { self_ptr.add(size_of::<ThinObj>()) };
            Ok(unsafe { &*(obj_ptr as *const T) })
        } else {
            Err(VMError::TypeError {
                expected: T::static_objtype(),
                got: self.deref().dyn_objtype(),
            })
        }
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
    type Target = dyn Obj;

    fn deref(&self) -> &(dyn Obj + 'static) {
        unsafe {
            let self_ptr = self as *const Self as *const u8;
            let obj_ptr = self_ptr.add(size_of::<ThinObj>());
            transmute::<(*const u8, usize), &dyn Obj>((obj_ptr, self.vtable))
        }
    }
}

impl Drop for ThinObj {
    fn drop(&mut self) {
        let self_ptr = self as *const Self as *const u8;
        unsafe {
            let obj_ptr = self_ptr.add(size_of::<ThinObj>());
            let fat_ptr =
                transmute::<(*mut u8, usize), *mut dyn Obj>((obj_ptr as *mut u8, self.vtable));
            ptr::drop_in_place(fat_ptr);
        }
    }
}

#[derive(Debug)]
pub struct Class<'a> {
    pub name: Val,
    pub path: PathBuf,
    pub supercls: Option<&'a Class<'a>>,
    pub num_inst_vars: usize,
    pub methods: HashMap<String, Method>,
    pub instrs: Vec<Instr>,
    pub consts: Vec<Val>,
    pub sends: Vec<(String, usize)>,
}

impl<'a> Obj for Class<'a> {
    fn dyn_objtype(&self) -> ObjType {
        ObjType::Class
    }

    fn as_isize(&self) -> Result<isize, VMError> {
        Err(VMError::CantRepresentAsUsize)
    }

    fn as_usize(&self) -> Result<usize, VMError> {
        Err(VMError::CantRepresentAsUsize)
    }

    fn get_class(&self, vm: &VM) -> Val {
        vm.cls_cls.clone()
    }
}

impl<'a> StaticObjType for Class<'a> {
    fn static_objtype() -> ObjType {
        ObjType::Class
    }
}

impl<'a> Class<'a> {
    pub fn from_ccls(vm: &VM, ccls: cobjects::Class) -> Result<Val, VMError> {
        let supercls = match ccls.supercls {
            Some(ref x) if x == "nil" => None,
            None => (Some(vm.obj_cls.gcbox_cast(vm)?)),
            _ => unimplemented!(),
        };

        let mut inst_vars = Vec::with_capacity(ccls.num_inst_vars);
        inst_vars.resize(ccls.num_inst_vars, Val::illegal());

        let mut methods = HashMap::with_capacity(ccls.methods.len());
        for cmeth in ccls.methods.into_iter() {
            let body = match cmeth.body {
                cobjects::MethodBody::Primitive(p) => MethodBody::Primitive(p),
                cobjects::MethodBody::User {
                    num_vars,
                    bytecode_off,
                } => MethodBody::User {
                    num_vars,
                    bytecode_off,
                },
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
        Ok(Val::from_obj(
            vm,
            Class {
                name: String_::new(vm, ccls.name),
                path: ccls.path,
                supercls,
                num_inst_vars: ccls.num_inst_vars,
                methods,
                instrs: ccls.instrs,
                consts,
                sends: ccls.sends,
            },
        ))
    }

    pub fn name(&self, _: &VM) -> Result<Val, VMError> {
        Ok(self.name.clone())
    }

    pub fn get_method(&self, vm: &VM, msg: &str) -> Result<(Val, &Method), VMError> {
        self.methods
            .get(msg)
            .map(|x| Ok((Val::recover(self), x)))
            .unwrap_or_else(|| match self.supercls {
                Some(scls) => scls.get_method(vm, msg),
                None => Err(VMError::UnknownMethod(msg.to_owned())),
            })
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
    /// User bytecode.
    User {
        /// How many variables does this method define?
        num_vars: usize,
        /// The offset of this method's bytecode in its parent class.
        bytecode_off: usize,
    },
}

impl Obj for Method {
    fn dyn_objtype(&self) -> ObjType {
        ObjType::Method
    }

    fn as_isize(&self) -> Result<isize, VMError> {
        Err(VMError::CantRepresentAsUsize)
    }

    fn as_usize(&self) -> Result<usize, VMError> {
        Err(VMError::CantRepresentAsUsize)
    }

    fn get_class(&self, _: &VM) -> Val {
        unimplemented!();
    }
}

impl StaticObjType for Method {
    fn static_objtype() -> ObjType {
        ObjType::Method
    }
}

/// An instance of a user class.
#[derive(Debug)]
pub struct Inst {
    class: Val,
    inst_vars: UnsafeCell<Vec<Val>>,
}

impl Obj for Inst {
    fn dyn_objtype(&self) -> ObjType {
        ObjType::Inst
    }

    fn as_isize(&self) -> Result<isize, VMError> {
        unimplemented!()
    }

    fn as_usize(&self) -> Result<usize, VMError> {
        unimplemented!()
    }

    fn get_class(&self, _: &VM) -> Val {
        self.class.clone()
    }
}

impl StaticObjType for Inst {
    fn static_objtype() -> ObjType {
        ObjType::Inst
    }
}

impl Inst {
    pub fn new(vm: &VM, class: Val) -> Val {
        let cls: &Class = class.gcbox_cast(vm).unwrap();
        let mut inst_vars = Vec::with_capacity(cls.num_inst_vars);
        inst_vars.resize(cls.num_inst_vars, Val::illegal());
        let inst = Inst {
            class,
            inst_vars: UnsafeCell::new(inst_vars),
        };
        Val::from_obj(vm, inst)
    }

    pub fn inst_var_lookup(&self, n: usize) -> Val {
        let inst_vars = unsafe { &mut *self.inst_vars.get() };
        inst_vars[n].clone()
    }

    pub fn inst_var_set(&self, n: usize, v: Val) {
        let inst_vars = unsafe { &mut *self.inst_vars.get() };
        inst_vars[n] = v;
    }
}

#[derive(Debug)]
pub struct Int {
    val: isize,
}

impl Obj for Int {
    fn dyn_objtype(&self) -> ObjType {
        ObjType::Int
    }

    fn as_isize(&self) -> Result<isize, VMError> {
        Ok(self.val)
    }

    fn as_usize(&self) -> Result<usize, VMError> {
        if self.val > 0 {
            Ok(self.val as usize)
        } else {
            Err(VMError::CantRepresentAsUsize)
        }
    }

    fn get_class(&self, _: &VM) -> Val {
        unimplemented!();
    }
}

impl StaticObjType for Int {
    fn static_objtype() -> ObjType {
        ObjType::Int
    }
}

impl Int {
    /// Create a `Val` representing the `isize` integer `i`.
    pub fn from_isize(vm: &VM, i: isize) -> Result<Val, VMError> {
        let top_bits = i as usize & (TAG_BITMASK << (BITSIZE - TAG_BITSIZE));
        if top_bits == 0 || top_bits == TAG_BITMASK << (BITSIZE - TAG_BITSIZE) {
            // top_bits == 0: A positive integer that fits in our tagging scheme
            // top_bits all set to 1: A negative integer that fits in our tagging scheme
            Ok(Val {
                val: ((i as usize) << TAG_BITSIZE) | (ValKind::INT as usize),
            })
        } else {
            Ok(Val::from_obj(vm, Int { val: i }))
        }
    }

    /// Create a `Val` representing the `usize` integer `i`. The `Val` is guaranteed to be boxed
    /// internally.
    pub fn boxed_isize(vm: &VM, i: isize) -> Result<Val, VMError> {
        Ok(Val::from_obj(vm, Int { val: i }))
    }

    /// Create a `Val` representing the `usize` integer `i`. Notice that this can fail if `i` is
    /// too big (since we don't have BigNum support and ints are internally represented as
    /// `isize`).
    pub fn from_usize(vm: &VM, i: usize) -> Result<Val, VMError> {
        if i & (TAG_BITMASK << (BITSIZE - TAG_BITSIZE)) == 0 {
            // The top TAG_BITSIZE bits aren't set, so this fits within our pointer tagging scheme.
            Ok(Val {
                val: (i << TAG_BITSIZE) | (ValKind::INT as usize),
            })
        } else if i & (1 << (BITSIZE - 1)) == 0 {
            // One of the top TAG_BITSIZE bits is set, but not the topmost bit itself, so we can
            // box this as an isize.
            Ok(Int::from_isize(vm, i as isize)?)
        } else {
            Err(VMError::CantRepresentAsIsize)
        }
    }
}

#[derive(Debug)]
pub struct String_ {
    s: String,
}

impl Obj for String_ {
    fn dyn_objtype(&self) -> ObjType {
        ObjType::String_
    }

    fn as_isize(&self) -> Result<isize, VMError> {
        Err(VMError::CantRepresentAsUsize)
    }

    fn as_usize(&self) -> Result<usize, VMError> {
        Err(VMError::CantRepresentAsUsize)
    }

    fn get_class(&self, vm: &VM) -> Val {
        vm.str_cls.clone()
    }
}

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
    pub fn concatenate(&self, vm: &VM, other: Val) -> Result<Val, VMError> {
        let other_tobj = other.tobj(vm)?;
        let other_str: &String_ = other_tobj.cast()?;

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
        Ok(String_::new(vm, new))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_isize() {
        let vm = VM::new_no_bootstrap();

        let v = Int::from_isize(&vm, 0).unwrap();
        assert_eq!(v.valkind(), ValKind::INT);
        assert_eq!(v.as_usize(&vm).unwrap(), 0);
        assert_eq!(v.as_isize(&vm).unwrap(), 0);

        let v = Int::from_isize(&vm, -1).unwrap();
        assert_eq!(v.valkind(), ValKind::INT);
        assert!(v.as_usize(&vm).is_err());
        assert_eq!(v.as_isize(&vm).unwrap(), -1);

        let v = Int::from_isize(&vm, isize::min_value()).unwrap();
        assert_eq!(v.valkind(), ValKind::GCBOX);
        assert_eq!(v.as_isize(&vm).unwrap(), isize::min_value());
        let v = Int::from_isize(&vm, isize::max_value()).unwrap();
        assert_eq!(v.valkind(), ValKind::GCBOX);
        assert_eq!(v.as_isize(&vm).unwrap(), isize::max_value());

        let v = Int::from_isize(&vm, 1 << (BITSIZE - 1 - TAG_BITSIZE) - 1).unwrap();
        assert_eq!(v.valkind(), ValKind::INT);
        assert_eq!(
            v.as_usize(&vm).unwrap(),
            1 << (BITSIZE - 1 - TAG_BITSIZE) - 1
        );
        assert_eq!(
            v.as_isize(&vm).unwrap(),
            1 << (BITSIZE - 1 - TAG_BITSIZE) - 1
        );

        let v = Int::from_isize(&vm, 1 << (BITSIZE - 2)).unwrap();
        assert_eq!(v.valkind(), ValKind::GCBOX);
        assert_eq!(v.as_usize(&vm).unwrap(), 1 << (BITSIZE - 2));
        assert_eq!(v.as_isize(&vm).unwrap(), 1 << (BITSIZE - 2));
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
        assert_eq!(
            v.as_usize(&vm).unwrap(),
            1 << (BITSIZE - 1 - TAG_BITSIZE) - 1
        );
        assert_eq!(
            v.as_isize(&vm).unwrap(),
            1 << (BITSIZE - 1 - TAG_BITSIZE) - 1
        );

        assert!(Int::from_usize(&vm, 1 << (BITSIZE - 1)).is_err());

        let v = Int::from_usize(&vm, 1 << (BITSIZE - 2)).unwrap();
        assert_eq!(v.valkind(), ValKind::GCBOX);
        assert_eq!(v.as_usize(&vm).unwrap(), 1 << (BITSIZE - 2));
        assert_eq!(v.as_isize(&vm).unwrap(), 1 << (BITSIZE - 2));
    }

    #[test]
    fn test_boxed_int() {
        let vm = VM::new_no_bootstrap();

        assert_eq!(Int::from_isize(&vm, 12345).unwrap().valkind(), ValKind::INT);
        assert_eq!(
            Int::boxed_isize(&vm, 12345).unwrap().valkind(),
            ValKind::GCBOX
        );

        let v = Int::from_isize(&vm, 12345).unwrap();
        assert_eq!(
            v.tobj(&vm).unwrap().as_usize().unwrap(),
            v.as_usize(&vm).unwrap()
        );
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
        assert_eq!(v.tobj(&vm).unwrap().cast::<String_>().unwrap().s, "s");
    }

    #[test]
    fn test_cast() {
        let vm = VM::new_no_bootstrap();
        let v = String_::new(&vm, "s".to_owned());
        assert!(v.tobj(&vm).unwrap().cast::<String_>().is_ok());
        assert_eq!(
            v.tobj(&vm).unwrap().cast::<Class>().unwrap_err(),
            VMError::TypeError {
                expected: ObjType::Class,
                got: ObjType::String_
            }
        );
    }

    #[test]
    fn test_gcbox_cast() {
        let vm = VM::new_no_bootstrap();
        let v = String_::new(&vm, "s".to_owned());
        assert!(v.gcbox_cast::<String_>(&vm).is_ok());
        let v = Int::from_usize(&vm, 0).unwrap();
        assert_eq!(
            v.gcbox_cast::<Int>(&vm).unwrap_err(),
            VMError::GcBoxTypeError {
                expected: ObjType::Int,
                got: ObjType::Int
            }
        );
    }
}
