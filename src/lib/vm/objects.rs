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

use std::{cell::UnsafeCell, collections::HashMap, fmt::Debug, path::PathBuf};

use abgc::{self, Gc};
use abgc_derive::GcLayout;
use natrob::narrowable_abgc;

use crate::{
    compiler::{
        cobjects,
        instrs::{Instr, Primitive},
    },
    vm::{
        val::Val,
        vm::{Closure, VMError, VM},
    },
};

/// The SOM type of objects.
///
/// It might seem that we should use `TypeId` for this, but that requires types to have a 'static
/// lifetime, which is an annoying restriction.
#[derive(Debug, PartialEq)]
pub enum ObjType {
    Block,
    Class,
    Method,
    Inst,
    Int,
    String_,
}

/// The main SOM Object trait.
#[narrowable_abgc(ThinObj)]
pub trait Obj: Debug + abgc::GcLayout {
    /// Return the `ObjType` of this object.
    fn dyn_objtype(&self) -> ObjType;
    /// If possible, return this `Obj` as an `isize`.
    fn as_isize(&self) -> Result<isize, VMError>;
    /// If possible, return this `Obj` as an `usize`.
    fn as_usize(&self) -> Result<usize, VMError>;
    /// What class is this object an instance of?
    fn get_class(&self, vm: &VM) -> Val;
}

/// SOM objects which `impl` this trait guarantee that they can only ever be stored boxed.
/// Implementing this trait on SOM objects which can be stored unboxed leads to undefined
/// behaviour.
pub trait NotUnboxable: Obj {}

pub trait StaticObjType {
    /// Return this trait type's static `ObjType`
    fn static_objtype() -> ObjType;
}

#[derive(Debug, GcLayout)]
pub struct Block {
    pub blockinfo_cls: Val,
    pub blockinfo_off: usize,
    pub parent_closure: Gc<Closure>,
}

impl Obj for Block {
    fn dyn_objtype(&self) -> ObjType {
        ObjType::Block
    }

    fn as_isize(&self) -> Result<isize, VMError> {
        Err(VMError::CantRepresentAsUsize)
    }

    fn as_usize(&self) -> Result<usize, VMError> {
        Err(VMError::CantRepresentAsUsize)
    }

    fn get_class(&self, vm: &VM) -> Val {
        vm.block_cls.clone()
    }
}

impl NotUnboxable for Block {}

impl StaticObjType for Block {
    fn static_objtype() -> ObjType {
        ObjType::Block
    }
}

impl Block {
    pub fn new(
        vm: &VM,
        blockinfo_cls: Val,
        blockinfo_off: usize,
        parent_closure: Gc<Closure>,
    ) -> Val {
        Val::from_obj(
            vm,
            Block {
                blockinfo_cls,
                blockinfo_off,
                parent_closure,
            },
        )
    }
}

#[derive(Debug, GcLayout)]
pub struct Class {
    pub name: Val,
    pub path: PathBuf,
    pub supercls: Option<Val>,
    pub num_inst_vars: usize,
    pub methods: HashMap<String, Method>,
    pub blockinfos: Vec<BlockInfo>,
    pub instrs: Vec<Instr>,
    pub consts: Vec<Val>,
    pub sends: Vec<(String, usize)>,
}

/// Minimal information about a SOM block.
#[derive(Debug)]
pub struct BlockInfo {
    pub bytecode_off: usize,
    pub bytecode_end: usize,
    pub num_vars: usize,
}

impl Obj for Class {
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

impl NotUnboxable for Class {}

impl StaticObjType for Class {
    fn static_objtype() -> ObjType {
        ObjType::Class
    }
}

impl Class {
    pub fn from_ccls(vm: &VM, ccls: cobjects::Class) -> Result<Val, VMError> {
        let supercls = match ccls.supercls {
            Some(ref x) => match x.as_str() {
                "Boolean" => Some(vm.bool_cls.clone()),
                "nil" => None,
                _ => unimplemented!(),
            },
            None => Some(vm.obj_cls.clone()),
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

        let blockinfos = ccls
            .blocks
            .into_iter()
            .map(|b| BlockInfo {
                bytecode_off: b.bytecode_off,
                bytecode_end: b.bytecode_end,
                num_vars: b.num_vars,
            })
            .collect();

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
                blockinfos,
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
            .unwrap_or_else(|| match &self.supercls {
                Some(scls) => scls.downcast::<Class>(vm)?.get_method(vm, msg),
                None => Err(VMError::UnknownMethod(msg.to_owned())),
            })
    }

    pub fn blockinfo(&self, blockinfo_off: usize) -> &BlockInfo {
        &self.blockinfos[blockinfo_off]
    }
}

#[derive(Debug, GcLayout)]
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

impl NotUnboxable for Method {}

impl StaticObjType for Method {
    fn static_objtype() -> ObjType {
        ObjType::Method
    }
}

/// An instance of a user class.
#[derive(Debug, GcLayout)]
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

impl NotUnboxable for Inst {}

impl StaticObjType for Inst {
    fn static_objtype() -> ObjType {
        ObjType::Inst
    }
}

impl Inst {
    pub fn new(vm: &VM, class: Val) -> Val {
        let cls: &Class = class.downcast(vm).unwrap();
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

#[derive(Debug, GcLayout)]
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
    /// Create a `Val` representing the `usize` integer `i`. The `Val` is guaranteed to be boxed
    /// internally.
    pub fn boxed_isize(vm: &VM, i: isize) -> Result<Val, VMError> {
        Ok(Val::from_obj(vm, Int { val: i }))
    }
}

#[derive(Debug, GcLayout)]
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
    pub fn concatenate(&self, vm: &VM, other: Val) -> Result<Val, VMError> {
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
        Ok(String_::new(vm, new))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm::val::ValKind;

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
            v.tobj(&vm).unwrap().as_usize().unwrap(),
            v.as_usize(&vm).unwrap()
        );
    }
}
