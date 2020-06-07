#![allow(clippy::new_ret_no_self)]

use std::{cell::Cell, collections::hash_map::DefaultHasher, hash::Hasher};

use crate::{
    compiler::instrs::Primitive,
    vm::{
        core::VM,
        objects::{Obj, ObjType, StaticObjType, String_},
        val::{NotUnboxable, Val},
    },
};

#[derive(Debug)]
pub struct Method {
    sig: Cell<Val>,
    pub body: MethodBody,
    holder: Cell<Val>,
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
        max_stack: usize,
    },
}

impl Obj for Method {
    fn dyn_objtype(&self) -> ObjType {
        ObjType::Method
    }

    fn get_class(&self, vm: &mut VM) -> Val {
        vm.method_cls
    }

    fn hashcode(&self) -> u64 {
        let mut hasher = DefaultHasher::new();
        hasher.write_usize(self as *const _ as usize);
        hasher.finish()
    }
}

impl NotUnboxable for Method {}

impl StaticObjType for Method {
    fn static_objtype() -> ObjType {
        ObjType::Method
    }
}

impl Method {
    pub fn new(vm: &VM, sig: Val, body: MethodBody) -> Method {
        Method {
            sig: Cell::new(sig),
            body,
            holder: Cell::new(vm.nil),
        }
    }

    pub fn holder(&self) -> Val {
        self.holder.get()
    }

    pub fn set_holder(&self, _: &VM, class: Val) {
        self.holder.set(class);
    }

    pub fn bootstrap(&self, vm: &VM) {
        self.sig
            .get()
            .downcast::<String_>(vm)
            .unwrap()
            .set_cls(vm.sym_cls);
    }

    pub fn sig(&self, _: &VM) -> Val {
        self.sig.get()
    }
}
