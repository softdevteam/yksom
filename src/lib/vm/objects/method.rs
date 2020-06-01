#![allow(clippy::new_ret_no_self)]

use std::cell::Cell;

use crate::{
    compiler::instrs::Primitive,
    vm::{
        core::VM,
        objects::{Obj, ObjType, StaticObjType},
        val::{NotUnboxable, Val},
    },
};

#[derive(Debug)]
pub struct Method {
    sig: Val,
    pub body: MethodBody,
    class: Cell<Val>,
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
            sig,
            body,
            class: Cell::new(vm.nil),
        }
    }

    pub fn class(&self) -> Val {
        self.class.get()
    }

    pub fn set_class(&self, _: &VM, class: Val) {
        self.class.set(class);
    }

    pub fn sig(&self, _: &VM) -> Val {
        self.sig
    }
}
