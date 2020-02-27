#![allow(clippy::new_ret_no_self)]

use abgc_derive::GcLayout;

use crate::{
    compiler::instrs::Primitive,
    vm::{
        core::VM,
        objects::{Obj, ObjType, StaticObjType},
        val::{NotUnboxable, Val},
    },
};

#[derive(Debug, GcLayout)]
pub struct Method {
    pub name: String,
    pub body: MethodBody,
}

#[derive(Debug, Clone, Copy)]
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

impl Clone for Method {
    fn clone(&self) -> Self {
        Method { name: self.name.clone(), body: self.body }
    }
}
