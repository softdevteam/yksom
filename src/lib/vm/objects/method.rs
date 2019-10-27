// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

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
