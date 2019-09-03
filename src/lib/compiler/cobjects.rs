// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

use std::path::PathBuf;

use crate::compiler::instrs::{Instr, Primitive};

#[derive(Eq, Hash, PartialEq)]
pub enum Const {
    Int(isize),
    String(String),
}

pub struct Class {
    pub name: String,
    pub path: PathBuf,
    pub supercls: Option<String>,
    pub num_inst_vars: usize,
    pub methods: Vec<Method>,
    pub blocks: Vec<Block>,
    pub instrs: Vec<Instr>,
    pub consts: Vec<Const>,
    pub sends: Vec<(String, usize)>,
}

pub struct Method {
    pub name: String,
    pub body: MethodBody,
}

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

pub struct Block {
    pub bytecode_off: usize,
    pub bytecode_end: usize,
    pub num_vars: usize,
}
