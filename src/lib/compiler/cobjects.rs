// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

use std::path::PathBuf;

use crate::compiler::instrs::Instr;

pub use crate::vm::objects::{Method, MethodBody};

pub struct Class {
    pub name: String,
    pub path: PathBuf,
    pub supercls: Option<String>,
    pub num_inst_vars: usize,
    pub methods: Vec<Method>,
    pub blocks: Vec<Block>,
    pub instrs: Vec<Instr>,
    pub sends: Vec<(String, usize)>,
    pub strings: Vec<String>,
}

pub struct Block {
    pub bytecode_off: usize,
    pub bytecode_end: usize,
    pub num_params: usize,
    pub num_vars: usize,
    pub max_stack: usize,
}
