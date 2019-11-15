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

pub use crate::vm::objects::{BlockInfo, Method, MethodBody};

pub struct Class {
    pub name: String,
    pub path: PathBuf,
    pub supercls: Option<String>,
    pub num_inst_vars: usize,
    pub methods: Vec<Method>,
    pub blocks: Vec<BlockInfo>,
    pub instrs: Vec<Instr>,
    pub sends: Vec<(String, usize)>,
    pub strings: Vec<String>,
}
