// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

#[derive(Clone, Copy, Debug)]
pub enum Instr {
    Const(usize),
    Primitive(Primitive),
    Return,
    Send(usize),
    VarLookup(usize),
    VarSet(usize),
}

#[derive(Clone, Copy, Debug)]
pub enum Primitive {
    Class,
    Concatenate,
    Name,
    New,
    PrintLn,
}

/// The index of the "self" variable.
pub const SELF_VAR: usize = 0;
