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
    Block(usize),
    Builtin(Builtin),
    ClosureReturn(usize),
    Const(usize),
    Double(f64),
    InstVarLookup(usize),
    InstVarSet(usize),
    Pop,
    Return,
    Send(usize),
    VarLookup(usize, usize),
    VarSet(usize, usize),
}

#[derive(Clone, Copy, Debug)]
pub enum Builtin {
    False,
    Nil,
    System,
    True,
}

#[derive(Clone, Copy, Debug)]
pub enum Primitive {
    Add,
    AsString,
    Class,
    Concatenate,
    Div,
    Equals,
    GreaterThan,
    GreaterThanEquals,
    LessThan,
    LessThanEquals,
    Mul,
    Name,
    NotEquals,
    New,
    PrintNewline,
    PrintString,
    Restart,
    Shl,
    Sub,
    /// Is this `value` (0), `value:` (1), or `value:with:` (2)?
    Value(u8),
}
