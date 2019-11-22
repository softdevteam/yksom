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
    Double(f64),
    InstVarLookup(usize),
    InstVarSet(usize),
    Int(isize),
    Pop,
    Return,
    Send(usize, usize),
    String(usize),
    VarLookup(usize, usize),
    VarSet(usize, usize),
}

#[derive(Clone, Copy, Debug)]
pub enum Builtin {
    False,
    Integer,
    Nil,
    System,
    True,
}

#[derive(Clone, Copy, Debug)]
pub enum Primitive {
    Add,
    And,
    AsString,
    BitXor,
    Class,
    Concatenate,
    Div,
    DoubleDiv,
    Equals,
    GreaterThan,
    GreaterThanEquals,
    Halt,
    Hashcode,
    Inspect,
    InstVarAt,
    InstVarAtPut,
    InstVarNamed,
    LessThan,
    LessThanEquals,
    Mod,
    Mul,
    Name,
    NotEquals,
    New,
    ObjectSize,
    Perform,
    PerformInSuperClass,
    PerformWithArguments,
    PerformWithArgumentsInSuperClass,
    PrintNewline,
    PrintString,
    RefEquals,
    Restart,
    Shl,
    Sqrt,
    Sub,
    /// Is this `value` (0), `value:` (1), or `value:with:` (2)?
    Value(u8),
}
