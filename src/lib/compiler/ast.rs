// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

use lrpar::Lexeme;

type StorageT = u32;

#[derive(Debug)]
pub struct Class {
    pub name: Lexeme<StorageT>,
    pub supername: Option<Lexeme<StorageT>>,
    pub methods: Vec<Method>,
}

#[derive(Debug)]
pub struct Method {
    pub name: MethodName,
    pub temps: Vec<Lexeme<StorageT>>,
    pub body: MethodBody,
}

#[derive(Debug)]
pub enum MethodName {
    Id(Lexeme<StorageT>),
    Keywords(Vec<(Lexeme<StorageT>, Lexeme<StorageT>)>),
}

#[derive(Debug)]
pub enum MethodBody {
    Primitive,
    Body { exprs: Vec<Expr> },
}

#[derive(Debug)]
pub enum Expr {
    KeywordMsg {
        receiver: Box<Expr>,
        msglist: Vec<(Lexeme<StorageT>, Expr)>,
    },
    UnaryMsg {
        receiver: Box<Expr>,
        ids: Vec<Lexeme<StorageT>>,
    },
    Return,
    String(Lexeme<StorageT>),
    VarLookup(Lexeme<StorageT>),
}
