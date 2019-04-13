// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

%start ClassDef
%avoid_insert "DOUBLE" "INT" "STRING" "KEYWORD" "PARAM" "ID"
%%
ClassDef -> Result<Class, ()>:
      "ID" "=" SuperClass "(" InstanceFields MethodsOpt ClassMethods ")"
      { Ok(Class{ name: map_err($1)?, supername: $3?, methods: $6? }) }
    ;
SuperClass -> Result<Option<Lexeme<StorageT>>, ()>:
      "ID" { Ok(Some(map_err($1)?)) }
    | { Ok(None) }
    ;
InstanceFields -> Result<(), ()>:
      "|" InstanceFieldNames "|" { unimplemented!() }
    | { Ok(()) }
    ;
InstanceFieldNames -> Result<(), ()>:
      "ID" { unimplemented!() }
    | InstanceFieldNames "ID" { unimplemented!() }
    ;
MethodsOpt -> Result<Vec<Method>, ()>:
      Methods { $1 }
    | { Ok(vec![]) }
    ;
Methods -> Result<Vec<Method>, ()>:
      Method { Ok(vec![$1?]) }
    | Methods Method { flatten($1, $2) }
    ;
ClassMethods -> Result<(), ()>:
          "SEPARATOR" InstanceFields MethodsOpt { unimplemented!() }
    | { Ok(()) }
    ;
Method -> Result<Method, ()>:
      MethodName "=" Temps MethodBody
      { Ok(Method{ name: $1?, temps: $3?, body: $4? }) }
    ;
Temps -> Result<Vec<Lexeme<StorageT>>, ()>:
      "|" IdListOpt "|" { Ok($2?) }
    | { Ok(vec![]) }
    ;
MethodName -> Result<MethodName, ()>:
      "ID" { Ok(MethodName::Id(map_err($1)?)) }
    | MethodNameKeywords { unimplemented!() }
    | MethodNameBin { unimplemented!() }
    ;
MethodNameKeywords -> Result<(), ()>:
      "KEYWORD" Argument { unimplemented!() }
    | MethodNameKeywords "KEYWORD" Argument { unimplemented!() }
    ;
MethodNameBin -> Result<(), ()>:
      MethodNameBinOp Argument { unimplemented!() };
// We'd like to just use BinOp here, rather than introducing MethodNameBinOp,
// but then the "|" symbol conflicts with InstanceFields. In other words, you
// can't have "|" as a method name in SOM.
MethodNameBinOp -> Result<(), ()>:
      "BINOPSEQ" { unimplemented!() }
    | "~" { unimplemented!() }
    | "&" { unimplemented!() }
    | "*" { unimplemented!() }
    | "/" { unimplemented!() }
    | "\\" { unimplemented!() }
    | "+" { unimplemented!() }
    | "-" { unimplemented!() }
    | "=" { unimplemented!() }
    | ">" { unimplemented!() }
    | "<" { unimplemented!() }
    | "," { unimplemented!() }
    | "@" { unimplemented!() }
    | "%" { unimplemented!() }
    ;
Argument -> Result<(), ()>:
      "ID" { unimplemented!() }
    | { unimplemented!() }
    ;
MethodBody -> Result<MethodBody, ()>:
      "PRIMITIVE" { Ok(MethodBody::Primitive) }
    | "(" InstanceFields BlockExprs ")" { Ok(MethodBody::Body{ exprs: $3? }) }
    ;
BlockExprs -> Result<Vec<Expr>, ()>:
      Exprs DotOpt "^" Expr DotOpt { unimplemented!() }
    | Exprs DotOpt { $1 }
    | "^" Expr DotOpt { unimplemented!() }
    | { unimplemented!() }
    ;
DotOpt -> Result<(), ()>:
      "." { unimplemented!() }
    | { Ok(()) }
    ;
Exprs -> Result<Vec<Expr>, ()>:
      Expr { Ok(vec![$1?]) }
    | Exprs "." Expr { flatten($1, $3) }
    ;
Expr -> Result<Expr, ()>:
      Assign { unimplemented!() }
    | KeywordMsg { $1 }
    ;
Assign -> Result<(), ()>:
      "ID" ":=" Expr { unimplemented!() };
Unit -> Result<Expr, ()>:
      "ID" { Ok(Expr::VarLookup(map_err($1)?)) }
    | Literal { $1 }
    | Block { unimplemented!() }
    | "(" Expr ")" { $2 }
    ;
KeywordMsg -> Result<Expr, ()>:
      BinaryMsg KeywordMsgList { Ok(Expr::KeywordMsg{receiver: Box::new($1?), msglist: $2?}) }
    | BinaryMsg { $1 }
    ;
KeywordMsgList -> Result<Vec<(Lexeme<StorageT>, Expr)>, ()>:
      KeywordMsgList "KEYWORD" BinaryMsg { flatten($1, Ok((map_err($2)?, $3?))) }
    | "KEYWORD" BinaryMsg { Ok(vec![(map_err($1)?, $2?)]) }
    ;
BinaryMsg -> Result<Expr, ()>:
      UnaryMsg BinOp BinaryMsg { unimplemented!() }
    | UnaryMsg { $1 }
    ;
UnaryMsg -> Result<Expr, ()>:
      Unit IdListOpt { Ok(Expr::UnaryMsg{ receiver: Box::new($1?), ids: $2? }) };
IdListOpt -> Result<Vec<Lexeme<StorageT>>, ()>:
      IdList { $1 }
    | { Ok(vec![]) }
    ;
IdList -> Result<Vec<Lexeme<StorageT>>, ()>:
      "ID" { Ok(vec![map_err($1)?]) }
    | IdList "ID" { flatten($1, map_err($2)) }
    ;
BinOp -> Result<(), ()>:
      "BINOPSEQ" { unimplemented!() }
    | "~" { unimplemented!() }
    | "&" { unimplemented!() }
    | "|" { unimplemented!() }
    | "*" { unimplemented!() }
    | "/" { unimplemented!() }
    | "\\" { unimplemented!() }
    | "+" { unimplemented!() }
    | "-" { unimplemented!() }
    | "=" { unimplemented!() }
    | ">" { unimplemented!() }
    | "<" { unimplemented!() }
    | "," { unimplemented!() }
    | "@" { unimplemented!() }
    | "%" { unimplemented!() }
    ;
Literal -> Result<Expr, ()>:
      "STRING" { Ok(Expr::String(map_err($1)?)) }
    | "INT" { unimplemented!() }
    | "-" "INT" { unimplemented!() }
    | "DOUBLE" { unimplemented!() }
    | "-" "DOUBLE" { unimplemented!() }
    | StringConst { unimplemented!() }
    | ArrayConst { unimplemented!() }
    ;
Block -> Result<(), ()>:
      "[" BlockParamsOpt Temps BlockExprs "]" { unimplemented!() };
BlockParamsOpt -> Result<(), ()>:
      BlockParams "|" { unimplemented!() }
    | { unimplemented!() }
    ;
BlockParams -> Result<(), ()>:
      "PARAM" Argument { unimplemented!() }
    | BlockParams "PARAM" Argument { unimplemented!() }
    ;
StringConst -> Result<(), ()>:
      "#" "STRING" { unimplemented!() }
    | "#" "ID" { unimplemented!() }
    | "#" "KEYWORD" { unimplemented!() }
    | "#" BinOp { unimplemented!() }
    ;
ArrayConst -> Result<(), ()>:
      "#" "(" ArrayList ")" { unimplemented!() };
ArrayList -> Result<(), ()>:
      Unit { unimplemented!() }
    | ArrayList Unit { unimplemented!() }
    ;

%%

type StorageT = u32;

fn map_err<StorageT>(r: Result<Lexeme<StorageT>, Lexeme<StorageT>>)
    -> Result<Lexeme<StorageT>, ()>
{
    r.map_err(|_| ())
}

fn flatten<T>(lhs: Result<Vec<T>, ()>, rhs: Result<T, ()>) -> Result<Vec<T>, ()> {
    let mut flt = lhs?;
    flt.push(rhs?);
    Ok(flt)
}

use crate::compiler::ast::*;
