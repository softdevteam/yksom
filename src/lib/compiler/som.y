%start ClassDef
%avoid_insert "DOUBLE" "INT" "STRING" "KEYWORD" "ID"
%%
ClassDef -> Result<Class, ()>:
      "ID" "=" SuperClass "(" NameDefs MethodsOpt ClassMethods ")"
      { Ok(Class{ name: map_err($1)?, supername: $3?, inst_vars: $5?, methods: $6? }) }
    ;
SuperClass -> Result<Option<Lexeme<StorageT>>, ()>:
      "ID" { Ok(Some(map_err($1)?)) }
    | { Ok(None) }
    ;
MethodsOpt -> Result<Vec<Method>, ()>:
      Methods { $1 }
    | { Ok(vec![]) }
    ;
Methods -> Result<Vec<Method>, ()>:
      Method { Ok(vec![$1?]) }
    | Methods Method { flattenr($1, $2) }
    ;
ClassMethods -> Result<(), ()>:
          "SEPARATOR" NameDefs MethodsOpt { unimplemented!() }
    | { Ok(()) }
    ;
Method -> Result<Method, ()>:
      MethodName "=" MethodBody
      { Ok(Method{ name: $1?, body: $3? }) }
    ;
NameDefs -> Result<Vec<Lexeme<StorageT>>, ()>:
      "|" IdListOpt "|" { Ok($2?) }
    | { Ok(vec![]) }
    ;
MethodName -> Result<MethodName, ()>:
      "ID" { Ok(MethodName::Id(map_err($1)?)) }
    | MethodNameKeywords { Ok(MethodName::Keywords($1?)) }
    | MethodNameBin { $1 }
    ;
MethodNameKeywords -> Result<Vec<(Lexeme<StorageT>, Lexeme<StorageT>)>, ()>:
      "KEYWORD" "ID" { Ok(vec![(map_err($1)?, map_err($2)?)]) }
    | MethodNameKeywords "KEYWORD" "ID" { flattenr($1, Ok((map_err($2)?, map_err($3)?))) }
    ;
MethodNameBin -> Result<MethodName, ()>:
      MethodNameBinOp Argument { Ok(MethodName::BinaryOp($1?, $2?)) };
// We'd like to just use BinOp here, rather than introducing MethodNameBinOp,
// but then the "|" symbol conflicts with NameDefs. In other words, you can't
// have "|" as a method name in SOM.
MethodNameBinOp -> Result<Lexeme<StorageT>, ()>:
      "BINOPSEQ" { Ok(map_err($1)?) }
    | "~" { Ok(map_err($1)?) }
    | "&" { Ok(map_err($1)?) }
    | "*" { Ok(map_err($1)?) }
    | "/" { Ok(map_err($1)?) }
    | "\\" { Ok(map_err($1)?) }
    | "+" { Ok(map_err($1)?) }
    | "-" { Ok(map_err($1)?) }
    | "=" { Ok(map_err($1)?) }
    | "<<" { Ok(map_err($1)?) }
    | ">" { Ok(map_err($1)?) }
    | "<" { Ok(map_err($1)?) }
    | "," { Ok(map_err($1)?) }
    | "@" { Ok(map_err($1)?) }
    | "%" { Ok(map_err($1)?) }
    ;
MethodBody -> Result<MethodBody, ()>:
      "PRIMITIVE" { Ok(MethodBody::Primitive) }
    | "(" NameDefs BlockExprs ")" { Ok(MethodBody::Body{ vars: $2?, exprs: $3? }) }
    ;
BlockExprs -> Result<Vec<Expr>, ()>:
      Exprs DotOpt "^" Expr DotOpt {
          let mut exprs = $1?;
          exprs.push(Expr::Return(Box::new($4?)));
          Ok(exprs)
      }
    | Exprs DotOpt { $1 }
    | "^" Expr DotOpt { Ok(vec![Expr::Return(Box::new($2?))]) }
    | { Ok(vec![]) }
    ;
DotOpt -> Result<(), ()>:
      "." { Ok(()) }
    | { Ok(()) }
    ;
Exprs -> Result<Vec<Expr>, ()>:
      Expr { Ok(vec![$1?]) }
    | Exprs "." Expr { flattenr($1, $3) }
    ;
Expr -> Result<Expr, ()>:
      Assign { $1 }
    | KeywordMsg { $1 }
    ;
Assign -> Result<Expr, ()>:
      "ID" ":=" Expr { Ok(Expr::Assign{id: map_err($1)?, expr: Box::new($3?)}) };
Unit -> Result<Expr, ()>:
      "ID" { Ok(Expr::VarLookup(map_err($1)?)) }
    | Literal { $1 }
    | Block { $1 }
    | "(" Expr ")" { $2 }
    ;
KeywordMsg -> Result<Expr, ()>:
      BinaryMsg KeywordMsgList { Ok(Expr::KeywordMsg{receiver: Box::new($1?), msglist: $2?}) }
    | BinaryMsg { $1 }
    ;
KeywordMsgList -> Result<Vec<(Lexeme<StorageT>, Expr)>, ()>:
      KeywordMsgList "KEYWORD" BinaryMsg { flattenr($1, Ok((map_err($2)?, $3?))) }
    | "KEYWORD" BinaryMsg { Ok(vec![(map_err($1)?, $2?)]) }
    ;
BinaryMsg -> Result<Expr, ()>:
      BinaryMsg BinOp UnaryMsg { Ok(Expr::BinaryMsg{ lhs: Box::new($1?), op: $2?, rhs: Box::new($3?) }) }
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
    | IdList "ID" { flattenr($1, map_err($2)) }
    ;
BinOp -> Result<Lexeme<StorageT>, ()>:
      "BINOPSEQ" { Ok(map_err($1)?) }
    | "~" { Ok(map_err($1)?) }
    | "&" { Ok(map_err($1)?) }
    | "|" { Ok(map_err($1)?) }
    | "*" { Ok(map_err($1)?) }
    | "/" { Ok(map_err($1)?) }
    | "\\" { Ok(map_err($1)?) }
    | "+" { Ok(map_err($1)?) }
    | "-" { Ok(map_err($1)?) }
    | "=" { Ok(map_err($1)?) }
    | "<<" { Ok(map_err($1)?) }
    | ">" { Ok(map_err($1)?) }
    | "<" { Ok(map_err($1)?) }
    | "," { Ok(map_err($1)?) }
    | "@" { Ok(map_err($1)?) }
    | "%" { Ok(map_err($1)?) }
    ;
Literal -> Result<Expr, ()>:
      "STRING" { Ok(Expr::String(map_err($1)?)) }
    | "INT" { Ok(Expr::Int{ is_negative: false, val: map_err($1)? }) }
    | "-" "INT" { Ok(Expr::Int{ is_negative: true, val: map_err($2)? }) }
    | "DOUBLE" { Ok(Expr::Double{ is_negative: false, val: map_err($1)? }) }
    | "-" "DOUBLE" { Ok(Expr::Double{ is_negative: true, val: map_err($2)? }) }
    | StringConst { $1 }
    | ArrayConst { unimplemented!() }
    ;
Block -> Result<Expr, ()>:
      "[" BlockParamsOpt NameDefs BlockExprs "]" { Ok(Expr::Block{ params: $2?, vars: $3?, exprs: $4? }) };
BlockParamsOpt -> Result<Vec<Lexeme<StorageT>>, ()>:
      BlockParams "|" { $1 }
    | { Ok(vec![]) }
    ;
BlockParams -> Result<Vec<Lexeme<StorageT>>, ()>:
      ":" "ID" { Ok(vec![map_err($2)?]) }
    | BlockParams ":" "ID" { flattenr($1, map_err($3)) }
    ;
Argument -> Result<Option<Lexeme<StorageT>>, ()>:
      "ID" { Ok(Some(map_err($1)?)) }
    | { unimplemented!() }
    ;
StringConst -> Result<Expr, ()>:
      "#" "STRING" { unimplemented!() }
    | "#" "ID" { Ok(Expr::Symbol(map_err($2)?)) }
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

/// Flatten `rhs` into `lhs`.
fn flattenr<T>(lhs: Result<Vec<T>, ()>, rhs: Result<T, ()>) -> Result<Vec<T>, ()> {
    let mut flt = lhs?;
    flt.push(rhs?);
    Ok(flt)
}

use crate::compiler::ast::*;
