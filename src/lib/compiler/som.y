%start ClassDef
%avoid_insert "DOUBLE" "INT" "STRING" "KEYWORD" "ID"
%%
ClassDef -> Result<Class, ()>:
      "ID" "=" SuperClass "(" NameDefs MethodsOpt ClassMethods ")"
      { let (class_inst_vars, class_methods) = $7?;
        Ok(Class{ name: map_err($1)?.span(),
                  supername: $3?,
                  inst_vars: $5?,
                  methods: $6?,
                  class_inst_vars,
                  class_methods
                })
      }
    ;
SuperClass -> Result<Option<Span>, ()>:
      "ID" { Ok(Some(map_err($1)?.span())) }
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
ClassMethods -> Result<(Vec<Span>, Vec<Method>), ()>:
      "SEPARATOR" NameDefs MethodsOpt {
        Ok(($2?, $3?))
      }
    | { Ok((vec![], vec![])) }
    ;
Method -> Result<Method, ()>:
      MethodName "=" MethodBody
      { Ok(Method{ span: $span, name: $1?, body: $3? }) }
    ;
NameDefs -> Result<Vec<Span>, ()>:
      "|" IdListOpt "|" { Ok($2?) }
    | { Ok(vec![]) }
    ;
MethodName -> Result<MethodName, ()>:
      "ID" { Ok(MethodName::Id(map_err($1)?.span())) }
    | MethodNameKeywords { Ok(MethodName::Keywords($1?)) }
    | MethodNameBin { $1 }
    ;
MethodNameKeywords -> Result<Vec<(Span, Span)>, ()>:
      "KEYWORD" "ID" { Ok(vec![(map_err($1)?.span(), map_err($2)?.span())]) }
    | MethodNameKeywords "KEYWORD" "ID" { flattenr($1, Ok((map_err($2)?.span(), map_err($3)?.span()))) }
    ;
MethodNameBin -> Result<MethodName, ()>:
      MethodNameBinOp Argument { Ok(MethodName::BinaryOp($1?, $2?)) };
// We'd like to just use BinOp here, rather than introducing MethodNameBinOp,
// but then the "|" symbol conflicts with NameDefs. In other words, you can't
// have "|" as a method name in SOM.
MethodNameBinOp -> Result<Span, ()>:
      "BINOPSEQ" { Ok(map_err($1)?.span()) }
    | "~" { Ok(map_err($1)?.span()) }
    | "&" { Ok(map_err($1)?.span()) }
    | "*" { Ok(map_err($1)?.span()) }
    | "/" { Ok(map_err($1)?.span()) }
    | "\\" { Ok(map_err($1)?.span()) }
    | "+" { Ok(map_err($1)?.span()) }
    | "-" { Ok(map_err($1)?.span()) }
    | "=" { Ok(map_err($1)?.span()) }
    | "<<" { Ok(map_err($1)?.span()) }
    | ">" { Ok(map_err($1)?.span()) }
    | "<" { Ok(map_err($1)?.span()) }
    | "," { Ok(map_err($1)?.span()) }
    | "@" { Ok(map_err($1)?.span()) }
    | "%" { Ok(map_err($1)?.span()) }
    ;
MethodBody -> Result<MethodBody, ()>:
      "PRIMITIVE" { Ok(MethodBody::Primitive) }
    | "(" NameDefs BlockExprs ")" { Ok(MethodBody::Body{ vars: $2?, exprs: $3? }) }
    ;
BlockExprs -> Result<Vec<Expr>, ()>:
      Exprs DotOpt "^" Expr DotOpt {
          let mut exprs = $1?;
          let expr = $4?;
          exprs.push(Expr::Return{span: span_merge($3, expr.span()), expr: Box::new(expr) });
          Ok(exprs)
      }
    | Exprs DotOpt { $1 }
    | "^" Expr DotOpt {
          let expr = $2?;
          Ok(vec![Expr::Return{span: span_merge($1, expr.span()), expr: Box::new(expr)}])
      }
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
      "ID" ":=" Expr { Ok(Expr::Assign{span: $span, id: map_err($1)?.span(), expr: Box::new($3?)}) };
Unit -> Result<Expr, ()>:
      "ID" { Ok(Expr::VarLookup(map_err($1)?.span())) }
    | Literal { $1 }
    | Block { $1 }
    | "(" Expr ")" { $2 }
    ;
KeywordMsg -> Result<Expr, ()>:
      BinaryMsg KeywordMsgList { Ok(Expr::KeywordMsg{ span: $span, receiver: Box::new($1?), msglist: $2? }) }
    | BinaryMsg { $1 }
    ;
KeywordMsgList -> Result<Vec<(Span, Expr)>, ()>:
      KeywordMsgList "KEYWORD" BinaryMsg { flattenr($1, Ok((map_err($2)?.span(), $3?))) }
    | "KEYWORD" BinaryMsg { Ok(vec![(map_err($1)?.span(), $2?)]) }
    ;
BinaryMsg -> Result<Expr, ()>:
      BinaryMsg BinOp UnaryMsg { Ok(Expr::BinaryMsg{ span: $span, lhs: Box::new($1?), op: $2?, rhs: Box::new($3?) }) }
    | UnaryMsg { $1 }
    ;
UnaryMsg -> Result<Expr, ()>:
      Unit IdListOpt { Ok(Expr::UnaryMsg{ span: $span, receiver: Box::new($1?), ids: $2? }) };
IdListOpt -> Result<Vec<Span>, ()>:
      IdList { $1 }
    | { Ok(vec![]) }
    ;
IdList -> Result<Vec<Span>, ()>:
      "ID" { Ok(vec![map_err($1)?.span()]) }
    | IdList "ID" { flattenr_span($1, $2) }
    ;
BinOp -> Result<Span, ()>:
      "BINOPSEQ" { Ok(map_err($1)?.span()) }
    | "~" { Ok(map_err($1)?.span()) }
    | "&" { Ok(map_err($1)?.span()) }
    | "|" { Ok(map_err($1)?.span()) }
    | "*" { Ok(map_err($1)?.span()) }
    | "/" { Ok(map_err($1)?.span()) }
    | "\\" { Ok(map_err($1)?.span()) }
    | "+" { Ok(map_err($1)?.span()) }
    | "-" { Ok(map_err($1)?.span()) }
    | "=" { Ok(map_err($1)?.span()) }
    | "<<" { Ok(map_err($1)?.span()) }
    | ">" { Ok(map_err($1)?.span()) }
    | "<" { Ok(map_err($1)?.span()) }
    | "," { Ok(map_err($1)?.span()) }
    | "@" { Ok(map_err($1)?.span()) }
    | "%" { Ok(map_err($1)?.span()) }
    ;
Literal -> Result<Expr, ()>:
      "STRING" { Ok(Expr::String(map_err($1)?.span())) }
    | "INT" { Ok(Expr::Int{ span: $span, is_negative: false, val: map_err($1)?.span() }) }
    | "-" "INT" { Ok(Expr::Int{ span: $span, is_negative: true, val: map_err($2)?.span() }) }
    | "DOUBLE" { Ok(Expr::Double{ span: $span, is_negative: false, val: map_err($1)?.span() }) }
    | "-" "DOUBLE" { Ok(Expr::Double{ span: $span, is_negative: true, val: map_err($2)?.span() }) }
    | StringConst { $1 }
    | ArrayConst { unimplemented!() }
    ;
Block -> Result<Expr, ()>:
      "[" BlockParamsOpt NameDefs BlockExprs "]" { Ok(Expr::Block{ span: $span, params: $2?, vars: $3?, exprs: $4? }) };
BlockParamsOpt -> Result<Vec<Span>, ()>:
      BlockParams "|" { $1 }
    | { Ok(vec![]) }
    ;
BlockParams -> Result<Vec<Span>, ()>:
      ":" "ID" { Ok(vec![map_err($2)?.span()]) }
    | BlockParams ":" "ID" { flattenr_span($1, $3) }
    ;
Argument -> Result<Option<Span>, ()>:
      "ID" { Ok(Some(map_err($1)?.span())) }
    | { unimplemented!() }
    ;
StringConst -> Result<Expr, ()>:
      "#" "STRING" { unimplemented!() }
    | "#" "ID" { Ok(Expr::Symbol(map_err($2)?.span())) }
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

use lrpar::{Lexeme, Span};

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

/// Flatten `rhs` into `lhs`.
fn flattenr_span(lhs: Result<Vec<Span>, ()>, rhs: Result<Lexeme<StorageT>, Lexeme<StorageT>>) -> Result<Vec<Span>, ()> {
    let mut flt = lhs?;
    flt.push(rhs.map_err(|_| ())?.span());
    Ok(flt)
}

fn span_merge(lhs: Result<Lexeme<StorageT>, Lexeme<StorageT>>, rhs: Span) -> Span {
    let lhs_span = match lhs {
        Ok(l) | Err(l) => l.span()
    };
    Span::new(lhs_span.start(), rhs.end())
}

use crate::compiler::ast::*;
