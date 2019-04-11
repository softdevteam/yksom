// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

use std::{collections::hash_map::HashMap, path::Path};

use indexmap::map::{Entry, IndexMap};
use itertools::Itertools;
use lrpar::{Lexeme, Lexer};

use super::{
    ast, cobjects,
    instrs::{Instr, Primitive},
    StorageT,
};

pub struct Compiler<'a> {
    lexer: &'a Lexer<StorageT>,
    path: &'a Path,
    instrs: Vec<Instr>,
    sends: IndexMap<(String, usize), usize>,
    consts: IndexMap<cobjects::Const, usize>,
    vars_stack: Vec<HashMap<&'a str, u32>>,
}

impl<'a> Compiler<'a> {
    pub fn compile(
        lexer: &Lexer<StorageT>,
        path: &Path,
        astcls: &ast::Class,
    ) -> Result<cobjects::Class, String> {
        let mut compiler = Compiler {
            lexer,
            path,
            instrs: Vec::new(),
            sends: IndexMap::new(),
            consts: IndexMap::new(),
            vars_stack: Vec::new(),
        };

        let mut methods = Vec::with_capacity(astcls.methods.len());
        let mut errs = vec![];
        for astmeth in &astcls.methods {
            match compiler.c_method(&astmeth) {
                Ok(m) => {
                    methods.push(m);
                }
                Err(mut e) => {
                    errs.extend(e.drain(..));
                }
            }
        }

        if !errs.is_empty() {
            let err_strs = errs
                .iter()
                .map(|(lexeme, msg)| {
                    let (line_off, col) = compiler.lexer.line_col(lexeme.start());
                    let line = compiler.lexer.surrounding_line_str(lexeme.start());
                    format!(
                        "File '{}', line {}, column {}:\n  {}\n{}",
                        compiler.path.to_str().unwrap(),
                        line_off,
                        col,
                        line.trim(),
                        msg
                    )
                })
                .join("\n\n");
            return Err(err_strs);
        }

        Ok(cobjects::Class {
            path: compiler.path.to_path_buf(),
            methods,
            instrs: compiler.instrs,
            consts: compiler.consts.into_iter().map(|(k, _)| k).collect(),
            sends: compiler.sends.into_iter().map(|(k, _)| k).collect(),
        })
    }

    fn const_off(&mut self, c: cobjects::Const) -> usize {
        let off = self.consts.len();
        match self.consts.entry(c) {
            Entry::Occupied(e) => *e.get(),
            Entry::Vacant(e) => {
                e.insert(off);
                off
            }
        }
    }

    fn send_off(&mut self, m: (String, usize)) -> usize {
        let off = self.sends.len();
        match self.sends.entry(m) {
            Entry::Occupied(e) => *e.get(),
            Entry::Vacant(e) => {
                e.insert(off);
                off
            }
        }
    }

    fn c_method(
        &mut self,
        astmeth: &ast::Method,
    ) -> Result<cobjects::Method, Vec<(Lexeme<StorageT>, String)>> {
        let mut vars = HashMap::new();
        vars.insert("self", 0);
        self.vars_stack.push(vars);
        let (name, body) = match astmeth.name {
            ast::MethodName::Id(lexeme) => {
                let name = self.lexer.lexeme_str(&lexeme).to_string();
                let body = self.c_body((lexeme, &name), &astmeth.body)?;
                (name, body)
            }
        };
        self.vars_stack.pop();
        Ok(cobjects::Method { name, body })
    }

    fn c_body(
        &mut self,
        name: (Lexeme<StorageT>, &str),
        body: &ast::MethodBody,
    ) -> Result<cobjects::MethodBody, Vec<(Lexeme<StorageT>, String)>> {
        match body {
            ast::MethodBody::Primitive => match name.1 {
                "new" => Ok(cobjects::MethodBody::Primitive(Primitive::New)),
                "println" => Ok(cobjects::MethodBody::Primitive(Primitive::PrintLn)),
                _ => Err(vec![(name.0, format!("Unknown primitive '{}'", name.1))]),
            },
            ast::MethodBody::Body { exprs } => {
                let body_idx = self.instrs.len();
                for e in exprs {
                    // We deliberately bomb out at the first error in a method on the basis that
                    // it's likely to lead to many repetitive errors.
                    self.c_expr(e)?;
                }
                Ok(cobjects::MethodBody::User(body_idx))
            }
        }
    }

    fn c_expr(&mut self, expr: &ast::Expr) -> Result<(), Vec<(Lexeme<StorageT>, String)>> {
        match expr {
            ast::Expr::KeywordMsg { receiver, msglist } => {
                self.c_expr(receiver)?;
                let mut mn = String::new();
                for (kw, expr) in msglist {
                    mn.push_str(self.lexer.lexeme_str(&kw));
                    self.c_expr(expr)?;
                }
                let send_off = self.send_off((mn, msglist.len()));
                self.instrs.push(Instr::Send(send_off));
                Ok(())
            }
            ast::Expr::UnaryMsg { receiver, ids } => {
                self.c_expr(receiver)?;
                for id in ids {
                    let send_off = self.send_off((self.lexer.lexeme_str(&id).to_string(), 0));
                    self.instrs.push(Instr::Send(send_off));
                }
                Ok(())
            }
            ast::Expr::String(lexeme) => {
                // XXX are there string escaping rules we need to take account of?
                let s = self.lexer.lexeme_str(&lexeme).to_string();
                let const_off = self.const_off(cobjects::Const::String(s));
                self.instrs.push(Instr::Const(const_off));
                Ok(())
            }
            ast::Expr::VarLookup(lexeme) => {
                let name = self.lexer.lexeme_str(&lexeme);
                match self.vars_stack.last().unwrap().get(name) {
                    Some(n) => {
                        self.instrs.push(Instr::VarLookup(*n));
                        Ok(())
                    }
                    None => Err(vec![(*lexeme, format!("Unknown variable '{}'", name))]),
                }
            }
        }
    }
}
