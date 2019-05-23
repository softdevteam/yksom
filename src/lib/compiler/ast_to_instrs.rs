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
use static_assertions::const_assert_eq;

use super::{
    ast, cobjects,
    instrs::{Builtin, Instr, Primitive, SELF_VAR},
    StorageT,
};

pub struct Compiler<'a> {
    lexer: &'a Lexer<StorageT>,
    path: &'a Path,
    instrs: Vec<Instr>,
    sends: IndexMap<(String, usize), usize>,
    consts: IndexMap<cobjects::Const, usize>,
    vars_stack: Vec<HashMap<&'a str, usize>>,
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

        let mut errs = vec![];
        let supercls = astcls.supername.map(|x| lexer.lexeme_str(&x).to_owned());

        let mut inst_vars = HashMap::with_capacity(astcls.inst_vars.len());
        for lexeme in &astcls.inst_vars {
            let vars_len = inst_vars.len();
            inst_vars.insert(lexer.lexeme_str(&lexeme), vars_len);
        }
        compiler.vars_stack.push(inst_vars);

        let mut methods = Vec::with_capacity(astcls.methods.len());
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
            name: lexer.lexeme_str(&astcls.name).to_owned(),
            path: compiler.path.to_path_buf(),
            supercls,
            num_inst_vars: astcls.inst_vars.len(),
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
        let (name, args) = match astmeth.name {
            ast::MethodName::Id(lexeme) => {
                ((lexeme, self.lexer.lexeme_str(&lexeme).to_string()), vec![])
            }
            ast::MethodName::Keywords(ref pairs) => {
                let name = pairs
                    .iter()
                    .map(|x| self.lexer.lexeme_str(&x.0))
                    .collect::<String>();
                let args = pairs.iter().map(|x| x.1).collect::<Vec<_>>();
                ((pairs[0].0, name), args)
            }
        };
        let body = self.c_body((name.0, &name.1), args, &astmeth.body)?;
        Ok(cobjects::Method { name: name.1, body })
    }

    fn c_body(
        &mut self,
        name: (Lexeme<StorageT>, &str),
        _args: Vec<Lexeme<StorageT>>,
        body: &ast::MethodBody,
    ) -> Result<cobjects::MethodBody, Vec<(Lexeme<StorageT>, String)>> {
        match body {
            ast::MethodBody::Primitive => match name.1 {
                "class" => Ok(cobjects::MethodBody::Primitive(Primitive::Class)),
                "concatenate:" => Ok(cobjects::MethodBody::Primitive(Primitive::Concatenate)),
                "name" => Ok(cobjects::MethodBody::Primitive(Primitive::Name)),
                "new" => Ok(cobjects::MethodBody::Primitive(Primitive::New)),
                "println" => Ok(cobjects::MethodBody::Primitive(Primitive::PrintLn)),
                _ => Err(vec![(name.0, format!("Unknown primitive '{}'", name.1))]),
            },
            ast::MethodBody::Body {
                vars: vars_lexemes,
                exprs,
            } => {
                let mut vars = HashMap::new();
                const_assert_eq!(SELF_VAR, 0);
                vars.insert("self", SELF_VAR);
                for lexeme in vars_lexemes {
                    let vars_len = vars.len();
                    vars.insert(self.lexer.lexeme_str(&lexeme), vars_len);
                }
                let num_vars = vars.len();
                self.vars_stack.push(vars);
                let bytecode_off = self.instrs.len();
                // We implicitly assume that the VM sets SELF_VAR to self.
                for (i, e) in exprs.iter().enumerate() {
                    // We deliberately bomb out at the first error in a method on the basis that
                    // it's likely to lead to many repetitive errors.
                    self.c_expr(e)?;
                    if i == exprs.len() - 1 {
                        self.instrs.push(Instr::Return);
                    } else {
                        self.instrs.push(Instr::Pop);
                    }
                }
                self.vars_stack.pop();
                Ok(cobjects::MethodBody::User {
                    num_vars,
                    bytecode_off,
                })
            }
        }
    }

    fn c_expr(&mut self, expr: &ast::Expr) -> Result<(), Vec<(Lexeme<StorageT>, String)>> {
        match expr {
            ast::Expr::Assign { id, expr } => {
                let (depth, var_num) = self.find_var(&id)?;
                self.c_expr(expr)?;
                debug_assert_eq!(self.vars_stack.len(), 2);
                match depth {
                    0 => self.instrs.push(Instr::InstVarSet(var_num)),
                    _ => self.instrs.push(Instr::VarSet(var_num)),
                }
                Ok(())
            }
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
            ast::Expr::Return => {
                self.instrs.push(Instr::Return);
                Ok(())
            }
            ast::Expr::String(lexeme) => {
                // XXX are there string escaping rules we need to take account of?
                let s_orig = self.lexer.lexeme_str(&lexeme);
                // Strip off the beginning/end quotes.
                let s = s_orig[1..s_orig.len() - 1].to_owned();
                let const_off = self.const_off(cobjects::Const::String(s));
                self.instrs.push(Instr::Const(const_off));
                Ok(())
            }
            ast::Expr::VarLookup(lexeme) => {
                match self.find_var(&lexeme) {
                    Ok((depth, var_num)) => {
                        debug_assert_eq!(self.vars_stack.len(), 2);
                        match depth {
                            0 => self.instrs.push(Instr::InstVarLookup(var_num)),
                            _ => self.instrs.push(Instr::VarLookup(var_num)),
                        }
                    }
                    Err(e) => match self.lexer.lexeme_str(&lexeme) {
                        "false" => self.instrs.push(Instr::Builtin(Builtin::False)),
                        "true" => self.instrs.push(Instr::Builtin(Builtin::True)),
                        _ => return Err(e),
                    },
                }
                Ok(())
            }
        }
    }

    /// Find the variable `name` in the variable stack returning a tuple `Some((depth, var_num))`
    /// or `Err` if the variable isn't found. `depth` is the depth of the `HashMap` in `vars_stack`
    /// (i.e. if `name` is found in the first element of the stack this will be 0). `var_num` is
    /// the variable number within that `HashMap`.
    fn find_var(
        &self,
        lexeme: &Lexeme<StorageT>,
    ) -> Result<(usize, usize), Vec<(Lexeme<StorageT>, String)>> {
        let name = self.lexer.lexeme_str(lexeme);
        for (depth, vars) in self.vars_stack.iter().enumerate().rev() {
            if let Some(n) = vars.get(name) {
                return Ok((depth, *n));
            }
        }
        Err(vec![(*lexeme, format!("Unknown variable '{}'", name))])
    }
}
