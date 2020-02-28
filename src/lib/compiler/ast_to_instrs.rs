use std::{
    cmp::max,
    collections::hash_map::{self, HashMap},
    path::Path,
};

use abgc::Gc;
use itertools::Itertools;
use lrpar::{Lexer, Span};

use crate::{
    compiler::{
        ast,
        instrs::{Builtin, Instr, Primitive},
        StorageT,
    },
    vm::{
        objects::{BlockInfo, Class, Method, MethodBody, String_},
        val::ValKind,
        VM,
    },
};

pub struct Compiler<'a> {
    lexer: &'a dyn Lexer<StorageT>,
    path: &'a Path,
    /// The stack of variables at the current point of evaluation.
    vars_stack: Vec<HashMap<&'a str, usize>>,
    /// Since SOM's "^" operator returns from the enclosed method, we need to track whether we are
    /// in a closure -- and, if so, how many nested closures we are inside at the current point of
    /// evaluation.
    closure_depth: usize,
}

impl<'a> Compiler<'a> {
    pub fn compile(
        vm: &VM,
        lexer: &dyn Lexer<StorageT>,
        path: &Path,
        astcls: &ast::Class,
    ) -> Result<Class, String> {
        let mut compiler = Compiler {
            lexer,
            path,
            vars_stack: Vec::new(),
            closure_depth: 0,
        };

        let mut errs = vec![];
        let name = lexer.span_str(astcls.name).to_owned();
        let supercls;
        if name != "Object" {
            if let Some(n) = astcls.supername.map(|x| lexer.span_str(x)) {
                supercls = match n {
                    "Block" => Some(vm.block_cls.clone()),
                    "Boolean" => Some(vm.bool_cls.clone()),
                    "nil" => None,
                    "String" => Some(vm.str_cls.clone()),
                    _ => unimplemented!(),
                };
            } else {
                supercls = Some(vm.obj_cls.clone());
            }
            // Whatever superclass has been chosen, it must have been initialised already or else
            // bad things will happen.
            debug_assert_ne!(
                supercls.as_ref().map(|x| x.valkind()),
                Some(ValKind::ILLEGAL)
            );
        } else {
            supercls = None;
        }

        let mut inst_vars = HashMap::with_capacity(astcls.inst_vars.len());
        for var in &astcls.inst_vars {
            let vars_len = inst_vars.len();
            inst_vars.insert(lexer.span_str(*var), vars_len);
        }
        compiler.vars_stack.push(inst_vars);

        let mut methods = HashMap::with_capacity(astcls.methods.len());
        for astmeth in &astcls.methods {
            match compiler.c_method(vm, &astmeth) {
                Ok(m) => {
                    methods.insert(m.name.clone(), Gc::new(m));
                }
                Err(mut e) => {
                    errs.extend(e.drain(..));
                }
            }
        }

        if !errs.is_empty() {
            let err_strs = errs
                .into_iter()
                .map(|(span, msg)| {
                    let ((line_off, col), _) = compiler.lexer.line_col(span);
                    let line = compiler
                        .lexer
                        .span_lines_str(span)
                        .split("\n")
                        .nth(0)
                        .unwrap();
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

        Ok(Class {
            name: String_::new(vm, name, true),
            path: compiler.path.to_path_buf(),
            supercls,
            num_inst_vars: astcls.inst_vars.len(),
            methods,
        })
    }

    fn c_method(&mut self, vm: &VM, astmeth: &ast::Method) -> Result<Method, Vec<(Span, String)>> {
        let (name, args) = match astmeth.name {
            ast::MethodName::BinaryOp(op, arg) => {
                let arg_v = match arg {
                    Some(l) => vec![l],
                    None => vec![],
                };
                ((op, self.lexer.span_str(op).to_string()), arg_v)
            }
            ast::MethodName::Id(span) => ((span, self.lexer.span_str(span).to_string()), vec![]),
            ast::MethodName::Keywords(ref pairs) => {
                let name = pairs
                    .iter()
                    .map(|x| self.lexer.span_str(x.0))
                    .collect::<String>();
                let args = pairs.iter().map(|x| x.1).collect::<Vec<_>>();
                ((pairs[0].0, name), args)
            }
        };
        let body = self.c_body(vm, (name.0, &name.1), args, &astmeth.body)?;
        Ok(Method { name: name.1, body })
    }

    fn c_body(
        &mut self,
        vm: &VM,
        name: (Span, &str),
        params: Vec<Span>,
        body: &ast::MethodBody,
    ) -> Result<MethodBody, Vec<(Span, String)>> {
        // We check the number of arguments at compile-time so that we don't have to check them
        // continuously at run-time.
        let requires_args = |n: usize| -> Result<(), Vec<(Span, String)>> {
            if params.len() != n {
                Err(vec![(
                    name.0,
                    format!("Expected {} parameters, got {}", n, params.len()),
                )])
            } else {
                Ok(())
            }
        };

        match body {
            ast::MethodBody::Primitive => match name.1 {
                "+" => {
                    requires_args(1)?;
                    Ok(MethodBody::Primitive(Primitive::Add))
                }
                "-" => {
                    requires_args(1)?;
                    Ok(MethodBody::Primitive(Primitive::Sub))
                }
                "*" => {
                    requires_args(1)?;
                    Ok(MethodBody::Primitive(Primitive::Mul))
                }
                "/" => {
                    requires_args(1)?;
                    Ok(MethodBody::Primitive(Primitive::Div))
                }
                "//" => {
                    requires_args(1)?;
                    Ok(MethodBody::Primitive(Primitive::DoubleDiv))
                }
                "%" => {
                    requires_args(1)?;
                    Ok(MethodBody::Primitive(Primitive::Mod))
                }
                "=" => {
                    requires_args(1)?;
                    Ok(MethodBody::Primitive(Primitive::Equals))
                }
                "==" => {
                    requires_args(1)?;
                    Ok(MethodBody::Primitive(Primitive::RefEquals))
                }
                "~=" => {
                    requires_args(1)?;
                    Ok(MethodBody::Primitive(Primitive::NotEquals))
                }
                "<<" => {
                    requires_args(1)?;
                    Ok(MethodBody::Primitive(Primitive::Shl))
                }
                "<" => {
                    requires_args(1)?;
                    Ok(MethodBody::Primitive(Primitive::LessThan))
                }
                "<=" => {
                    requires_args(1)?;
                    Ok(MethodBody::Primitive(Primitive::LessThanEquals))
                }
                ">" => {
                    requires_args(1)?;
                    Ok(MethodBody::Primitive(Primitive::GreaterThan))
                }
                ">=" => {
                    requires_args(1)?;
                    Ok(MethodBody::Primitive(Primitive::GreaterThanEquals))
                }
                "&" => {
                    requires_args(1)?;
                    Ok(MethodBody::Primitive(Primitive::And))
                }
                "bitXor:" => {
                    requires_args(1)?;
                    Ok(MethodBody::Primitive(Primitive::BitXor))
                }
                "sqrt" => Ok(MethodBody::Primitive(Primitive::Sqrt)),
                "asString" => Ok(MethodBody::Primitive(Primitive::AsString)),
                "asSymbol" => Ok(MethodBody::Primitive(Primitive::AsSymbol)),
                "class" => Ok(MethodBody::Primitive(Primitive::Class)),
                "concatenate:" => Ok(MethodBody::Primitive(Primitive::Concatenate)),
                "global:" => Ok(MethodBody::Primitive(Primitive::Global)),
                "global:put:" => Ok(MethodBody::Primitive(Primitive::GlobalPut)),
                "halt" => Ok(MethodBody::Primitive(Primitive::Halt)),
                "hashcode" => Ok(MethodBody::Primitive(Primitive::Hashcode)),
                "inspect" => Ok(MethodBody::Primitive(Primitive::Inspect)),
                "instVarAt:" => Ok(MethodBody::Primitive(Primitive::InstVarAt)),
                "instVarAt:put:" => Ok(MethodBody::Primitive(Primitive::InstVarAtPut)),
                "instVarNamed:" => Ok(MethodBody::Primitive(Primitive::InstVarNamed)),
                "name" => Ok(MethodBody::Primitive(Primitive::Name)),
                "new" => Ok(MethodBody::Primitive(Primitive::New)),
                "objectSize" => Ok(MethodBody::Primitive(Primitive::ObjectSize)),
                "perform:" => Ok(MethodBody::Primitive(Primitive::Perform)),
                "perform:inSuperclass:" => {
                    Ok(MethodBody::Primitive(Primitive::PerformInSuperClass))
                }
                "perform:withArguments:" => {
                    Ok(MethodBody::Primitive(Primitive::PerformWithArguments))
                }
                "perform:withArguments:inSuperclass:" => Ok(MethodBody::Primitive(
                    Primitive::PerformWithArgumentsInSuperClass,
                )),
                "printNewline" => Ok(MethodBody::Primitive(Primitive::PrintNewline)),
                "printString:" => Ok(MethodBody::Primitive(Primitive::PrintString)),
                "restart" => Ok(MethodBody::Primitive(Primitive::Restart)),
                "superclass" => Ok(MethodBody::Primitive(Primitive::Superclass)),
                "value" => Ok(MethodBody::Primitive(Primitive::Value(0))),
                "value:" => Ok(MethodBody::Primitive(Primitive::Value(1))),
                "value:with:" => Ok(MethodBody::Primitive(Primitive::Value(2))),
                _ => Err(vec![(name.0, format!("Unknown primitive '{}'", name.1))]),
            },
            ast::MethodBody::Body { vars, exprs } => {
                let bytecode_off = vm.instrs_len();
                let (num_vars, max_stack) = self.c_block(vm, true, &params, vars, exprs)?;
                Ok(MethodBody::User {
                    num_vars,
                    bytecode_off,
                    max_stack,
                })
            }
        }
    }

    /// Evaluate an expression, returning `Ok(max_stack_size)` if successful. Note that there is an
    /// implicit assumption that primitives never need more stack size than they take in (e.g. if
    /// they push an item on to the stack, they must have popped at least one element off it
    /// beforehand).
    fn c_block(
        &mut self,
        vm: &VM,
        is_method: bool,
        params: &[Span],
        vars_spans: &[Span],
        exprs: &[ast::Expr],
    ) -> Result<(usize, usize), Vec<(Span, String)>> {
        let mut vars = HashMap::new();
        if is_method {
            // The VM assumes that the first variable of a method is "self".
            vars.insert("self", 0);
        }

        let mut process_var = |var_sp: Span| {
            let vars_len = vars.len();
            let var_str = self.lexer.span_str(var_sp);
            match vars.entry(var_str) {
                hash_map::Entry::Occupied(_) => Err(vec![(
                    var_sp,
                    format!("Variable '{}' shadows another of the same name", var_str),
                )]),
                hash_map::Entry::Vacant(e) => {
                    e.insert(vars_len);
                    Ok(vars_len)
                }
            }
        };

        // The VM assumes that a blocks's arguments are stored in variables
        // 0..n and a method's arguments in 1..n+1.
        for param in params.iter() {
            process_var(*param)?;
        }

        for var in vars_spans {
            process_var(*var)?;
        }

        let num_vars = vars.len();
        self.vars_stack.push(vars);
        let mut max_stack = 0;
        for (i, e) in exprs.iter().enumerate() {
            // We deliberately bomb out at the first error in a method on the basis that
            // it's likely to lead to many repetitive errors.
            let stack_size = self.c_expr(vm, e)?;
            max_stack = max(max_stack, stack_size);
            if i != exprs.len() - 1 {
                vm.instrs_push(Instr::Pop);
            }
        }
        // Blocks return the value of the last statement, but methods return `self`.
        if is_method {
            vm.instrs_push(Instr::Pop);
            debug_assert_eq!(*self.vars_stack.last().unwrap().get("self").unwrap(), 0);
            vm.instrs_push(Instr::VarLookup(0, 0));
            max_stack = max(max_stack, 1);
        }
        vm.instrs_push(Instr::Return);
        self.vars_stack.pop();

        Ok((num_vars, max_stack))
    }

    /// Evaluate an expression, returning `Ok(max_stack_size)` if successful.
    fn c_expr(&mut self, vm: &VM, expr: &ast::Expr) -> Result<usize, Vec<(Span, String)>> {
        match expr {
            ast::Expr::Assign { id, expr } => {
                let (depth, var_num) = self.find_var(*id)?;
                let max_stack = self.c_expr(vm, expr)?;
                if depth == self.vars_stack.len() - 1 {
                    vm.instrs_push(Instr::InstVarSet(var_num));
                } else {
                    vm.instrs_push(Instr::VarSet(depth, var_num));
                }
                debug_assert!(max_stack > 0);
                Ok(max_stack)
            }
            ast::Expr::BinaryMsg { lhs, op, rhs } => {
                let mut stack_size = self.c_expr(vm, lhs)?;
                stack_size = max(stack_size, 1 + self.c_expr(vm, rhs)?);
                let send_off = vm.add_send((self.lexer.span_str(*op).to_string(), 1));
                vm.instrs_push(Instr::Send(send_off, vm.new_inline_cache()));
                debug_assert!(stack_size > 0);
                Ok(stack_size)
            }
            ast::Expr::Block {
                params,
                vars,
                exprs,
            } => {
                let blkinfo_idx = vm.push_blockinfo(BlockInfo {
                    bytecode_off: vm.instrs_len(),
                    bytecode_end: 0,
                    num_params: params.len(),
                    num_vars: 0,
                    max_stack: 0,
                });
                vm.instrs_push(Instr::Block(blkinfo_idx));
                self.closure_depth += 1;
                let bytecode_off = vm.instrs_len();
                let (num_vars, max_stack) = self.c_block(vm, false, &params, vars, exprs)?;
                self.closure_depth -= 1;
                vm.set_blockinfo(
                    blkinfo_idx,
                    BlockInfo {
                        bytecode_off,
                        bytecode_end: vm.instrs_len(),
                        num_params: params.len(),
                        num_vars,
                        max_stack,
                    },
                );
                Ok(1)
            }
            ast::Expr::Double { is_negative, val } => {
                let s = if *is_negative {
                    format!("-{}", self.lexer.span_str(*val))
                } else {
                    self.lexer.span_str(*val).to_owned()
                };
                match s.parse::<f64>() {
                    Ok(i) => {
                        vm.instrs_push(Instr::Double(i));
                        Ok(1)
                    }
                    Err(e) => Err(vec![(*val, format!("{}", e))]),
                }
            }
            ast::Expr::Int { is_negative, val } => {
                match self.lexer.span_str(*val).parse::<isize>() {
                    Ok(mut i) => {
                        if *is_negative {
                            // With twos complement, `0-i` will always succeed, but just in case...
                            i = 0isize.checked_sub(i).unwrap();
                        }
                        vm.instrs_push(Instr::Int(i));
                        Ok(1)
                    }
                    Err(e) => Err(vec![(*val, format!("{}", e))]),
                }
            }
            ast::Expr::KeywordMsg { receiver, msglist } => {
                let mut max_stack = self.c_expr(vm, receiver)?;
                let mut mn = String::new();
                for (i, (kw, expr)) in msglist.iter().enumerate() {
                    mn.push_str(self.lexer.span_str(*kw));
                    let expr_stack = self.c_expr(vm, expr)?;
                    max_stack = max(max_stack, 1 + i + expr_stack);
                }
                let send_off = vm.add_send((mn, msglist.len()));
                vm.instrs_push(Instr::Send(send_off, vm.new_inline_cache()));
                debug_assert!(max_stack > 0);
                Ok(max_stack)
            }
            ast::Expr::UnaryMsg { receiver, ids } => {
                let max_stack = self.c_expr(vm, receiver)?;
                for id in ids {
                    let send_off = vm.add_send((self.lexer.span_str(*id).to_string(), 0));
                    vm.instrs_push(Instr::Send(send_off, vm.new_inline_cache()));
                }
                debug_assert!(max_stack > 0);
                Ok(max_stack)
            }
            ast::Expr::Return(expr) => {
                let max_stack = self.c_expr(vm, expr)?;
                if self.closure_depth == 0 {
                    vm.instrs_push(Instr::Return);
                } else {
                    vm.instrs_push(Instr::ClosureReturn(self.closure_depth));
                }
                debug_assert!(max_stack > 0);
                Ok(max_stack)
            }
            ast::Expr::String(span) => {
                // XXX are there string escaping rules we need to take account of?
                let s_orig = self.lexer.span_str(*span);
                // Strip off the beginning/end quotes.
                let s = s_orig[1..s_orig.len() - 1].to_owned();
                vm.instrs_push(Instr::String(vm.add_string(s)));
                Ok(1)
            }
            ast::Expr::Symbol(span) => {
                // XXX are there string escaping rules we need to take account of?
                let s = self.lexer.span_str(*span);
                vm.instrs_push(Instr::Symbol(vm.add_symbol(s.to_owned())));
                Ok(1)
            }
            ast::Expr::VarLookup(span) => {
                match self.find_var(*span) {
                    Ok((depth, var_num)) => {
                        if depth == self.vars_stack.len() - 1 {
                            vm.instrs_push(Instr::InstVarLookup(var_num));
                        } else {
                            vm.instrs_push(Instr::VarLookup(depth, var_num));
                        }
                    }
                    Err(_) => {
                        let lex_string = self.lexer.span_str(*span);
                        match lex_string {
                            "nil" => vm.instrs_push(Instr::Builtin(Builtin::Nil)),
                            "false" => vm.instrs_push(Instr::Builtin(Builtin::False)),
                            "true" => vm.instrs_push(Instr::Builtin(Builtin::True)),
                            _ => {
                                vm.instrs_push(Instr::Global(
                                    vm.add_symbol(lex_string.to_string()),
                                ));
                            }
                        }
                    }
                }
                Ok(1)
            }
        }
    }

    /// Find the variable at `span` in the variable stack returning a tuple `Some((depth,
    /// var_num))` or `Err` if the variable isn't found. `depth` is the number of closures away
    /// from the "current" one that the variable is found.
    fn find_var(&self, span: Span) -> Result<(usize, usize), Vec<(Span, String)>> {
        let name = self.lexer.span_str(span);
        for (depth, vars) in self.vars_stack.iter().enumerate().rev() {
            if let Some(n) = vars.get(name) {
                return Ok((self.vars_stack.len() - depth - 1, *n));
            }
        }
        Err(vec![(span, format!("Unknown variable '{}'", name))])
    }
}
