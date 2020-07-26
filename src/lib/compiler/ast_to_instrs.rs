use std::{
    cmp::max,
    collections::hash_map::{self, HashMap},
    path::Path,
};

use itertools::Itertools;
use lrpar::{NonStreamingLexer, Span};
use rboehm::Gc;
use smartstring::alias::String as SmartString;

use crate::{
    compiler::{
        ast,
        instrs::{Instr, Primitive},
        StorageT,
    },
    vm::{
        objects::{BlockInfo, Class, Method, MethodBody, MethodsArray, String_},
        val::Val,
        VM,
    },
};

pub struct Compiler<'a, 'input> {
    lexer: &'a dyn NonStreamingLexer<'input, StorageT>,
    path: &'a Path,
    /// The stack of variables at the current point of evaluation.
    vars_stack: Vec<HashMap<SmartString, usize>>,
    /// Since SOM's "^" operator returns from the enclosed method, we need to track whether we are
    /// in a closure -- and, if so, how many nested closures we are inside at the current point of
    /// evaluation.
    closure_depth: usize,
}

type CompileResult<T> = Result<T, Vec<(Span, String)>>;

impl<'a, 'input> Compiler<'a, 'input> {
    pub fn compile(
        vm: &mut VM,
        lexer: &dyn NonStreamingLexer<StorageT>,
        path: &Path,
        astcls: &ast::Class,
    ) -> Result<(SmartString, Val), String> {
        let mut compiler = Compiler {
            lexer,
            path,
            vars_stack: Vec::new(),
            closure_depth: 0,
        };

        let name = SmartString::from(lexer.span_str(astcls.name));
        let (supercls_val, supercls_meta_val) = if name.as_str() != "Object" {
            let supercls_val = if let Some(n) = astcls.supername.map(|x| lexer.span_str(x)) {
                match vm.load_class(n) {
                    Ok(cls) => cls,
                    Err(()) => todo!(),
                }
            } else {
                vm.obj_cls
            };
            (supercls_val, supercls_val.get_class(vm))
        } else {
            (vm.nil, vm.nil)
        };

        let mut errs = vec![];
        // Create the metaclass (i.e. for a class C, this creates a class called "C class").
        let metacls = match compiler.c_class(
            vm,
            lexer,
            format!("{} class", name.as_str()).into(),
            supercls_meta_val,
            &astcls.class_inst_vars,
            &astcls.class_methods,
        ) {
            Ok(c) => Some(c),
            Err(e) => {
                errs.extend(e);
                None
            }
        };

        // Create the "main" class.
        let cls = match compiler.c_class(
            vm,
            lexer,
            name.clone(),
            supercls_val,
            &astcls.inst_vars,
            &astcls.methods,
        ) {
            Ok(c) => Some(c),
            Err(e) => {
                errs.extend(e);
                None
            }
        };

        if !errs.is_empty() {
            let err_strs = errs
                .into_iter()
                .map(|(span, msg)| {
                    let ((line_off, col), _) = compiler.lexer.line_col(span);
                    let line = compiler
                        .lexer
                        .span_lines_str(span)
                        .split('\n')
                        .next()
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

        let cls = cls.unwrap();
        let metacls = metacls.unwrap();
        metacls
            .downcast::<Class>(&vm)
            .unwrap()
            .set_metacls(&vm, vm.metacls_cls);
        cls.downcast::<Class>(&vm)
            .unwrap()
            .set_metacls(&vm, metacls);

        Ok((name, cls))
    }

    fn c_class(
        &mut self,
        vm: &mut VM,
        lexer: &'a dyn NonStreamingLexer<StorageT>,
        name: SmartString,
        supercls_val: Val,
        ast_inst_vars: &[Span],
        ast_methods: &[ast::Method],
    ) -> CompileResult<Val> {
        let instrs_off = vm.instrs_len();
        let mut inst_vars = if supercls_val != vm.nil {
            let supercls = supercls_val.downcast::<Class>(vm).unwrap();
            let mut inst_vars =
                HashMap::with_capacity(supercls.inst_vars_map.len() + ast_inst_vars.len());
            inst_vars.extend(
                supercls
                    .inst_vars_map
                    .iter()
                    .map(|(k, v)| (k.to_owned(), *v)),
            );
            for var in ast_inst_vars {
                let n = lexer.span_str(*var);
                if inst_vars.contains_key(n) {
                    return Err(vec![(
                        *var,
                        format!("Field '{}' is already defined in a superclass.", n),
                    )]);
                }
            }
            inst_vars
        } else {
            HashMap::with_capacity(ast_inst_vars.len())
        };
        for var in ast_inst_vars {
            let vars_len = inst_vars.len();
            let n = SmartString::from(lexer.span_str(*var));
            match inst_vars.entry(n) {
                hash_map::Entry::Occupied(_) => {
                    return Err(vec![(
                        *var,
                        format!(
                            "Field '{}' has already been defined in this class.",
                            self.lexer.span_str(*var)
                        ),
                    )])
                }
                hash_map::Entry::Vacant(e) => {
                    e.insert(vars_len);
                }
            }
        }
        self.vars_stack.push(inst_vars);

        let mut methods = Vec::with_capacity(ast_methods.len());
        let mut methods_map = HashMap::with_capacity(ast_methods.len());
        let mut errs = vec![];
        for astmeth in ast_methods {
            match self.c_method(vm, astmeth) {
                Ok((name, meth_val)) => {
                    methods.push(meth_val);
                    // methods_map uses SOM indexing (starting from 1)
                    methods_map.insert(name, methods.len());
                }
                Err(mut e) => {
                    errs.extend(e.drain(..));
                }
            }
        }
        let inst_vars_map = self.vars_stack[0]
            .iter()
            .map(|(k, v)| (k.clone(), *v))
            .collect::<HashMap<SmartString, usize>>();
        self.vars_stack.pop();
        if !errs.is_empty() {
            return Err(errs);
        }

        let name_val = String_::new_str(vm, name);
        let methods = MethodsArray::from_vec(vm, methods);
        let cls_val = Class::new(
            vm,
            vm.cls_cls,
            name_val,
            self.path.to_path_buf(),
            instrs_off,
            supercls_val,
            inst_vars_map,
            methods,
            methods_map,
        );
        let cls: Gc<Class> = cls_val.downcast(vm).unwrap();
        cls.set_methods_class(vm, cls_val);
        Ok(cls_val)
    }

    fn c_method(
        &mut self,
        vm: &mut VM,
        astmeth: &ast::Method,
    ) -> CompileResult<(SmartString, Val)> {
        let (name, args) = match astmeth.name {
            ast::MethodName::BinaryOp(op, arg) => {
                let arg_v = match arg {
                    Some(l) => vec![l],
                    None => vec![],
                };
                ((op, SmartString::from(self.lexer.span_str(op))), arg_v)
            }
            ast::MethodName::Id(span) => {
                ((span, SmartString::from(self.lexer.span_str(span))), vec![])
            }
            ast::MethodName::Keywords(ref pairs) => {
                let name = pairs
                    .iter()
                    .map(|x| self.lexer.span_str(x.0))
                    .collect::<SmartString>();
                let args = pairs.iter().map(|x| x.1).collect::<Vec<_>>();
                ((pairs[0].0, name), args)
            }
        };
        let args_len = args.len();
        let body = self.c_body(vm, astmeth.span, (name.0, &name.1), args, &astmeth.body)?;
        let sig = String_::new_sym(vm, name.1.clone());
        let meth = Method::new(vm, sig, args_len, body);
        Ok((name.1, meth))
    }

    fn c_body(
        &mut self,
        vm: &mut VM,
        span: Span,
        name: (Span, &str),
        params: Vec<Span>,
        body: &ast::MethodBody,
    ) -> CompileResult<MethodBody> {
        // We check the number of arguments at compile-time so that we don't have to check them
        // continuously at run-time.
        let requires_args = |n: usize| -> CompileResult<()> {
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
                ">>>" => {
                    requires_args(1)?;
                    Ok(MethodBody::Primitive(Primitive::Shr))
                }
                ">=" => {
                    requires_args(1)?;
                    Ok(MethodBody::Primitive(Primitive::GreaterThanEquals))
                }
                "&" => {
                    requires_args(1)?;
                    Ok(MethodBody::Primitive(Primitive::And))
                }
                "bitXor:" => Ok(MethodBody::Primitive(Primitive::BitXor)),
                "as32BitSignedValue" => Ok(MethodBody::Primitive(Primitive::As32BitSignedValue)),
                "as32BitUnsignedValue" => {
                    Ok(MethodBody::Primitive(Primitive::As32BitUnsignedValue))
                }
                "asInteger" => Ok(MethodBody::Primitive(Primitive::AsInteger)),
                "asString" => Ok(MethodBody::Primitive(Primitive::AsString)),
                "asSymbol" => Ok(MethodBody::Primitive(Primitive::AsSymbol)),
                "at:" => Ok(MethodBody::Primitive(Primitive::At)),
                "at:put:" => Ok(MethodBody::Primitive(Primitive::AtPut)),
                "atRandom" => Ok(MethodBody::Primitive(Primitive::AtRandom)),
                "class" => Ok(MethodBody::Primitive(Primitive::Class)),
                "concatenate:" => Ok(MethodBody::Primitive(Primitive::Concatenate)),
                "cos" => Ok(MethodBody::Primitive(Primitive::Cos)),
                "exit:" => Ok(MethodBody::Primitive(Primitive::Exit)),
                "fields" => Ok(MethodBody::Primitive(Primitive::Fields)),
                "fromString:" => Ok(MethodBody::Primitive(Primitive::FromString)),
                "fullGC" => Ok(MethodBody::Primitive(Primitive::FullGC)),
                "global:" => Ok(MethodBody::Primitive(Primitive::Global)),
                "global:put:" => Ok(MethodBody::Primitive(Primitive::GlobalPut)),
                "halt" => Ok(MethodBody::Primitive(Primitive::Halt)),
                "hasGlobal:" => Ok(MethodBody::Primitive(Primitive::HasGlobal)),
                "hashcode" => Ok(MethodBody::Primitive(Primitive::Hashcode)),
                "holder" => Ok(MethodBody::Primitive(Primitive::Holder)),
                "inspect" => Ok(MethodBody::Primitive(Primitive::Inspect)),
                "instVarAt:" => Ok(MethodBody::Primitive(Primitive::InstVarAt)),
                "instVarAt:put:" => Ok(MethodBody::Primitive(Primitive::InstVarAtPut)),
                "instVarNamed:" => Ok(MethodBody::Primitive(Primitive::InstVarNamed)),
                "invokeOn:with:" => Ok(MethodBody::Primitive(Primitive::InvokeOnWith)),
                "isDigits" => Ok(MethodBody::Primitive(Primitive::IsDigits)),
                "isLetters" => Ok(MethodBody::Primitive(Primitive::IsLetters)),
                "isWhiteSpace" => Ok(MethodBody::Primitive(Primitive::IsWhiteSpace)),
                "length" => Ok(MethodBody::Primitive(Primitive::Length)),
                "load:" => Ok(MethodBody::Primitive(Primitive::Load)),
                "methods" => Ok(MethodBody::Primitive(Primitive::Methods)),
                "name" => Ok(MethodBody::Primitive(Primitive::Name)),
                "new" => Ok(MethodBody::Primitive(Primitive::New)),
                "new:" => Ok(MethodBody::Primitive(Primitive::NewArray)),
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
                "PositiveInfinity" => Ok(MethodBody::Primitive(Primitive::PositiveInfinity)),
                "primSubstringFrom:to:" => {
                    Ok(MethodBody::Primitive(Primitive::PrimSubstringFromTo))
                }
                "printNewline" => Ok(MethodBody::Primitive(Primitive::PrintNewline)),
                "printString:" => Ok(MethodBody::Primitive(Primitive::PrintString)),
                "rem:" => Ok(MethodBody::Primitive(Primitive::Rem)),
                "signature" => Ok(MethodBody::Primitive(Primitive::Signature)),
                "sin" => Ok(MethodBody::Primitive(Primitive::Sin)),
                "sqrt" => Ok(MethodBody::Primitive(Primitive::Sqrt)),
                "restart" => Ok(MethodBody::Primitive(Primitive::Restart)),
                "round" => Ok(MethodBody::Primitive(Primitive::Round)),
                "superclass" => Ok(MethodBody::Primitive(Primitive::Superclass)),
                "ticks" => Ok(MethodBody::Primitive(Primitive::Ticks)),
                "time" => Ok(MethodBody::Primitive(Primitive::Time)),
                "value" => Ok(MethodBody::Primitive(Primitive::Value(0))),
                "value:" => Ok(MethodBody::Primitive(Primitive::Value(1))),
                "value:with:" => Ok(MethodBody::Primitive(Primitive::Value(2))),
                _ => Err(vec![(name.0, format!("Unknown primitive '{}'", name.1))]),
            },
            ast::MethodBody::Body { vars, exprs } => {
                let bytecode_off = vm.instrs_len();
                let (num_vars, max_stack) = self.c_block(vm, true, span, &params, vars, exprs)?;
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
        vm: &mut VM,
        is_method: bool,
        span: Span,
        params: &[Span],
        vars_spans: &[Span],
        exprs: &[ast::Expr],
    ) -> CompileResult<(usize, usize)> {
        let mut vars = HashMap::new();
        if is_method {
            // The VM assumes that the first variable of a method is "self".
            vars.insert(SmartString::from("self"), 0);
        }

        let mut process_var = |var_sp: Span| {
            let vars_len = vars.len();
            let var_str = SmartString::from(self.lexer.span_str(var_sp));
            match vars.entry(var_str.clone()) {
                hash_map::Entry::Occupied(_) => Err(vec![(
                    var_sp,
                    format!(
                        "Variable '{}' shadows another of the same name",
                        var_str.as_str()
                    ),
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
                vm.instrs_push(Instr::Pop, e.span());
            }
        }
        // Blocks return the value of the last statement, but methods return `self`.
        if is_method {
            if !exprs.is_empty() {
                vm.instrs_push(Instr::Pop, span);
            }
            debug_assert_eq!(*self.vars_stack.last().unwrap().get("self").unwrap(), 0);
            vm.instrs_push(Instr::VarLookup(0, 0), span);
            max_stack = max(max_stack, 1);
            vm.instrs_push(Instr::Return, span);
        } else if exprs.is_empty() {
            let idx = vm.add_global("nil");
            vm.instrs_push(Instr::GlobalLookup(idx), span);
            vm.instrs_push(Instr::Return, span);
        } else {
            vm.instrs_push(Instr::Return, exprs.iter().last().unwrap().span());
        }
        self.vars_stack.pop();

        Ok((num_vars, max_stack))
    }

    /// Evaluate an expression, returning `Ok(max_stack_size)` if successful.
    fn c_expr(&mut self, vm: &mut VM, expr: &ast::Expr) -> CompileResult<usize> {
        match expr {
            ast::Expr::Array { span, items } => {
                let mut max_stack = max(items.len(), 1);
                for (i, it) in items.iter().enumerate() {
                    max_stack = max(max_stack, i + self.c_expr(vm, it)?);
                }
                vm.instrs_push(Instr::Array(items.len()), *span);
                Ok(max_stack)
            }
            ast::Expr::Assign { span, id, expr } => {
                let (depth, var_num) = match self.find_var(*id) {
                    Some((d, v)) => (d, v),
                    None => {
                        return Err(vec![(
                            *span,
                            format!("No such field '{}' in class", self.lexer.span_str(*id)),
                        )])
                    }
                };
                let max_stack = self.c_expr(vm, expr)?;
                if depth == self.vars_stack.len() - 1 {
                    vm.instrs_push(Instr::InstVarSet(var_num), *span);
                } else {
                    vm.instrs_push(Instr::VarSet(depth, var_num), *span);
                }
                debug_assert!(max_stack > 0);
                Ok(max_stack)
            }
            ast::Expr::BinaryMsg { span, lhs, op, rhs } => {
                let mut stack_size = self.c_expr(vm, lhs)?;
                stack_size = max(stack_size, 1 + self.c_expr(vm, rhs)?);
                let send_off = vm.add_send((SmartString::from(self.lexer.span_str(*op)), 1));
                let instr = Instr::Send(send_off, vm.new_inline_cache());
                vm.instrs_push(instr, *span);
                debug_assert!(stack_size > 0);
                Ok(stack_size)
            }
            ast::Expr::Block {
                span,
                params,
                vars,
                exprs,
            } => {
                let bytecode_off = vm.instrs_len();
                let blkinfo_idx = vm.push_blockinfo(BlockInfo {
                    bytecode_off,
                    bytecode_end: 0,
                    num_params: params.len(),
                    num_vars: 0,
                    max_stack: 0,
                });
                vm.instrs_push(Instr::Block(blkinfo_idx), *span);
                self.closure_depth += 1;
                let bytecode_off = vm.instrs_len();
                let (num_vars, max_stack) = self.c_block(vm, false, *span, &params, vars, exprs)?;
                self.closure_depth -= 1;
                let bytecode_end = vm.instrs_len();
                vm.set_blockinfo(
                    blkinfo_idx,
                    BlockInfo {
                        bytecode_off,
                        bytecode_end,
                        num_params: params.len(),
                        num_vars,
                        max_stack,
                    },
                );
                Ok(1)
            }
            ast::Expr::Double {
                span,
                is_negative,
                val,
            } => {
                let s = if *is_negative {
                    format!("-{}", self.lexer.span_str(*val))
                } else {
                    self.lexer.span_str(*val).to_owned()
                };
                match s.parse::<f64>() {
                    Ok(i) => {
                        vm.instrs_push(Instr::Double(i), *span);
                        Ok(1)
                    }
                    Err(e) => Err(vec![(*val, format!("{}", e))]),
                }
            }
            ast::Expr::Int {
                span,
                is_negative,
                val,
            } => {
                match self.lexer.span_str(*val).parse::<isize>() {
                    Ok(mut i) => {
                        if *is_negative {
                            // With twos complement, `0-i` will always succeed, but just in case...
                            i = 0isize.checked_sub(i).unwrap();
                        }
                        vm.instrs_push(Instr::Int(i), *span);
                        Ok(1)
                    }
                    Err(e) => Err(vec![(*val, format!("{}", e))]),
                }
            }
            ast::Expr::KeywordMsg {
                span,
                receiver,
                msglist,
            } => {
                let mut max_stack = self.c_expr(vm, receiver)?;
                let mut mn = SmartString::new();
                for (i, (kw, expr)) in msglist.iter().enumerate() {
                    mn.push_str(self.lexer.span_str(*kw));
                    let expr_stack = self.c_expr(vm, expr)?;
                    max_stack = max(max_stack, 1 + i + expr_stack);
                }
                let send_off = vm.add_send((mn, msglist.len()));
                let instr = Instr::Send(send_off, vm.new_inline_cache());
                vm.instrs_push(instr, *span);
                debug_assert!(max_stack > 0);
                Ok(max_stack)
            }
            ast::Expr::UnaryMsg {
                span,
                receiver,
                ids,
            } => {
                let max_stack = self.c_expr(vm, receiver)?;
                for (i, id) in ids.iter().enumerate() {
                    let send_off = vm.add_send((SmartString::from(self.lexer.span_str(*id)), 0));
                    let instr = match receiver {
                        box ast::Expr::VarLookup(span)
                            if i == 0 && self.lexer.span_str(*span) == "super" =>
                        {
                            Instr::SuperSend(send_off, vm.new_inline_cache())
                        }
                        _ => Instr::Send(send_off, vm.new_inline_cache()),
                    };
                    vm.instrs_push(instr, *span);
                }
                debug_assert!(max_stack > 0);
                Ok(max_stack)
            }
            ast::Expr::Return { span, expr } => {
                let max_stack = self.c_expr(vm, expr)?;
                if self.closure_depth == 0 {
                    vm.instrs_push(Instr::Return, *span);
                } else {
                    vm.instrs_push(Instr::ClosureReturn(self.closure_depth), *span);
                }
                debug_assert!(max_stack > 0);
                Ok(max_stack)
            }
            ast::Expr::String(span) => {
                let s_orig = self.lexer.span_str(*span);
                let mut new_s = SmartString::new();
                // Start by ignoring the beginning quote.
                let mut i = '\"'.len_utf8();
                // End by ignoring the beginning quote.
                while i < s_orig.len() - '\"'.len_utf8() {
                    let mut c = s_orig[i..].chars().next().unwrap();
                    if c == '\\' {
                        i += c.len_utf8();
                        let next_c = s_orig[i..].chars().next().unwrap();
                        c = match next_c {
                            't' => '\t',
                            'b' => '\x08',
                            'n' => '\n',
                            'r' => '\r',
                            'f' => '\x0C',
                            '\'' => '\'',
                            '\\' => '\\',
                            '0' => '\0',
                            x => {
                                return Err(vec![(
                                    Span::new(
                                        span.start() + i - c.len_utf8(),
                                        span.start() + i + next_c.len_utf8(),
                                    ),
                                    format!("Unknown escape sequence '\\{}'", x),
                                )]);
                            }
                        };
                    }
                    new_s.push(c);
                    i += c.len_utf8();
                }

                let instr = Instr::String(vm.add_string(new_s));
                vm.instrs_push(instr, *span);
                Ok(1)
            }
            ast::Expr::StringSymbol(span) => {
                // XXX are there string escaping rules we need to take account of?
                let s_orig = self.lexer.span_str(*span);
                // Strip off the beginning/end quotes.
                let s = SmartString::from(&s_orig[1..s_orig.len() - 1]);
                let instr = Instr::Symbol(vm.add_symbol(s));
                vm.instrs_push(instr, *span);
                Ok(1)
            }
            ast::Expr::Symbol(span) => {
                let s = SmartString::from(self.lexer.span_str(*span));
                let instr = Instr::Symbol(vm.add_symbol(s));
                vm.instrs_push(instr, *span);
                Ok(1)
            }
            ast::Expr::VarLookup(span) => {
                match self.find_var(*span) {
                    Some((depth, var_num)) => {
                        if depth == self.vars_stack.len() - 1 {
                            vm.instrs_push(Instr::InstVarLookup(var_num), *span);
                        } else {
                            vm.instrs_push(Instr::VarLookup(depth, var_num), *span);
                        }
                    }
                    None => {
                        let name = self.lexer.span_str(*span);
                        let instr = Instr::GlobalLookup(vm.add_global(name));
                        vm.instrs_push(instr, *span);
                    }
                }
                Ok(1)
            }
        }
    }

    /// Find the variable at `span` in the variable stack returning a tuple `Some((depth,
    /// var_num))` or `Err` if the variable isn't found. `depth` is the number of closures away
    /// from the "current" one that the variable is found.
    fn find_var(&self, span: Span) -> Option<(usize, usize)> {
        let name = match self.lexer.span_str(span) {
            "super" => "self",
            s => s,
        };
        for (depth, vars) in self.vars_stack.iter().enumerate().rev() {
            if let Some(n) = vars.get(name) {
                return Some((self.vars_stack.len() - depth - 1, *n));
            }
        }
        None
    }
}
