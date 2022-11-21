use std::{
    cmp::max,
    collections::hash_map::{self, HashMap},
    path::Path,
};

use itertools::Itertools;
use lrpar::{NonStreamingLexer, Span};
use num_bigint::BigInt;
use smartstring::alias::String as SmartString;
use std::gc::{Gc, NonFinalizable};

use crate::{
    compiler::{
        ast,
        instrs::{Instr, Primitive, UpVarDef},
        StorageT,
    },
    vm::{
        function::Function,
        objects::{Class, Method, MethodsArray, String_},
        val::Val,
        VM,
    },
};

// A variable with a name which the user cannot reference.
const CLOSURE_RETURN_VAR: &str = "$$closurereturn$$";

pub struct Compiler<'a, 'input> {
    lexer: &'a dyn NonStreamingLexer<'input, StorageT>,
    path: &'a Path,
    upvars_stack: Vec<Vec<(SmartString, UpVarDef)>>,
    /// The stack of local variables at the current point of evaluation. Maps variable names to
    /// `(captured, var idx)`.
    locals_stack: Vec<HashMap<SmartString, (bool, usize)>>,
    blocks_stack: Vec<Vec<Gc<Function>>>,
    /// Since SOM's "^" operator returns from the enclosed method, we need to track whether we are
    /// in a closure -- and, if so, how many nested closures we are inside at the current point of
    /// evaluation.
    closure_depth: usize,
}

type CompileResult<T> = Result<T, Vec<(Span, String)>>;

#[derive(Debug)]
enum VarLookup {
    Local(usize),
    UpVar(usize),
    InstVar(usize),
    Unknown,
}

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
            locals_stack: Vec::new(),
            upvars_stack: Vec::new(),
            blocks_stack: Vec::new(),
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

        debug_assert_eq!(compiler.locals_stack.len(), 0);
        debug_assert_eq!(compiler.upvars_stack.len(), 0);
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
                    .map(|(k, v)| (k.to_owned(), (false, *v))),
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
                    e.insert((false, vars_len));
                }
            }
        }
        self.upvars_stack.push(Vec::new());
        self.locals_stack.push(inst_vars);

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
                    self.locals_stack.truncate(1);
                    self.upvars_stack.truncate(1);
                    self.blocks_stack.truncate(1);
                }
            }
        }
        debug_assert!(self.locals_stack.len() == 1);
        debug_assert!(self.upvars_stack.len() == 1 && self.upvars_stack.last().unwrap().is_empty());
        self.upvars_stack.pop();
        let inst_vars_map = self.locals_stack[0]
            .iter()
            .map(|(k, v)| (k.clone(), v.1))
            .collect::<HashMap<SmartString, usize>>();
        self.locals_stack.pop();
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
            NonFinalizable::new(inst_vars_map),
            methods,
            NonFinalizable::new(methods_map),
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
        // We later have to go over all the `BlockInfo`s and update their `method` field to point
        // to this method, once it has been created.
        let func = self.c_body(vm, astmeth.span, (name.0, &name.1), args, &astmeth.body)?;
        let sig = String_::new_sym(vm, name.1.clone());
        let meth = Method::new(vm, sig, func);
        let meth_gc = meth.tobj(vm).unwrap().downcast::<Method>().unwrap();

        // We now need to set the containing method of all blocks (and, recursively, their child
        // blocks) to be the method itself.
        fn patch(f: &Function, meth: Gc<Method>) {
            f.set_containing_method(meth);
            for blk_func in f.block_funcs().iter() {
                patch(blk_func, meth);
            }
        }
        patch(&meth_gc.func, meth_gc);

        Ok((name.1, meth))
    }

    fn c_body(
        &mut self,
        vm: &mut VM,
        span: Span,
        name: (Span, &str),
        params: Vec<Span>,
        body: &ast::MethodBody,
    ) -> CompileResult<Function> {
        match body {
            ast::MethodBody::Primitive => {
                let (num_params, primitive) = match name.1 {
                    "+" => (1, Primitive::Add),
                    "-" => (1, Primitive::Sub),
                    "*" => (1, Primitive::Mul),
                    "/" => (1, Primitive::Div),
                    "//" => (1, Primitive::DoubleDiv),
                    "%" => (1, Primitive::Mod),
                    "=" => (1, Primitive::Equals),
                    "==" => (1, Primitive::RefEquals),
                    "~=" => (1, Primitive::NotEquals),
                    "<<" => (1, Primitive::Shl),
                    "<" => (1, Primitive::LessThan),
                    "<=" => (1, Primitive::LessThanEquals),
                    ">" => (1, Primitive::GreaterThan),
                    ">>>" => (1, Primitive::Shr),
                    ">=" => (1, Primitive::GreaterThanEquals),
                    "&" => (1, Primitive::And),
                    "bitXor:" => (1, Primitive::BitXor),
                    "as32BitSignedValue" => (0, Primitive::As32BitSignedValue),
                    "as32BitUnsignedValue" => (0, Primitive::As32BitUnsignedValue),
                    "asDouble" => (0, Primitive::AsDouble),
                    "asInteger" => (0, Primitive::AsInteger),
                    "asString" => (0, Primitive::AsString),
                    "asSymbol" => (0, Primitive::AsSymbol),
                    "at:" => (1, Primitive::At),
                    "at:put:" => (2, Primitive::AtPut),
                    "atRandom" => (0, Primitive::AtRandom),
                    "class" => (0, Primitive::Class),
                    "concatenate:" => (0, Primitive::Concatenate),
                    "cos" => (0, Primitive::Cos),
                    "errorPrint:" => (1, Primitive::ErrorPrint),
                    "errorPrintln:" => (1, Primitive::ErrorPrintln),
                    "exit:" => (1, Primitive::Exit),
                    "fields" => (0, Primitive::Fields),
                    "fromString:" => (1, Primitive::FromString),
                    "fullGC" => (0, Primitive::FullGC),
                    "global:" => (1, Primitive::Global),
                    "global:put:" => (2, Primitive::GlobalPut),
                    "halt" => (0, Primitive::Halt),
                    "hasGlobal:" => (1, Primitive::HasGlobal),
                    "hashcode" => (0, Primitive::Hashcode),
                    "holder" => (0, Primitive::Holder),
                    "inspect" => (0, Primitive::Inspect),
                    "instVarAt:" => (1, Primitive::InstVarAt),
                    "instVarAt:put:" => (2, Primitive::InstVarAtPut),
                    "instVarNamed:" => (1, Primitive::InstVarNamed),
                    "invokeOn:with:" => (2, Primitive::InvokeOnWith),
                    "isDigits" => (0, Primitive::IsDigits),
                    "isLetters" => (0, Primitive::IsLetters),
                    "isWhiteSpace" => (0, Primitive::IsWhiteSpace),
                    #[cfg(feature = "krun_harness")]
                    "krunInit" => (0, Primitive::KrunInit),
                    #[cfg(feature = "krun_harness")]
                    "krunDone" => (0, Primitive::KrunDone),
                    #[cfg(feature = "krun_harness")]
                    "krunMeasure:" => (1, Primitive::KrunMeasure),
                    #[cfg(feature = "krun_harness")]
                    "krunGetCoreCyclesDouble:core:" => (2, Primitive::KrunGetCoreCyclesDouble),
                    #[cfg(feature = "krun_harness")]
                    "krunGetNumCores" => (0, Primitive::KrunGetNumCores),
                    #[cfg(feature = "krun_harness")]
                    "krunGetWallclock:" => (1, Primitive::KrunGetWallclock),
                    "length" => (0, Primitive::Length),
                    "load:" => (1, Primitive::Load),
                    "loadFile:" => (1, Primitive::LoadFile),
                    "methods" => (0, Primitive::Methods),
                    "name" => (0, Primitive::Name),
                    "new" => (0, Primitive::New),
                    "new:" => (0, Primitive::NewArray),
                    "objectSize" => (0, Primitive::ObjectSize),
                    "perform:" => (1, Primitive::Perform),
                    "perform:inSuperclass:" => (2, Primitive::PerformInSuperClass),
                    "perform:withArguments:" => (2, Primitive::PerformWithArguments),
                    "perform:withArguments:inSuperclass:" => {
                        (3, Primitive::PerformWithArgumentsInSuperClass)
                    }
                    "PositiveInfinity" => (0, Primitive::PositiveInfinity),
                    "primSubstringFrom:to:" => (2, Primitive::PrimSubstringFromTo),
                    "printNewline" => (0, Primitive::PrintNewline),
                    "printString:" => (1, Primitive::PrintString),
                    "printStackTrace" => (1, Primitive::PrintStackTrace),
                    "rem:" => (1, Primitive::Rem),
                    "signature" => (0, Primitive::Signature),
                    "sin" => (0, Primitive::Sin),
                    "sqrt" => (0, Primitive::Sqrt),
                    "restart" => (0, Primitive::Restart),
                    "round" => (0, Primitive::Round),
                    "superclass" => (0, Primitive::Superclass),
                    "ticks" => (0, Primitive::Ticks),
                    "time" => (0, Primitive::Time),
                    "value" => (0, Primitive::Value(0)),
                    "value:" => (1, Primitive::Value(1)),
                    "value:with:" => (2, Primitive::Value(2)),
                    _ => return Err(vec![(name.0, format!("Unknown primitive '{}'", name.1))]),
                };

                Ok(Function::new_primitive(vm, num_params + 1, primitive))
            }
            ast::MethodBody::Body { vars, exprs } => {
                let bytecode_off = vm.instrs_len();
                let (max_stack, block_funcs, upvars) =
                    self.c_block(vm, true, span, &params, &vars, exprs)?;
                debug_assert_eq!(upvars.len(), 0);
                Ok(Function::new_bytecode(
                    vm,
                    params.len() + 1,
                    params.len() + 1 + vars.len(),
                    bytecode_off,
                    None,
                    max_stack,
                    Vec::new(),
                    block_funcs,
                ))
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
    ) -> CompileResult<(usize, Vec<Gc<Function>>, Vec<UpVarDef>)> {
        self.upvars_stack.push(Vec::new());
        let mut vars = HashMap::new();
        vars.insert(SmartString::from("self"), (false, 0));
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
                    e.insert((false, vars_len));
                    Ok(vars_len)
                }
            }
        };

        // The VM assumes that the 'n' arguments are stored in variables 1..n+1.
        for param in params.iter() {
            process_var(*param)?;
        }

        for var in vars_spans {
            process_var(*var)?;
        }

        self.locals_stack.push(vars);
        self.blocks_stack.push(Vec::new());
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
            debug_assert_eq!(self.locals_stack.last().unwrap().get("self").unwrap().1, 0);
            vm.instrs_push(Instr::LocalVarLookup(0), span);
            max_stack = max(max_stack, 1);
            vm.instrs_push(Instr::Return, span);
        } else if exprs.is_empty() {
            let idx = vm.add_global("nil");
            vm.instrs_push(Instr::GlobalLookup(idx), span);
            vm.instrs_push(Instr::Return, span);
        } else {
            vm.instrs_push(Instr::Return, exprs.iter().last().unwrap().span());
        }
        self.locals_stack.pop();
        let upvars = self
            .upvars_stack
            .pop()
            .unwrap()
            .drain(..)
            .map(|x| x.1)
            .collect::<Vec<_>>();

        Ok((max_stack, self.blocks_stack.pop().unwrap(), upvars))
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
                let max_stack = self.c_expr(vm, expr)?;
                debug_assert!(max_stack > 0);
                match self.find_var(*id) {
                    VarLookup::Local(idx) => vm.instrs_push(Instr::LocalVarSet(idx), *span),
                    VarLookup::UpVar(idx) => vm.instrs_push(Instr::UpVarSet(idx), *span),
                    VarLookup::InstVar(idx) => vm.instrs_push(Instr::InstVarSet(idx), *span),
                    VarLookup::Unknown => {
                        return Err(vec![(
                            *span,
                            format!("No such field '{}' in class", self.lexer.span_str(*id)),
                        )])
                    }
                }
                Ok(max_stack)
            }
            ast::Expr::BinaryMsg { span, lhs, op, rhs } => {
                let mut stack_size = self.c_expr(vm, lhs)?;
                stack_size = max(stack_size, 1 + self.c_expr(vm, rhs)?);
                let send_off = vm.add_send((SmartString::from(self.lexer.span_str(*op)), 1));
                let instr = match lhs {
                    box ast::Expr::UnaryMsg {
                        receiver: box ast::Expr::VarLookup(span2),
                        ids,
                        span: _,
                    } if ids.len() == 0 && self.lexer.span_str(*span2) == "super" => {
                        Instr::SuperSend(send_off, vm.new_inline_cache())
                    }
                    _ => Instr::Send(send_off, vm.new_inline_cache()),
                };
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
                let instr_idx = vm.instrs_len();
                vm.instrs_push(Instr::Dummy, *span);
                self.closure_depth += 1;
                let bytecode_off = vm.instrs_len();
                let (max_stack, block_funcs, upvars) =
                    self.c_block(vm, false, *span, &params, vars, exprs)?;
                self.closure_depth -= 1;
                let bytecode_end = vm.instrs_len();
                let func = Gc::new(Function::new_bytecode(
                    vm,
                    params.len() + 1,
                    params.len() + 1 + vars.len(),
                    bytecode_off,
                    Some(bytecode_end),
                    max_stack,
                    upvars,
                    block_funcs,
                ));
                vm.instrs_set(
                    instr_idx,
                    Instr::Block(self.blocks_stack.last().unwrap().len()),
                    *span,
                );
                self.blocks_stack.last_mut().unwrap().push(func);
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
                    Err(e) => match self.lexer.span_str(*val).parse::<BigInt>() {
                        Ok(mut i) => {
                            if *is_negative {
                                i = -i;
                            }
                            let off = vm.add_bigint(i);
                            vm.instrs_push(Instr::ArbInt(off), *span);
                            Ok(1)
                        }
                        Err(_) => Err(vec![(*val, format!("{}", e))]),
                    },
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
                let instr = match receiver {
                    box ast::Expr::UnaryMsg {
                        receiver: box ast::Expr::VarLookup(span2),
                        ids,
                        span: _,
                    } if ids.len() == 0 && self.lexer.span_str(*span2) == "super" => {
                        Instr::SuperSend(send_off, vm.new_inline_cache())
                    }
                    _ => Instr::Send(send_off, vm.new_inline_cache()),
                };
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
                    // When we encounter a return in a closure, we need to provide some way for the
                    // VM to detect closures that have escaped their containing method. The way we
                    // do that is to rely on a variable that is defined in the containing method
                    // itself: at run-time we merely need to check whether the corresponding
                    // `UpVar` has been closed or not to detect whether a closure has escaped. We
                    // do this by relying on the method's `self` variable; to reference that we use
                    // a hacky guaranteed-can't-be-used-by-the-user variable name that threads
                    // "self" as an upvalue.
                    let locals_stack_len = self.locals_stack[1].len();
                    self.locals_stack[1]
                        .entry(SmartString::from(CLOSURE_RETURN_VAR))
                        .or_insert((false, locals_stack_len));
                    match self.find_var_name(CLOSURE_RETURN_VAR) {
                        VarLookup::UpVar(upidx) => {
                            vm.instrs_push(Instr::ClosureReturn(upidx), *span)
                        }
                        _ => unreachable!(),
                    }
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
                    VarLookup::Local(idx) => vm.instrs_push(Instr::LocalVarLookup(idx), *span),
                    VarLookup::UpVar(idx) => vm.instrs_push(Instr::UpVarLookup(idx), *span),
                    VarLookup::InstVar(idx) => vm.instrs_push(Instr::InstVarLookup(idx), *span),
                    VarLookup::Unknown => {
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
    fn find_var(&mut self, span: Span) -> VarLookup {
        self.find_var_name(self.lexer.span_str(span))
    }

    /// Find the variable at `span` in the variable stack returning a tuple `Some((depth,
    /// var_num))` or `Err` if the variable isn't found. `depth` is the number of closures away
    /// from the "current" one that the variable is found.
    fn find_var_name(&mut self, mut name: &str) -> VarLookup {
        name = match name {
            "super" => "self",
            s => s,
        };
        debug_assert!(!self.locals_stack.is_empty());
        debug_assert_eq!(self.locals_stack.len(), self.upvars_stack.len());

        let mut depth = self.locals_stack.len() - 1;
        while depth > 0 {
            if depth == 1 && name == CLOSURE_RETURN_VAR {
                name = "self";
            }

            if self.locals_stack[depth].contains_key(name) {
                let locals_stack_len = self.locals_stack.len();
                let upidx = {
                    let e = self.locals_stack[depth].get_mut(name).unwrap();
                    if depth == locals_stack_len - 1 {
                        return VarLookup::Local(e.1);
                    }
                    e.0 = true;
                    e.1
                };
                self.upvars_stack[depth + 1].push((
                    SmartString::from(name),
                    UpVarDef {
                        capture_local: true,
                        upidx,
                    },
                ));
                depth += 1;
            }

            for i in 0..self.upvars_stack[depth].len() {
                if &self.upvars_stack[depth][i].0 == name {
                    let mut upidx = i;
                    for j in depth + 1..self.upvars_stack.len() {
                        self.upvars_stack[j].push((
                            SmartString::from(name),
                            UpVarDef {
                                capture_local: false,
                                upidx,
                            },
                        ));
                        upidx = self.upvars_stack[j].len() - 1;
                    }
                    return VarLookup::UpVar(upidx);
                }
            }
            depth -= 1;
        }

        if let Some(ref e) = self.locals_stack[0].get(name) {
            return VarLookup::InstVar(e.1);
        }

        VarLookup::Unknown
    }
}
