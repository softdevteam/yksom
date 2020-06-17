//! The core part of the interpreter.

use std::{
    cell::UnsafeCell,
    collections::HashMap,
    convert::TryFrom,
    mem::size_of,
    path::{Path, PathBuf},
    process,
    str::FromStr,
    time::{SystemTime, UNIX_EPOCH},
};

use lrpar::Span;
use num_bigint::BigInt;
use rboehm::Gc;
use static_assertions::const_assert;

use crate::{
    compiler::{
        compile,
        instrs::{Instr, Primitive},
    },
    vm::{
        error::{VMError, VMErrorKind},
        objects::{
            ArbInt, Block, BlockInfo, Class, Double, Inst, Int, Method, MethodBody, NormalArray,
            StaticObjType, String_,
        },
        somstack::SOMStack,
        val::{Val, ValKind},
    },
};

pub const SOM_EXTENSION: &str = "som";

#[derive(Debug)]
/// The result of a non-top-level SOM send.
enum SendReturn {
    /// A closure wants to perform a return *n* frames up the call stack.
    ClosureReturn(usize),
    /// An error has occurred.
    Err(Box<VMError>),
    /// A return value has been left at the appropriate place on the SOM stack.
    Val,
}

/// The core VM struct.
pub struct VM {
    classpath: Vec<PathBuf>,
    pub array_cls: Val,
    pub block_cls: Val,
    pub block1_cls: Val,
    pub block2_cls: Val,
    pub block3_cls: Val,
    pub bool_cls: Val,
    pub cls_cls: Val,
    pub double_cls: Val,
    pub false_cls: Val,
    pub int_cls: Val,
    pub metacls_cls: Val,
    pub method_cls: Val,
    pub nil_cls: Val,
    pub obj_cls: Val,
    pub str_cls: Val,
    pub sym_cls: Val,
    pub system_cls: Val,
    pub true_cls: Val,
    pub false_: Val,
    pub nil: Val,
    pub system: Val,
    pub true_: Val,
    blockinfos: Vec<BlockInfo>,
    /// The current known set of globals including those not yet assigned to: in other words, it is
    /// expected that some entries of this `Vec` are illegal (i.e. created by `Val::illegal`).
    globals: Vec<Val>,
    reverse_globals: HashMap<String, usize>,
    inline_caches: Vec<Option<(Val, Gc<Method>)>>,
    /// `instrs` and `instr_span`s are always the same length: they are separated only because we
    /// rarely access `instr_spans`.
    instrs: Vec<Instr>,
    instr_spans: Vec<Span>,
    sends: Vec<(Gc<String>, usize)>,
    /// reverse_sends is an optimisation allowing us to reuse sends: it maps a send `(String,
    /// usize)` to a `usize` where the latter represents the index of the send in `sends`.
    reverse_sends: HashMap<(Gc<String>, usize), usize>,
    stack: SOMStack,
    strings: Vec<Val>,
    /// reverse_strings is an optimisation allowing us to reuse strings: it maps a `String to a
    /// `usize` where the latter represents the index of the string in `strings`.
    reverse_strings: HashMap<String, usize>,
    symbols: Vec<Val>,
    reverse_symbols: HashMap<String, usize>,
    frames: Vec<Frame>,
}

impl VM {
    pub fn new(classpath: Vec<PathBuf>) -> Self {
        // The bootstrapping phase is delicate: we need to bootstrap the Object, Class, and Nil
        // classes before we can create basic objects like nil. We thus perform bootstrapping in
        // two phases: the "very delicate" phase (with very strict rules on what is possible)
        // followed by the "slightly delicate phase" (with looser, but still fairly strict, rules
        // on what is possible).

        let mut vm = VM {
            classpath,
            array_cls: Val::illegal(),
            block_cls: Val::illegal(),
            block1_cls: Val::illegal(),
            block2_cls: Val::illegal(),
            block3_cls: Val::illegal(),
            bool_cls: Val::illegal(),
            cls_cls: Val::illegal(),
            double_cls: Val::illegal(),
            false_cls: Val::illegal(),
            int_cls: Val::illegal(),
            metacls_cls: Val::illegal(),
            method_cls: Val::illegal(),
            obj_cls: Val::illegal(),
            nil_cls: Val::illegal(),
            str_cls: Val::illegal(),
            sym_cls: Val::illegal(),
            system_cls: Val::illegal(),
            true_cls: Val::illegal(),
            false_: Val::illegal(),
            nil: Val::illegal(),
            system: Val::illegal(),
            true_: Val::illegal(),
            blockinfos: Vec::new(),
            globals: Vec::new(),
            reverse_globals: HashMap::new(),
            inline_caches: Vec::new(),
            instrs: Vec::new(),
            instr_spans: Vec::new(),
            sends: Vec::new(),
            reverse_sends: HashMap::new(),
            stack: SOMStack::new(),
            strings: Vec::new(),
            reverse_strings: HashMap::new(),
            symbols: Vec::new(),
            reverse_symbols: HashMap::new(),
            frames: Vec::new(),
        };

        // These two phases must be executed in the correct order.
        vm = vm.bootstrap_very_delicate();
        vm = vm.bootstrap_semi_delicate();

        // Populate globals.
        vm.set_global("false", vm.false_);
        vm.set_global("nil", vm.nil);
        vm.set_global("true", vm.true_);
        let v = vm.system_cls;
        let v = Inst::new(&mut vm, v);
        vm.set_global("system", v);

        vm
    }

    fn bootstrap_very_delicate(mut self) -> Self {
        // The problem in this phase is that we are creating objects that have references to other
        // objects which are not yet created i.e. we end up with `Val::illegal`s lurking around.
        // All of these *must* be patched with references to the "true" objects before main
        // execution happens, or we will be in undefined behaviour (and, to be clear, this will be
        // the sort of UB you notice: segfaults etc.).

        self.obj_cls = self.init_builtin_class("Object", false);
        self.cls_cls = self.init_builtin_class("Class", false);
        self.nil_cls = self.init_builtin_class("Nil", true);
        let v = self.nil_cls;
        self.nil = Inst::new(&mut self, v);
        self.metacls_cls = self.init_builtin_class("Metaclass", false);

        // Patch incorrect references.
        let obj_cls = self.obj_cls;
        obj_cls
            .downcast::<Class>(&self)
            .unwrap()
            .set_supercls(&self, self.nil);
        obj_cls
            .get_class(&mut self)
            .downcast::<Class>(&self)
            .unwrap()
            .set_metacls(&self, self.metacls_cls);
        obj_cls
            .get_class(&mut self)
            .downcast::<Class>(&self)
            .unwrap()
            .set_supercls(&self, self.cls_cls);
        let cls_cls = self.cls_cls;
        cls_cls
            .get_class(&mut self)
            .downcast::<Class>(&self)
            .unwrap()
            .set_metacls(&self, self.metacls_cls);
        let nil_cls = self.nil_cls;
        nil_cls
            .get_class(&mut self)
            .downcast::<Class>(&self)
            .unwrap()
            .set_metacls(&self, self.metacls_cls);
        let metacls_cls = self.metacls_cls;
        metacls_cls
            .get_class(&mut self)
            .downcast::<Class>(&self)
            .unwrap()
            .set_metacls(&self, self.metacls_cls);

        self.str_cls = self.init_builtin_class("String", false);
        let str_cls = self.str_cls;
        self.sym_cls = self.init_builtin_class("Symbol", false);
        let sym_cls = self.sym_cls;
        for c in &[obj_cls, cls_cls, nil_cls, metacls_cls, str_cls, sym_cls] {
            let cls = c.downcast::<Class>(&self).unwrap();
            cls.bootstrap(&self);
            let metacls_val = c.get_class(&mut self);
            let metacls = metacls_val.downcast::<Class>(&self).unwrap();
            metacls.bootstrap(&self);
        }
        for s in &self.strings {
            s.downcast::<String_>(&self).unwrap().set_cls(str_cls);
        }

        self
    }

    fn bootstrap_semi_delicate(mut self) -> Self {
        // Nothing in this phase must store references to any classes earlier than it in the phase.
        assert!(self.symbols.is_empty());

        self.array_cls = self.init_builtin_class("Array", false);
        self.block_cls = self.init_builtin_class("Block", false);
        self.block1_cls = self.init_builtin_class("Block1", false);
        self.block2_cls = self.init_builtin_class("Block2", false);
        self.block3_cls = self.init_builtin_class("Block3", false);
        self.bool_cls = self.init_builtin_class("Boolean", false);
        self.double_cls = self.init_builtin_class("Double", false);
        self.false_cls = self.init_builtin_class("False", false);
        self.int_cls = self.init_builtin_class("Integer", false);
        self.method_cls = self.init_builtin_class("Method", false);
        self.system_cls = self.init_builtin_class("System", false);
        self.true_cls = self.init_builtin_class("True", false);
        let v = self.false_cls;
        self.false_ = Inst::new(&mut self, v);
        let v = self.system_cls;
        self.system = Inst::new(&mut self, v);
        let v = self.true_cls;
        self.true_ = Inst::new(&mut self, v);

        self
    }

    /// Load the class `name`. Note that this looks `name` up in the globals, so you can get a
    /// successful value back which isn't a class (e.g. `nil`, which is `Object`'s superclass).
    pub fn load_class(&mut self, name: &str) -> Result<Val, ()> {
        if let Some(i) = self.reverse_globals.get(name) {
            let v = self.globals[*i];
            if v.valkind() != ValKind::ILLEGAL {
                return Ok(v);
            }
        }
        if let Ok(p) = self.find_class_path(name) {
            let cls = self.compile(&p, true);
            self.set_global(name, cls);
            return Ok(cls);
        }
        Err(())
    }

    /// Compile the file at `path`. `inst_vars_allowed` should be set to `false` only for those
    /// builtin classes which do not lead to run-time instances of `Inst`.
    fn compile(&mut self, path: &Path, inst_vars_allowed: bool) -> Val {
        let (name, cls_val) = compile(self, path);
        let cls: Gc<Class> = cls_val.downcast(self).unwrap();
        if !inst_vars_allowed && cls.num_inst_vars > 0 {
            panic!("No instance vars allowed in {}", path.to_str().unwrap());
        }
        self.set_global(&name, cls_val);
        cls_val
    }

    fn find_class_path(&self, name: &str) -> Result<PathBuf, ()> {
        for dn in &self.classpath {
            let mut pb = PathBuf::new();
            pb.push(dn);
            pb.push(name);
            pb.set_extension(SOM_EXTENSION);
            if pb.is_file() {
                return Ok(pb);
            }
        }
        Err(())
    }

    /// Find and compile the builtin class 'name'.
    fn init_builtin_class(&mut self, name: &str, inst_vars_allowed: bool) -> Val {
        let path = self
            .find_class_path(name)
            .unwrap_or_else(|_| panic!("Can't find builtin class '{}'", name));

        let val = self.compile(&path, inst_vars_allowed);
        self.set_global(name, val);

        val
    }

    /// Inform the user of the error string `error` and then exit.
    pub fn error(&self, error: &str) -> ! {
        eprintln!("{}", error);
        process::exit(1);
    }

    /// Send the message `msg` to the receiver `rcv` with arguments `args`.
    pub fn top_level_send(
        &mut self,
        rcv: Val,
        msg: &str,
        args: Vec<Val>,
    ) -> Result<Val, Box<VMError>> {
        assert!(self.frames_len() == 0);
        let cls = rcv.get_class(self);
        let meth = cls.downcast::<Class>(self)?.get_method(self, msg)?;
        match meth.body {
            MethodBody::Primitive(_) => {
                panic!("Primitives can't be called outside of a function frame.");
            }
            MethodBody::User {
                num_vars,
                bytecode_off,
                max_stack,
            } => {
                if self.stack.remaining_capacity() < max_stack {
                    panic!("Not enough stack space to execute method.");
                }
                if args.len() != meth.num_params() {
                    panic!("Passed the wrong number of parameters.");
                }
                for a in args {
                    self.stack.push(a);
                }
                let frame = Frame::new(self, None, rcv, None, num_vars, meth.num_params());
                self.frames.push(frame);
                let r = self.exec_user(rcv, meth, bytecode_off);
                self.frame_pop();
                match r {
                    SendReturn::ClosureReturn(_) => unreachable!(),
                    SendReturn::Err(e) => Err(Box::new(*e)),
                    SendReturn::Val => Ok(self.stack.pop()),
                }
            }
        }
    }

    fn send_args_on_stack(&mut self, rcv: Val, method: Gc<Method>) -> SendReturn {
        match method.body {
            MethodBody::Primitive(p) => self.exec_primitive(p, rcv),
            MethodBody::User {
                num_vars,
                bytecode_off,
                max_stack,
            } => {
                if self.stack.remaining_capacity() < max_stack {
                    panic!("Not enough stack space to execute method.");
                }
                let nframe = Frame::new(self, None, rcv, None, num_vars, method.num_params());
                self.frames.push(nframe);
                let r = self.exec_user(rcv, method, bytecode_off);
                self.frame_pop();
                r
            }
        }
    }

    /// Execute a SOM method. Note that the frame for this method must have been created *before*
    /// calling this function.
    fn exec_user(&mut self, rcv: Val, method: Gc<Method>, meth_start_pc: usize) -> SendReturn {
        let mut pc = meth_start_pc;

        macro_rules! stry {
            ($elem:expr) => {{
                let e = $elem;
                match e {
                    Ok(o) => o,
                    Err(mut e) => {
                        e.backtrace.push((method, self.instr_spans[pc]));
                        return SendReturn::Err(e);
                    }
                }
            }};
        }

        // Inside this function, one should use this macro instead of calling `send_args_on_stack`
        // directly.
        macro_rules! send_args_on_stack {
            ($send_rcv:expr, $send_method:expr) => {{
                match self.send_args_on_stack($send_rcv, $send_method) {
                    SendReturn::ClosureReturn(d) => {
                        if d > 0 {
                            return SendReturn::ClosureReturn(d - 1);
                        }
                    }
                    SendReturn::Err(mut e) => {
                        e.backtrace.push((method, self.instr_spans[pc]));
                        return SendReturn::Err(e);
                    }
                    SendReturn::Val => (),
                }
            }};
        }

        let stack_start = self.stack.len();
        loop {
            let instr = {
                debug_assert!(pc < self.instrs.len());
                *unsafe { self.instrs.get_unchecked(pc) }
            };
            match instr {
                Instr::Array(num_items) => {
                    let items = self.stack.split_off(self.stack.len() - num_items);
                    let arr = NormalArray::from_vec(self, items);
                    self.stack.push(arr);
                    pc += 1;
                }
                Instr::Block(blkinfo_off) => {
                    let (num_params, bytecode_end) = {
                        let blkinfo = &self.blockinfos[blkinfo_off];
                        (blkinfo.num_params, blkinfo.bytecode_end)
                    };
                    let closure = self.current_frame().closure;
                    let v = Block::new(self, method, rcv, blkinfo_off, closure, num_params);
                    self.stack.push(v);
                    pc = bytecode_end;
                }
                Instr::ClosureReturn(closure_depth) => {
                    // We want to do a non-local return. Before we attempt that, we need to
                    // check that the block hasn't escaped its function (and we know we're in a
                    // block because only a block can attempt a non-local return).
                    // Fortunately, the `closure` pointer in a frame is a perfect proxy for
                    // determining this: if this frame's (i.e. block's!) parent closure is not
                    // consistent with the frame stack, then the block has escaped.
                    let v = self.stack.pop();
                    let parent_closure = self.current_frame().closure(closure_depth);
                    for (frame_depth, pframe) in self.frames.iter().rev().enumerate() {
                        if Gc::ptr_eq(&parent_closure, &pframe.closure) {
                            let sp = pframe.sp();
                            self.stack.truncate(sp);
                            self.stack.push(v);
                            return SendReturn::ClosureReturn(frame_depth);
                        }
                    }
                    let cls_val = rcv.get_class(self);
                    let cls: Gc<Class> = stry!(cls_val.downcast(self));
                    let meth = stry!(cls.get_method(self, "escapedBlock:"));
                    let blk = self.current_frame().block.unwrap();
                    self.stack.push(blk);
                    send_args_on_stack!(rcv, meth);
                    pc += 1;
                }
                Instr::Double(i) => {
                    let v = Double::new(self, i);
                    self.stack.push(v);
                    pc += 1;
                }
                Instr::GlobalLookup(i) => {
                    let v = self.globals[i];
                    if v.valkind() != ValKind::ILLEGAL {
                        // The global value is already set
                        self.stack.push(v);
                    } else {
                        // We have to call `self unknownGlobal:<symbol name>`.
                        let cls_val = rcv.get_class(self);
                        let cls: Gc<Class> = stry!(cls_val.downcast(self));
                        let meth = stry!(cls.get_method(self, "unknownGlobal:"));
                        let len = self.stack.len();
                        self.current_frame().set_sp(len);
                        let name = {
                            // XXX O(n) lookup!
                            self.reverse_globals
                                .iter()
                                .find(|(_, j)| **j == i)
                                .map(|(n, _)| n)
                                .unwrap()
                                .to_string()
                        };
                        let v = String_::new_sym(self, name);
                        self.stack.push(v);
                        send_args_on_stack!(rcv, meth);
                    }
                    pc += 1;
                }
                Instr::InstVarLookup(n) => {
                    let inst = stry!(rcv.tobj(self));
                    self.stack.push(unsafe { inst.unchecked_inst_var_get(n) });
                    pc += 1;
                }
                Instr::InstVarSet(n) => {
                    let inst = stry!(rcv.tobj(self));
                    unsafe { inst.unchecked_inst_var_set(n, self.stack.peek()) };
                    pc += 1;
                }
                Instr::Int(i) => {
                    let v = Val::from_isize(self, i);
                    self.stack.push(v);
                    pc += 1;
                }
                Instr::Pop => {
                    self.stack.pop();
                    pc += 1;
                }
                Instr::Return => {
                    return SendReturn::Val;
                }
                Instr::Send(send_idx, cache_idx) | Instr::SuperSend(send_idx, cache_idx) => {
                    let (send_rcv, nargs, meth) = {
                        debug_assert!(send_idx < self.sends.len());
                        let nargs = unsafe { self.sends.get_unchecked(send_idx) }.1;
                        let rcv = self.stack.pop_n(nargs);
                        let lookup_cls = match instr {
                            Instr::Send(_, _) => rcv.get_class(self),
                            Instr::SuperSend(_, _) => {
                                let method_cls_val = method.holder();
                                let method_cls: Gc<Class> = stry!(method_cls_val.downcast(self));
                                method_cls.supercls(self)
                            }
                            _ => unreachable!(),
                        };

                        let meth = match &self.inline_caches[cache_idx] {
                            Some((cache_cls, cache_meth)) if cache_cls.bit_eq(&lookup_cls) => {
                                *cache_meth
                            }
                            _ => {
                                // The inline cache is empty or out of date, so store a new value in it.
                                let name = unsafe { self.sends.get_unchecked(send_idx) }.0;
                                let cls: Gc<Class> = stry!(lookup_cls.downcast(self));
                                let meth = match cls.get_method(self, &*name) {
                                    Ok(m) => {
                                        self.inline_caches[cache_idx] = Some((lookup_cls, m));
                                        m
                                    }
                                    Err(box VMError {
                                        kind: VMErrorKind::UnknownMethod,
                                        ..
                                    }) => {
                                        let meth = cls
                                            .get_method(self, "doesNotUnderstand:arguments:")
                                            .unwrap();
                                        let items = self.stack.split_off(self.stack.len() - nargs);
                                        let arr = NormalArray::from_vec(self, items);
                                        let sig = String_::new_sym(self, (&*name).to_owned());
                                        self.stack.push(sig);
                                        self.stack.push(arr);
                                        send_args_on_stack!(rcv, meth);
                                        pc += 1;
                                        continue;
                                    }
                                    Err(e) => stry!(Err(e)),
                                };
                                meth
                            }
                        };
                        (rcv, nargs, meth)
                    };

                    if let MethodBody::Primitive(Primitive::Restart) = meth.body {
                        self.stack.truncate(stack_start);
                        pc = meth_start_pc;
                        continue;
                    }

                    let len = self.stack.len() - nargs;
                    self.current_frame().set_sp(len);
                    send_args_on_stack!(send_rcv, meth);
                    pc += 1;
                }
                Instr::String(string_off) => {
                    debug_assert!(self.strings.len() > string_off);
                    let s = *unsafe { self.strings.get_unchecked(string_off) };
                    self.stack.push(s);
                    pc += 1;
                }
                Instr::Symbol(symbol_off) => {
                    debug_assert!(self.symbols.len() > symbol_off);
                    let s = *unsafe { self.symbols.get_unchecked(symbol_off) };
                    self.stack.push(s);
                    pc += 1;
                }
                Instr::VarLookup(d, n) => {
                    let v = self.current_frame().var_lookup(d, n);
                    self.stack.push(v);
                    pc += 1;
                }
                Instr::VarSet(d, n) => {
                    let v = self.stack.peek();
                    self.current_frame().var_set(d, n, v);
                    pc += 1;
                }
            }
        }
    }

    fn exec_primitive(&mut self, prim: Primitive, rcv: Val) -> SendReturn {
        macro_rules! stry {
            ($elem:expr) => {{
                let e = $elem;
                match e {
                    Ok(o) => o,
                    Err(e) => return SendReturn::Err(e),
                }
            }};
        }

        match prim {
            Primitive::Add => {
                let v = self.stack.pop();
                let v = stry!(rcv.add(self, v));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::And => {
                let v = self.stack.pop();
                let v = stry!(rcv.and(self, v));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::AsInteger => {
                let dbl = stry!(rcv.downcast::<Double>(self));
                let v = dbl.as_integer(self);
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::AsString => {
                let v = stry!(rcv.to_strval(self));
                let str_maybe: Gc<String_> = stry!(v.downcast(self));
                let str_ = stry!(str_maybe.to_string_(self));
                self.stack.push(str_);
                SendReturn::Val
            }
            Primitive::AsSymbol => {
                let v = stry!(stry!(rcv.downcast::<String_>(self)).to_symbol(self));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::As32BitSignedValue => {
                let i = if let Some(i) = rcv.as_isize(self) {
                    i as i32 as isize
                } else {
                    rcv.downcast::<ArbInt>(self)
                        .unwrap()
                        .bigint()
                        .to_u32_digits()
                        .1[0] as i32 as isize
                };
                let v = Val::from_isize(self, i as isize);
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::As32BitUnsignedValue => {
                let i = if let Some(i) = rcv.as_isize(self) {
                    i as u32
                } else {
                    rcv.downcast::<ArbInt>(self)
                        .unwrap()
                        .bigint()
                        .to_u32_digits()
                        .1[0] as u32
                };
                let v = Val::from_isize(self, i as isize);
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::At => {
                let rcv_tobj = stry!(rcv.tobj(self));
                let arr = stry!(rcv_tobj.to_array());
                let idx = stry!(self.stack.pop().as_usize(self));
                let v = stry!(arr.at(self, idx));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::AtPut => {
                let rcv_tobj = stry!(rcv.tobj(self));
                let arr = stry!(rcv_tobj.to_array());
                let v = self.stack.pop();
                let idx = stry!(self.stack.pop().as_usize(self));
                stry!(arr.at_put(self, idx, v));
                self.stack.push(rcv);
                SendReturn::Val
            }
            Primitive::AtRandom => todo!(),
            Primitive::BitXor => {
                let v = self.stack.pop();
                let v = stry!(rcv.xor(self, v));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Class => {
                let v = rcv.get_class(self);
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Concatenate => {
                let rhs = self.stack.pop();
                let v = stry!(stry!(rcv.downcast::<String_>(self)).concatenate(self, rhs));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Cos => {
                let dbl = rcv.downcast::<Double>(self).unwrap();
                let v = dbl.cos(self);
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Div => {
                let v = self.stack.pop();
                let v = stry!(rcv.div(self, v));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::DoubleDiv => {
                let v = self.stack.pop();
                let v = stry!(rcv.double_div(self, v));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Equals => {
                let v = self.stack.pop();
                let v = stry!(rcv.equals(self, v));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Exit => {
                let c_val = self.stack.pop();
                // We now have to undertake a slightly awkward dance: unknown to the user,
                // integers are unboxed, boxed, or big ints. Just because we can't convert the
                // value to an isize doesn't mean that the user hasn't handed us an integer: we
                // have to craft a special error message below to capture this.
                if let Some(c) = c_val.as_isize(self) {
                    if let Ok(c) = i32::try_from(c) {
                        return SendReturn::Err(VMError::new(self, VMErrorKind::Exit(c)));
                    }
                }
                if c_val.get_class(self) == self.int_cls {
                    SendReturn::Err(VMError::new(self, VMErrorKind::DomainError))
                } else {
                    let expected = Int::static_objtype();
                    let got = c_val.dyn_objtype(self);
                    SendReturn::Err(VMError::new(
                        self,
                        VMErrorKind::BuiltinTypeError { expected, got },
                    ))
                }
            }
            Primitive::Fields => {
                let fields = stry!(rcv.downcast::<Class>(self)).fields(self);
                self.stack.push(fields);
                SendReturn::Val
            }
            Primitive::FromString => {
                let str_ = stry!(self.stack.pop().downcast::<String_>(self));
                let s = str_.as_str();
                let v = match s.parse::<isize>() {
                    Ok(i) => Val::from_isize(self, i),
                    Err(_) => match BigInt::from_str(s) {
                        Ok(i) => ArbInt::new(self, i),
                        Err(_) => {
                            return SendReturn::Err(VMError::new(
                                self,
                                VMErrorKind::InvalidInteger(s.to_owned()),
                            ))
                        }
                    },
                };
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::FullGC => {
                self.stack.push(self.true_);
                SendReturn::Val
            }
            Primitive::Global => {
                let name_val = self.stack.pop();
                let name = stry!(String_::symbol_to_string_(self, name_val));
                let g = self.get_global_or_nil(name.as_str());
                self.stack.push(g);
                SendReturn::Val
            }
            Primitive::GlobalPut => {
                let v = self.stack.pop();
                let name_val = self.stack.pop();
                let name = stry!(String_::symbol_to_string_(self, name_val));
                self.set_global(name.as_str(), v);
                self.stack.push(rcv);
                SendReturn::Val
            }
            Primitive::GreaterThan => {
                let v = self.stack.pop();
                let v = stry!(rcv.greater_than(self, v));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::GreaterThanEquals => {
                let v = self.stack.pop();
                let v = stry!(rcv.greater_than_equals(self, v));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Halt => unimplemented!(),
            Primitive::HasGlobal => todo!(),
            Primitive::Hashcode => {
                let hc = rcv.hashcode(self);
                self.stack.push(hc);
                SendReturn::Val
            }
            Primitive::Holder => {
                let meth = stry!(rcv.downcast::<Method>(self));
                let cls = meth.holder();
                self.stack.push(cls);
                SendReturn::Val
            }
            Primitive::Inspect => unimplemented!(),
            Primitive::InstVarAt => {
                let n = stry!(self.stack.pop().as_usize(self));
                let inst = stry!(rcv.tobj(self));
                let v = stry!(inst.inst_var_at(self, n));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::InstVarAtPut => {
                let v = self.stack.pop();
                let n = stry!(self.stack.pop().as_usize(self));
                let inst = stry!(rcv.tobj(self));
                stry!(inst.inst_var_at_put(self, n, v));
                self.stack.push(rcv);
                SendReturn::Val
            }
            Primitive::InstVarNamed => unimplemented!(),
            Primitive::InvokeOnWith => todo!(),
            Primitive::IsDigits => {
                stry!(self.str_is(rcv, |x| x.is_ascii_digit()));
                SendReturn::Val
            }
            Primitive::IsLetters => {
                stry!(self.str_is(rcv, |x| x.is_alphabetic()));
                SendReturn::Val
            }
            Primitive::IsWhiteSpace => {
                stry!(self.str_is(rcv, |x| x.is_whitespace()));
                SendReturn::Val
            }
            Primitive::Length => {
                // Only Arrays and Strings can have this primitive installed.
                debug_assert!(rcv.valkind() == ValKind::GCBOX);
                let tobj = rcv.tobj(self).unwrap();
                let v = Val::from_usize(self, tobj.length());
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::LessThan => {
                let v = self.stack.pop();
                let v = stry!(rcv.less_than(self, v));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::LessThanEquals => {
                let v = self.stack.pop();
                let v = stry!(rcv.less_than_equals(self, v));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Load => {
                let name_val = self.stack.pop();
                let name = stry!(String_::symbol_to_string_(self, name_val));
                match self.load_class(name.as_str()) {
                    Ok(cls) => {
                        self.stack.push(cls);
                    }
                    Err(()) => {
                        let v = self.nil;
                        self.stack.push(v);
                    }
                }
                SendReturn::Val
            }
            Primitive::Methods => {
                let methods = stry!(rcv.downcast::<Class>(self)).methods(self);
                self.stack.push(methods);
                SendReturn::Val
            }
            Primitive::Mod => {
                let v = self.stack.pop();
                let v = stry!(rcv.modulus(self, v));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Mul => {
                let v = self.stack.pop();
                let v = stry!(rcv.mul(self, v));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Name => {
                let v = stry!(stry!(rcv.downcast::<Class>(self)).name(self));
                let str_: Gc<String_> = stry!(v.downcast(self));
                let sym = stry!(str_.to_symbol(self));
                self.stack.push(sym);
                SendReturn::Val
            }
            Primitive::New => {
                let v = Inst::new(self, rcv);
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::NewArray => {
                let len = stry!(self.stack.pop().as_usize(self));
                let v = NormalArray::new(self, len);
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::NotEquals => {
                let v = self.stack.pop();
                let v = stry!(rcv.not_equals(self, v));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::ObjectSize => unimplemented!(),
            Primitive::Perform => {
                let args_val = NormalArray::new(self, 0);
                let sig_val = self.stack.pop();
                let cls_val = rcv.get_class(self);
                self.perform(rcv, cls_val, sig_val, args_val)
            }
            Primitive::PerformInSuperClass => {
                let args_val = NormalArray::new(self, 0);
                let cls_val = self.stack.pop();
                let sig_val = self.stack.pop();
                self.perform(rcv, cls_val, sig_val, args_val)
            }
            Primitive::PerformWithArguments => {
                let args_val = self.stack.pop();
                let sig_val = self.stack.pop();
                let cls_val = rcv.get_class(self);
                self.perform(rcv, cls_val, sig_val, args_val)
            }
            Primitive::PerformWithArgumentsInSuperClass => {
                let cls_val = self.stack.pop();
                let args_val = self.stack.pop();
                let sig_val = self.stack.pop();
                self.perform(rcv, cls_val, sig_val, args_val)
            }
            Primitive::PositiveInfinity => {
                let dbl = Double::new(self, f64::INFINITY);
                self.stack.push(dbl);
                SendReturn::Val
            }
            Primitive::PrimSubstringFromTo => {
                let end = stry!(self.stack.pop().as_usize(self));
                let start = stry!(self.stack.pop().as_usize(self));
                let str_: Gc<String_> = stry!(rcv.downcast(self));
                let substr = stry!(str_.substring(self, start, end));
                self.stack.push(substr);
                SendReturn::Val
            }
            Primitive::RefEquals => {
                let v = self.stack.pop();
                let v = stry!(rcv.ref_equals(self, v));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Restart => unreachable!(),
            Primitive::PrintNewline => {
                println!();
                let v = self.system;
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::PrintString => {
                let v = self.stack.pop();
                let str_: Gc<String_> = stry!(v.downcast(self));
                print!("{}", str_.as_str());
                let v = self.system;
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Rem => {
                let v = self.stack.pop();
                let v = stry!(rcv.remainder(self, v));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Round => {
                let dbl = rcv.downcast::<Double>(self).unwrap();
                let v = dbl.round(self);
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Shl => {
                let v = self.stack.pop();
                let v = stry!(rcv.shl(self, v));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Shr => {
                let v = self.stack.pop();
                let v = stry!(rcv.shr(self, v));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Signature => {
                let meth = rcv.downcast::<Method>(self).unwrap();
                self.stack.push(meth.sig(self));
                SendReturn::Val
            }
            Primitive::Sin => {
                let dbl = rcv.downcast::<Double>(self).unwrap();
                let v = dbl.sin(self);
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Sqrt => {
                let v = stry!(rcv.sqrt(self));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Sub => {
                let v = self.stack.pop();
                let v = stry!(rcv.sub(self, v));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Superclass => {
                let cls: Gc<Class> = stry!(rcv.downcast(self));
                let v = cls.supercls(self);
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Ticks => {
                match SystemTime::now().duration_since(UNIX_EPOCH) {
                    Ok(d) => {
                        let t = d.as_micros();
                        const_assert!(size_of::<usize>() <= size_of::<u128>());
                        if t > usize::max_value() as u128 {
                            todo!();
                        } else {
                            let v = Val::from_usize(self, t as usize);
                            self.stack.push(v);
                        }
                    }
                    Err(_) => todo!(),
                }
                SendReturn::Val
            }
            Primitive::Time => todo!(),
            Primitive::Value(nargs) => {
                let rcv_blk: Gc<Block> = stry!(rcv.downcast(self));
                let (num_vars, bytecode_off, max_stack) = {
                    let blkinfo = &self.blockinfos[rcv_blk.blockinfo_off];
                    (blkinfo.num_vars, blkinfo.bytecode_off, blkinfo.max_stack)
                };
                if self.stack.remaining_capacity() < max_stack {
                    panic!("Not enough stack space to execute block.");
                }
                let frame = Frame::new(
                    self,
                    Some(rcv),
                    rcv,
                    Some(rcv_blk.parent_closure),
                    num_vars,
                    nargs as usize,
                );
                self.frames.push(frame);
                let r = self.exec_user(rcv_blk.inst, rcv_blk.method, bytecode_off);
                self.frame_pop();
                r
            }
        }
    }

    fn perform(&mut self, rcv: Val, cls_val: Val, sig_val: Val, args_val: Val) -> SendReturn {
        macro_rules! stry {
            ($elem:expr) => {{
                let e = $elem;
                match e {
                    Ok(o) => o,
                    Err(e) => return SendReturn::Err(e),
                }
            }};
        }

        let args_tobj = stry!(args_val.tobj(self));
        let args = stry!(args_tobj.to_array());
        let sig = stry!(String_::symbol_to_string_(self, sig_val));
        let cls = stry!(cls_val.downcast::<Class>(self));
        match cls.get_method(self, sig.as_str()) {
            Ok(m) => {
                if args_tobj.length() != m.num_params() {
                    return SendReturn::Err(VMError::new(
                        self,
                        VMErrorKind::WrongNumberOfArgs {
                            wanted: m.num_params(),
                            got: args_tobj.length(),
                        },
                    ));
                }
                for v in args.iter() {
                    self.stack.push(v);
                }
                self.send_args_on_stack(rcv, m)
            }
            Err(box VMError {
                kind: VMErrorKind::UnknownMethod,
                ..
            }) => {
                let meth = cls
                    .get_method(self, "doesNotUnderstand:arguments:")
                    .unwrap();
                self.stack.push(sig_val);
                let arr = NormalArray::new(self, 0);
                self.stack.push(arr);
                self.send_args_on_stack(rcv, meth)
            }
            Err(e) => return SendReturn::Err(e),
        }
    }

    /// Does every character in the SOM string in `rcv` satisfy the condition `f`? Pushes true/false onto the SOM
    /// stack. Note that empty strings are considered not to satisfy the condition by definition.
    pub fn str_is<F>(&mut self, rcv: Val, f: F) -> Result<(), Box<VMError>>
    where
        F: Fn(char) -> bool,
    {
        let str_val = rcv.downcast::<String_>(self)?;
        let str_ = str_val.as_str();
        if !str_.is_empty() && str_.chars().all(f) {
            self.stack.push(self.true_);
        } else {
            self.stack.push(self.false_);
        }
        Ok(())
    }

    fn current_frame(&mut self) -> &mut Frame {
        debug_assert!(!self.frames.is_empty());
        let frames_len = self.frames.len();
        unsafe { self.frames.get_unchecked_mut(frames_len - 1) }
    }

    fn frame_pop(&mut self) {
        self.frames.pop();
    }

    pub fn frames_len(&self) -> usize {
        self.frames.len()
    }

    /// Add `blkinfo` to the set of known `BlockInfo`s and return its index.
    pub fn push_blockinfo(&mut self, blkinfo: BlockInfo) -> usize {
        let len = self.blockinfos.len();
        self.blockinfos.push(blkinfo);
        len
    }

    /// Update the `BlockInfo` at index `idx` to `blkinfo`.
    pub fn set_blockinfo(&mut self, idx: usize, blkinfo: BlockInfo) {
        self.blockinfos[idx] = blkinfo;
    }

    pub fn flush_inline_caches(&mut self) {
        for c in &mut self.inline_caches {
            *c = None;
        }
    }

    /// Add an empty inline cache to the VM, returning its index.
    pub fn new_inline_cache(&mut self) -> usize {
        let len = self.inline_caches.len();
        self.inline_caches.push(None);
        len
    }

    /// Lookup the method `name` in the class `rcv_cls`, utilising the inline cache at index `idx`.
    pub fn inline_cache_lookup(
        &mut self,
        idx: usize,
        rcv_cls: Val,
        name: &str,
    ) -> Result<Gc<Method>, Box<VMError>> {
        // Lookup the method in the inline cache.
        {
            if let Some((cache_cls, cache_meth)) = &self.inline_caches[idx] {
                if cache_cls.bit_eq(&rcv_cls) {
                    return Ok(*cache_meth);
                }
            }
        }
        // The inline cache is empty or out of date, so store a new value in it.
        let meth = rcv_cls.downcast::<Class>(self)?.get_method(self, &name)?;
        self.inline_caches[idx] = Some((rcv_cls, meth));
        Ok(meth)
    }

    /// How many instructions are currently present in the VM?
    pub fn instrs_len(&self) -> usize {
        self.instrs.len()
    }

    /// Push `instr` to the end of the current vector of instructions, associating `span` with it
    /// for the purposes of backtraces.
    pub fn instrs_push(&mut self, instr: Instr, span: Span) {
        debug_assert_eq!(self.instrs.len(), self.instr_spans.len());
        self.instrs.push(instr);
        self.instr_spans.push(span);
    }

    /// Add the send `send` to the VM, returning its index. Note that sends are reused, so indexes
    /// are also reused.
    pub fn add_send(&mut self, send: (String, usize)) -> usize {
        // We want to avoid `clone`ing `send` in the (hopefully common) case of a cache hit, hence
        // this slightly laborious dance and double-lookup.
        let send = (Gc::new(send.0), send.1);
        if let Some(i) = self.reverse_sends.get(&send) {
            *i
        } else {
            let len = self.sends.len();
            self.reverse_sends.insert(send.clone(), len);
            self.sends.push(send);
            len
        }
    }

    /// Add the string `s` to the VM, returning its index. Note that strings are reused, so indexes
    /// are also reused.
    pub fn add_string(&mut self, s: String) -> usize {
        // We want to avoid `clone`ing `s` in the (hopefully common) case of a cache hit, hence
        // this slightly laborious dance and double-lookup.
        if let Some(i) = self.reverse_strings.get(&s) {
            *i
        } else {
            let len = self.strings.len();
            self.reverse_strings.insert(s.clone(), len);
            let v = String_::new_str(self, s);
            self.strings.push(v);
            len
        }
    }

    /// Add the symbol `s` to the VM, returning its index. Note that symbols are reused, so indexes
    /// are also reused.
    pub fn add_symbol(&mut self, s: String) -> usize {
        // We want to avoid `clone`ing `s` in the (hopefully common) case of a cache hit, hence
        // this slightly laborious dance and double-lookup.
        if let Some(i) = self.reverse_symbols.get(&s) {
            *i
        } else {
            let len = self.symbols.len();
            self.reverse_symbols.insert(s.clone(), len);
            let v = String_::new_sym(self, s);
            self.symbols.push(v);
            len
        }
    }

    /// Add the global `n` to the VM, returning its index. Note that global names (like strings)
    /// are reused, so indexes are also reused.
    pub fn add_global(&mut self, s: &str) -> usize {
        if let Some(i) = self.reverse_globals.get(s) {
            *i
        } else {
            let len = self.globals.len();
            self.reverse_globals.insert(s.to_owned(), len);
            self.globals.push(Val::illegal());
            len
        }
    }

    /// Lookup the global `name`: if it has not been added, or has been added but not set, then
    /// `self.nil` will be returned.
    pub fn get_global_or_nil(&self, name: &str) -> Val {
        if let Some(i) = self.reverse_globals.get(name) {
            let v = self.globals[*i];
            if v.valkind() != ValKind::ILLEGAL {
                return v;
            }
        }
        self.nil
    }

    /// Get the global at position `i`: if it has not been set (i.e. is `ValKind::ILLEGAL`) this
    /// will return `Err(...)`.
    pub fn get_legal_global(&self, i: usize) -> Result<Val, Box<VMError>> {
        let v = self.globals[i];
        if v.valkind() != ValKind::ILLEGAL {
            return Ok(v);
        }
        Err(VMError::new(
            self,
            VMErrorKind::UnknownGlobal(
                self.reverse_globals
                    .iter()
                    .find(|(_, j)| **j == i)
                    .map(|(n, _)| n)
                    .unwrap()
                    .clone(),
            ),
        ))
    }

    /// Set the global `name` to the value `v`, overwriting the previous value (if any).
    pub fn set_global(&mut self, name: &str, v: Val) {
        debug_assert_eq!(self.globals.len(), self.reverse_globals.len());
        // We want to avoid `clone`ing `s` in the (hopefully common) case of a cache hit, hence
        // this slightly laborious dance and double-lookup.
        if let Some(i) = self.reverse_globals.get(name) {
            self.globals[*i] = v;
        } else {
            self.reverse_globals
                .insert(name.to_owned(), self.globals.len());
            self.globals.push(v);
        }
    }
}

#[derive(Debug)]
pub struct Frame {
    /// Stack pointer. Note that this is updated lazily (i.e. it might not be accurate at all
    /// points, but it is guaranteed to be correct over function calls).
    sp: usize,
    block: Option<Val>,
    closure: Gc<Closure>,
}

impl Frame {
    fn new(
        vm: &mut VM,
        block: Option<Val>,
        self_val: Val,
        parent_closure: Option<Gc<Closure>>,
        num_vars: usize,
        num_args: usize,
    ) -> Self {
        let mut vars = Vec::with_capacity(num_vars);
        vars.resize_with(num_vars, Val::illegal);

        if block.is_none() {
            vars[0] = self_val;
            for i in 0..num_args {
                vars[num_args - i] = vm.stack.pop();
            }
            for v in vars.iter_mut().skip(num_args + 1).take(num_vars) {
                *v = vm.nil;
            }
        } else {
            for i in 0..num_args {
                vars[num_args - i - 1] = vm.stack.pop();
            }
            for v in vars.iter_mut().skip(num_args).take(num_vars) {
                *v = vm.nil;
            }
        }

        Frame {
            sp: 0,
            block,
            closure: Gc::new(Closure::new(parent_closure, vars)),
        }
    }

    fn var_lookup(&self, depth: usize, var: usize) -> Val {
        self.closure(depth).get_var(var)
    }

    fn var_set(&mut self, depth: usize, var: usize, val: Val) {
        self.closure(depth).set_var(var, val);
    }

    /// Return the closure `depth` closures up from this frame's closure (where `depth` can be 0
    /// which returns this frame's closure).
    fn closure(&self, mut depth: usize) -> Gc<Closure> {
        let mut c = self.closure;
        while depth > 0 {
            c = *c.parent.as_ref().unwrap();
            depth -= 1;
        }
        c
    }

    /// Return this frame's stack pointer.
    fn sp(&self) -> usize {
        self.sp
    }

    /// Set this frame's stack pointer to `sp`.
    fn set_sp(&mut self, sp: usize) {
        self.sp = sp;
    }
}

#[derive(Debug)]
pub struct Closure {
    parent: Option<Gc<Closure>>,
    vars: Gc<Vars>,
}

#[derive(Debug)]
struct Vars(UnsafeCell<Vec<Val>>);

impl Closure {
    fn new(parent: Option<Gc<Closure>>, vars: Vec<Val>) -> Closure {
        Closure {
            parent,
            vars: Gc::new(Vars(UnsafeCell::new(vars))),
        }
    }

    fn get_var(&self, var: usize) -> Val {
        *unsafe { (&*self.vars.0.get()).get_unchecked(var) }
    }

    fn set_var(&self, var: usize, val: Val) {
        let raw = self.vars.0.get();
        unsafe { *(&mut *raw).get_unchecked_mut(var) = val };
    }
}

#[cfg(test)]
impl VM {
    pub fn new_no_bootstrap() -> Self {
        VM {
            classpath: vec![],
            array_cls: Val::illegal(),
            block_cls: Val::illegal(),
            block1_cls: Val::illegal(),
            block2_cls: Val::illegal(),
            block3_cls: Val::illegal(),
            bool_cls: Val::illegal(),
            cls_cls: Val::illegal(),
            double_cls: Val::illegal(),
            false_cls: Val::illegal(),
            int_cls: Val::illegal(),
            metacls_cls: Val::illegal(),
            method_cls: Val::illegal(),
            nil_cls: Val::illegal(),
            obj_cls: Val::illegal(),
            str_cls: Val::illegal(),
            sym_cls: Val::illegal(),
            system_cls: Val::illegal(),
            true_cls: Val::illegal(),
            false_: Val::illegal(),
            nil: Val::illegal(),
            system: Val::illegal(),
            true_: Val::illegal(),
            blockinfos: Vec::new(),
            globals: Vec::new(),
            reverse_globals: HashMap::new(),
            inline_caches: Vec::new(),
            instrs: Vec::new(),
            instr_spans: Vec::new(),
            sends: Vec::new(),
            reverse_sends: HashMap::new(),
            stack: SOMStack::new(),
            strings: Vec::new(),
            reverse_strings: HashMap::new(),
            symbols: Vec::new(),
            reverse_symbols: HashMap::new(),
            frames: Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serial_test::serial;

    #[test]
    #[serial]
    fn test_frame() {
        let mut vm = VM::new_no_bootstrap();
        let selfv = Val::from_isize(&mut vm, 42);
        let v = Val::from_isize(&mut vm, 43);
        vm.stack.push(v);
        let v = Val::from_isize(&mut vm, 44);
        vm.stack.push(v);
        let f = Frame::new(&mut vm, None, selfv, None, 3, 2);
        assert_eq!(f.var_lookup(0, 0).as_isize(&mut vm).unwrap(), 42);
        assert_eq!(f.var_lookup(0, 1).as_isize(&mut vm).unwrap(), 43);
        assert_eq!(f.var_lookup(0, 2).as_isize(&mut vm).unwrap(), 44);
    }
}
