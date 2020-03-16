//! The core part of the interpreter.

use std::{
    cell::UnsafeCell,
    collections::HashMap,
    convert::TryFrom,
    path::{Path, PathBuf},
    process,
    rc::Rc,
};

use abgc::{Gc, GcLayout};
use lrpar::Span;

use crate::{
    compiler::{
        compile,
        instrs::{Instr, Primitive},
    },
    vm::{
        error::{VMError, VMErrorKind},
        objects::{
            Block, BlockInfo, Class, Double, Inst, Int, Method, MethodBody, StaticObjType, String_,
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
    classpath: Vec<String>,
    pub block_cls: Val,
    pub block2_cls: Val,
    pub block3_cls: Val,
    pub bool_cls: Val,
    pub cls_cls: Val,
    pub double_cls: Val,
    pub false_cls: Val,
    pub int_cls: Val,
    pub metacls_cls: Val,
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
    sends: Vec<(Rc<String>, usize)>,
    /// reverse_sends is an optimisation allowing us to reuse sends: it maps a send `(String,
    /// usize)` to a `usize` where the latter represents the index of the send in `sends`.
    reverse_sends: HashMap<(Rc<String>, usize), usize>,
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
    pub fn new(classpath: Vec<String>) -> Self {
        // The bootstrapping phase is delicate: we need to bootstrap the Object, Class, and Nil
        // classes before we can create basic objects like nil. We thus perform bootstrapping in
        // two phases: the "very delicate" phase (with very strict rules on what is possible)
        // followed by the "slightly delicate phase" (with looser, but still fairly strict, rules
        // on what is possible).

        let mut vm = VM {
            classpath,
            block_cls: Val::illegal(),
            bool_cls: Val::illegal(),
            block2_cls: Val::illegal(),
            block3_cls: Val::illegal(),
            cls_cls: Val::illegal(),
            double_cls: Val::illegal(),
            false_cls: Val::illegal(),
            int_cls: Val::illegal(),
            metacls_cls: Val::illegal(),
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
        };
        // The very delicate phase.
        //
        // The problem in this phase is that we are creating objects that have references to other
        // objects which are not yet created i.e. we end up with `Val::illegal`s lurking around.
        // All of these *must* be patched with references to the "true" objects before main
        // execution happens, or we will be in undefined behaviour (and, to be clear, this will be
        // the sort of UB you notice: segfaults etc.).
        vm.obj_cls = vm.init_builtin_class("Object", false);
        vm.cls_cls = vm.init_builtin_class("Class", false);
        vm.nil_cls = vm.init_builtin_class("Nil", true);
        let v = vm.nil_cls.clone();
        vm.nil = Inst::new(&mut vm, v);
        vm.metacls_cls = vm.init_builtin_class("Metaclass", false);
        {
            // Patch incorrect references.
            let obj_cls = vm.obj_cls.clone();
            obj_cls
                .downcast::<Class>(&vm)
                .unwrap()
                .set_supercls(&vm, vm.nil.clone());
            obj_cls
                .get_class(&mut vm)
                .downcast::<Class>(&vm)
                .unwrap()
                .set_metacls(&vm, vm.metacls_cls.clone());
            obj_cls
                .get_class(&mut vm)
                .downcast::<Class>(&vm)
                .unwrap()
                .set_supercls(&vm, vm.cls_cls.clone());
            let cls_cls = vm.cls_cls.clone();
            cls_cls
                .get_class(&mut vm)
                .downcast::<Class>(&vm)
                .unwrap()
                .set_metacls(&vm, vm.metacls_cls.clone());
            let nil_cls = vm.nil_cls.clone();
            nil_cls
                .get_class(&mut vm)
                .downcast::<Class>(&vm)
                .unwrap()
                .set_metacls(&vm, vm.metacls_cls.clone());
            let metacls_cls = vm.metacls_cls.clone();
            metacls_cls
                .get_class(&mut vm)
                .downcast::<Class>(&vm)
                .unwrap()
                .set_metacls(&vm, vm.metacls_cls.clone());
        }

        // The slightly delicate phase.
        //
        // Nothing in this phase must store references to any classes earlier than it in the phase.
        vm.block_cls = vm.init_builtin_class("Block", false);
        vm.block2_cls = vm.init_builtin_class("Block2", false);
        vm.block3_cls = vm.init_builtin_class("Block3", false);
        vm.bool_cls = vm.init_builtin_class("Boolean", false);
        vm.double_cls = vm.init_builtin_class("Double", false);
        vm.false_cls = vm.init_builtin_class("False", false);
        vm.int_cls = vm.init_builtin_class("Integer", false);
        vm.str_cls = vm.init_builtin_class("String", false);
        vm.sym_cls = vm.init_builtin_class("Symbol", false);
        vm.system_cls = vm.init_builtin_class("System", false);
        vm.true_cls = vm.init_builtin_class("True", false);
        let v = vm.false_cls.clone();
        vm.false_ = Inst::new(&mut vm, v);
        let v = vm.system_cls.clone();
        vm.system = Inst::new(&mut vm, v);
        let v = vm.true_cls.clone();
        vm.true_ = Inst::new(&mut vm, v);

        // Populate globals.
        vm.set_global("false", vm.false_.clone());
        vm.set_global("nil", vm.nil.clone());
        vm.set_global("true", vm.true_.clone());
        let v = vm.system_cls.clone();
        let v = Inst::new(&mut vm, v);
        vm.set_global("system", v);

        vm
    }

    /// Compile the file at `path`. `inst_vars_allowed` should be set to `false` only for those
    /// builtin classes which do not lead to run-time instances of `Inst`.
    pub fn compile(&mut self, path: &Path, inst_vars_allowed: bool) -> Val {
        let (name, cls_val) = compile(self, path);
        let cls: &Class = cls_val.downcast(self).unwrap();
        if !inst_vars_allowed && cls.num_inst_vars > 0 {
            panic!("No instance vars allowed in {}", path.to_str().unwrap());
        }
        self.set_global(&name, cls_val.clone());
        cls_val
    }

    fn find_class(&self, name: &str) -> Result<PathBuf, ()> {
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
            .find_class(name)
            .unwrap_or_else(|_| panic!("Can't find builtin class '{}'", name));

        let val = self.compile(&path, inst_vars_allowed);
        self.set_global(name, val.clone());

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
                let nargs = args.len();
                for a in args {
                    self.stack.push(a);
                }
                let frame = Frame::new(self, true, rcv.clone(), None, num_vars, nargs);
                self.frames.push(frame);
                let r = self.exec_user(rcv, Gc::clone(&meth), bytecode_off);
                self.frame_pop();
                match r {
                    SendReturn::ClosureReturn(_) => unreachable!(),
                    SendReturn::Err(e) => Err(Box::new(*e)),
                    SendReturn::Val => Ok(self.stack.pop()),
                }
            }
        }
    }

    /// This function should only be called via the `send_args_on_stack!` macro.
    fn send_args_on_stack(&mut self, rcv: Val, method: Gc<Method>, nargs: usize) -> SendReturn {
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
                let nframe = Frame::new(self, true, rcv.clone(), None, num_vars, nargs);
                self.frames.push(nframe);
                let r = self.exec_user(rcv, Gc::clone(&method), bytecode_off);
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
                        e.backtrace.push((Gc::clone(&method), self.instr_spans[pc]));
                        return SendReturn::Err(e);
                    }
                }
            }};
        }

        macro_rules! send_args_on_stack {
            ($send_rcv:expr, $send_method:expr, $nargs:expr) => {{
                match self.send_args_on_stack($send_rcv, $send_method, $nargs) {
                    SendReturn::ClosureReturn(d) => {
                        if d > 0 {
                            return SendReturn::ClosureReturn(d - 1);
                        }
                    }
                    SendReturn::Err(mut e) => {
                        e.backtrace.push((Gc::clone(&method), self.instr_spans[pc]));
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
                Instr::Block(blkinfo_off) => {
                    let (num_params, bytecode_end) = {
                        let blkinfo = &self.blockinfos[blkinfo_off];
                        (blkinfo.num_params, blkinfo.bytecode_end)
                    };
                    let closure = Gc::clone(&self.current_frame().closure);
                    let v = Block::new(
                        self,
                        Gc::clone(&method),
                        rcv.clone(),
                        blkinfo_off,
                        closure,
                        num_params,
                    );
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
                    panic!("Return from escaped block");
                }
                Instr::Double(i) => {
                    let v = Double::new(self, i);
                    self.stack.push(v);
                    pc += 1;
                }
                Instr::GlobalLookup(i) => {
                    let v = &self.globals[i];
                    if v.valkind() != ValKind::ILLEGAL {
                        // The global value is already set
                        self.stack.push(v.clone());
                    } else {
                        // We have to call `self unknownGlobal:<symbol name>`.
                        let cls_val = rcv.get_class(self);
                        let cls: &Class = stry!(cls_val.downcast(self));
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
                                .clone()
                        };
                        let v = String_::new(self, name, false);
                        self.stack.push(v);
                        send_args_on_stack!(rcv.clone(), meth, 1);
                    }
                    pc += 1;
                }
                Instr::InstVarLookup(n) => {
                    let inst = stry!(rcv.tobj(self));
                    self.stack.push(inst.inst_var_lookup(n));
                    pc += 1;
                }
                Instr::InstVarSet(n) => {
                    let inst = stry!(rcv.tobj(self));
                    inst.inst_var_set(n, self.stack.peek());
                    pc += 1;
                }
                Instr::Int(i) => {
                    // from_isize(i) cannot fail so the unwrap() is safe.
                    let v = Val::from_isize(self, i).unwrap();
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
                Instr::Send(send_idx, cache_idx) => {
                    let (send_rcv, nargs, meth) = {
                        debug_assert!(send_idx < self.sends.len());
                        let nargs = unsafe { self.sends.get_unchecked(send_idx) }.1;
                        let rcv = self.stack.pop_n(nargs);
                        let rcv_cls = rcv.get_class(self);

                        let meth = match &self.inline_caches[cache_idx] {
                            Some((cache_cls, cache_meth)) if cache_cls.bit_eq(&rcv_cls) => {
                                Gc::clone(cache_meth)
                            }
                            _ => {
                                // The inline cache is empty or out of date, so store a new value in it.
                                let cls: &Class = stry!(rcv_cls.downcast(self));
                                let name =
                                    Rc::clone(&unsafe { self.sends.get_unchecked(send_idx) }.0);
                                let meth = stry!(cls.get_method(self, &*name));
                                self.inline_caches[cache_idx] = Some((rcv_cls, Gc::clone(&meth)));
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
                    send_args_on_stack!(send_rcv, meth, nargs);
                    pc += 1;
                }
                Instr::String(string_off) => {
                    debug_assert!(self.strings.len() > string_off);
                    let s = unsafe { self.strings.get_unchecked(string_off) }.clone();
                    self.stack.push(s);
                    pc += 1;
                }
                Instr::Symbol(symbol_off) => {
                    debug_assert!(self.symbols.len() > symbol_off);
                    let s = unsafe { self.symbols.get_unchecked(symbol_off) }.clone();
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
            Primitive::AsString => {
                let v = stry!(rcv.to_strval(self));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::AsSymbol => {
                let v = stry!(stry!(rcv.downcast::<String_>(self)).to_symbol(self));
                self.stack.push(v);
                SendReturn::Val
            }
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
                        process::exit(c);
                    }
                }
                if c_val.get_class(self) == self.int_cls {
                    SendReturn::Err(VMError::new(self, VMErrorKind::DomainError))
                } else {
                    let expected = Int::static_objtype();
                    let got = c_val.dyn_objtype(self);
                    SendReturn::Err(VMError::new(self, VMErrorKind::TypeError { expected, got }))
                }
            }
            Primitive::Global => {
                let name_val = self.stack.pop();
                // XXX This should use Symbols not strings.
                let name: &String_ = stry!(name_val.downcast(self));
                assert!(!name.is_str);
                let g = self.get_global_or_nil(name.as_str());
                self.stack.push(g);
                SendReturn::Val
            }
            Primitive::GlobalPut => {
                let v = self.stack.pop();
                let name_val = self.stack.pop();
                // XXX This should use Symbols not strings.
                let name: &String_ = stry!(name_val.downcast(self));
                assert!(!name.is_str);
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
            Primitive::Hashcode => unimplemented!(),
            Primitive::Inspect => unimplemented!(),
            Primitive::InstVarAt => unimplemented!(),
            Primitive::InstVarAtPut => unimplemented!(),
            Primitive::InstVarNamed => unimplemented!(),
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
                // XXX This should use Symbols not strings.
                let name: &String_ = stry!(name_val.downcast(self));
                match self.find_class(name.as_str()) {
                    Ok(ref p) => {
                        let cls = self.compile(p, true);
                        self.stack.push(cls);
                    }
                    Err(_) => {
                        let v = self.nil.clone();
                        self.stack.push(v);
                    }
                }
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
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::New => {
                let v = Inst::new(self, rcv);
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
            Primitive::Perform => unimplemented!(),
            Primitive::PerformInSuperClass => unimplemented!(),
            Primitive::PerformWithArguments => unimplemented!(),
            Primitive::PerformWithArgumentsInSuperClass => unimplemented!(),
            Primitive::RefEquals => {
                let v = self.stack.pop();
                let v = stry!(rcv.ref_equals(self, v));
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Restart => unreachable!(),
            Primitive::PrintNewline => {
                println!();
                let v = self.system.clone();
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::PrintString => {
                let v = self.stack.pop();
                let str_: &String_ = stry!(v.downcast(self));
                print!("{}", str_.as_str());
                let v = self.system.clone();
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Shl => {
                let v = self.stack.pop();
                let v = stry!(rcv.shl(self, v));
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
                let cls: &Class = stry!(rcv.downcast(self));
                let v = cls.supercls(self);
                self.stack.push(v);
                SendReturn::Val
            }
            Primitive::Value(nargs) => {
                let rcv_blk: &Block = stry!(rcv.downcast(self));
                let (num_vars, bytecode_off, max_stack) = {
                    let blkinfo = &self.blockinfos[rcv_blk.blockinfo_off];
                    (blkinfo.num_vars, blkinfo.bytecode_off, blkinfo.max_stack)
                };
                if self.stack.remaining_capacity() < max_stack {
                    panic!("Not enough stack space to execute block.");
                }
                let frame = Frame::new(
                    self,
                    false,
                    rcv.clone(),
                    Some(Gc::clone(&rcv_blk.parent_closure)),
                    num_vars,
                    nargs as usize,
                );
                self.frames.push(frame);
                let r = self.exec_user(
                    rcv_blk.inst.clone(),
                    Gc::clone(&rcv_blk.method),
                    bytecode_off,
                );
                self.frame_pop();
                r
            }
        }
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
                    return Ok(Gc::clone(cache_meth));
                }
            }
        }
        // The inline cache is empty or out of date, so store a new value in it.
        let meth = rcv_cls.downcast::<Class>(self)?.get_method(self, &name)?;
        self.inline_caches[idx] = Some((rcv_cls, Gc::clone(&meth)));
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
        let send = (Rc::new(send.0), send.1);
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
            let v = String_::new(self, s, true);
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
            let v = String_::new(self, s, false);
            self.symbols.push(v);
            len
        }
    }

    /// Add the global `n` to the VM, returning its index. Note that global names (like strings)
    /// are reused, so indexes are also reused.
    pub fn add_global(&mut self, s: String) -> usize {
        // We want to avoid `clone`ing `s` in the (hopefully common) case of a cache hit, hence
        // this slightly laborious dance and double-lookup.
        if let Some(i) = self.reverse_globals.get(&s) {
            *i
        } else {
            let len = self.globals.len();
            self.reverse_globals.insert(s.clone(), len);
            self.globals.push(Val::illegal());
            len
        }
    }

    /// Lookup the global `name`: if it has not been added, or has been added but not set, then
    /// `self.nil` will be returned.
    pub fn get_global_or_nil(&self, name: &str) -> Val {
        if let Some(i) = self.reverse_globals.get(name).cloned() {
            let v = &self.globals[i];
            if v.valkind() != ValKind::ILLEGAL {
                return v.clone();
            }
        }
        self.nil.clone()
    }

    /// Get the global at position `i`: if it has not been set (i.e. is `ValKind::ILLEGAL`) this
    /// will return `Err(...)`.
    pub fn get_legal_global(&self, i: usize) -> Result<Val, Box<VMError>> {
        let v = &self.globals[i];
        if v.valkind() != ValKind::ILLEGAL {
            return Ok(v.clone());
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
    closure: Gc<Closure>,
}

impl Frame {
    fn new(
        vm: &mut VM,
        is_method: bool,
        self_val: Val,
        parent_closure: Option<Gc<Closure>>,
        num_vars: usize,
        num_args: usize,
    ) -> Self {
        let mut vars = Vec::with_capacity(num_vars);
        vars.resize_with(num_vars, Val::illegal);

        if is_method {
            vars[0] = self_val;
            for i in 0..num_args {
                vars[num_args - i] = vm.stack.pop();
            }
            for v in vars.iter_mut().skip(num_args + 1).take(num_vars) {
                *v = vm.nil.clone();
            }
        } else {
            for i in 0..num_args {
                vars[num_args - i - 1] = vm.stack.pop();
            }
            for v in vars.iter_mut().skip(num_args).take(num_vars) {
                *v = vm.nil.clone();
            }
        }

        Frame {
            sp: 0,
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
        let mut c = Gc::clone(&self.closure);
        while depth > 0 {
            c = Gc::clone(c.parent.as_ref().unwrap());
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
        unsafe { (&*self.vars.0.get()).get_unchecked(var) }.clone()
    }

    fn set_var(&self, var: usize, val: Val) {
        unsafe { *(&mut *self.vars.0.get()).get_unchecked_mut(var) = val };
    }
}

impl GcLayout for Closure {
    fn layout(&self) -> std::alloc::Layout {
        std::alloc::Layout::new::<Self>()
    }
}

impl GcLayout for Vars {
    fn layout(&self) -> std::alloc::Layout {
        std::alloc::Layout::new::<Self>()
    }
}

#[cfg(test)]
impl VM {
    pub fn new_no_bootstrap() -> Self {
        VM {
            classpath: vec![],
            block_cls: Val::illegal(),
            block2_cls: Val::illegal(),
            block3_cls: Val::illegal(),
            bool_cls: Val::illegal(),
            cls_cls: Val::illegal(),
            double_cls: Val::illegal(),
            false_cls: Val::illegal(),
            int_cls: Val::illegal(),
            metacls_cls: Val::illegal(),
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
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_frame() {
        let mut vm = VM::new_no_bootstrap();
        let selfv = Val::from_isize(&mut vm, 42).unwrap();
        let v = Val::from_isize(&mut vm, 43).unwrap();
        vm.stack.push(v);
        let v = Val::from_isize(&mut vm, 44).unwrap();
        vm.stack.push(v);
        let f = Frame::new(&mut vm, true, selfv, None, 3, 2);
        assert_eq!(f.var_lookup(0, 0).as_isize(&mut vm).unwrap(), 42);
        assert_eq!(f.var_lookup(0, 1).as_isize(&mut vm).unwrap(), 43);
        assert_eq!(f.var_lookup(0, 2).as_isize(&mut vm).unwrap(), 44);
    }
}
