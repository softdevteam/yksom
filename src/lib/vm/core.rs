//! The core part of the interpreter.

use std::{
    cell::UnsafeCell,
    collections::HashMap,
    convert::TryFrom,
    path::{Path, PathBuf},
    process,
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

/// The core VM struct. Although SOM is single-threaded, we roughly model what a multi-threaded VM
/// would need to look like. That is, since this struct would need to be shared between threads and
/// called without a single lock, thread-safety would need to be handled internally. We model that
/// with [`UnsafeCell`].
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
    blockinfos: UnsafeCell<Vec<BlockInfo>>,
    classes: UnsafeCell<Vec<Val>>,
    /// The current known set of globals including those not yet assigned to: in other words, it is
    /// expected that some entries of this `Vec` are illegal (i.e. created by `Val::illegal`).
    globals: UnsafeCell<Vec<Val>>,
    reverse_globals: UnsafeCell<HashMap<String, usize>>,
    inline_caches: UnsafeCell<Vec<Option<(Val, Gc<Method>)>>>,
    /// `instrs` and `instr_span`s are always the same length: they are separated only because we
    /// rarely access `instr_spans`.
    instrs: UnsafeCell<Vec<Instr>>,
    instr_spans: UnsafeCell<Vec<Span>>,
    sends: UnsafeCell<Vec<(String, usize)>>,
    /// reverse_sends is an optimisation allowing us to reuse sends: it maps a send `(String,
    /// usize)` to a `usize` where the latter represents the index of the send in `sends`.
    reverse_sends: UnsafeCell<HashMap<(String, usize), usize>>,
    stack: UnsafeCell<SOMStack>,
    strings: UnsafeCell<Vec<Val>>,
    /// reverse_strings is an optimisation allowing us to reuse strings: it maps a `String to a
    /// `usize` where the latter represents the index of the string in `strings`.
    reverse_strings: UnsafeCell<HashMap<String, usize>>,
    symbols: UnsafeCell<Vec<Val>>,
    reverse_symbols: UnsafeCell<HashMap<String, usize>>,
    frames: UnsafeCell<Vec<Frame>>,
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
            blockinfos: UnsafeCell::new(Vec::new()),
            classes: UnsafeCell::new(Vec::new()),
            globals: UnsafeCell::new(Vec::new()),
            reverse_globals: UnsafeCell::new(HashMap::new()),
            inline_caches: UnsafeCell::new(Vec::new()),
            instrs: UnsafeCell::new(Vec::new()),
            instr_spans: UnsafeCell::new(Vec::new()),
            sends: UnsafeCell::new(Vec::new()),
            reverse_sends: UnsafeCell::new(HashMap::new()),
            stack: UnsafeCell::new(SOMStack::new()),
            strings: UnsafeCell::new(Vec::new()),
            reverse_strings: UnsafeCell::new(HashMap::new()),
            symbols: UnsafeCell::new(Vec::new()),
            reverse_symbols: UnsafeCell::new(HashMap::new()),
            frames: UnsafeCell::new(Vec::new()),
        };
        // The very delicate phase.
        //
        // Nothing in this phase must store references to the nil object or any classes earlier
        // than it in the phase.
        vm.obj_cls = vm.init_builtin_class("Object", false);
        vm.cls_cls = vm.init_builtin_class("Class", false);
        vm.nil_cls = vm.init_builtin_class("Nil", true);
        vm.nil = Inst::new(&vm, vm.nil_cls.clone());

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
        vm.false_ = Inst::new(&vm, vm.false_cls.clone());
        vm.system = Inst::new(&vm, vm.system_cls.clone());
        vm.true_ = Inst::new(&vm, vm.true_cls.clone());

        // Populate globals.
        vm.set_global("false", vm.false_.clone());
        vm.set_global("nil", vm.nil.clone());
        vm.set_global("true", vm.true_.clone());
        vm.set_global("system", Inst::new(&vm, vm.system_cls.clone()));

        vm
    }

    /// Compile the file at `path`. `inst_vars_allowed` should be set to `false` only for those
    /// builtin classes which do not lead to run-time instances of `Inst`.
    pub fn compile(&self, path: &Path, inst_vars_allowed: bool) -> Val {
        let cls_val = compile(self, path);
        let cls: &Class = cls_val.downcast(self).unwrap();
        if !inst_vars_allowed && cls.num_inst_vars > 0 {
            panic!("No instance vars allowed in {}", path.to_str().unwrap());
        }
        unsafe { &mut *self.classes.get() }.push(cls_val.clone());
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
    fn init_builtin_class(&self, name: &str, inst_vars_allowed: bool) -> Val {
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
    pub fn top_level_send(&self, rcv: Val, msg: &str, args: Vec<Val>) -> Result<Val, Box<VMError>> {
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
                if unsafe { &*self.stack.get() }.remaining_capacity() < max_stack {
                    panic!("Not enough stack space to execute method.");
                }
                let nargs = args.len();
                for a in args {
                    unsafe { &mut *self.stack.get() }.push(a);
                }
                let frame = Frame::new(self, true, rcv.clone(), None, num_vars, nargs);
                unsafe { &mut *self.frames.get() }.push(frame);
                let r = self.exec_user(rcv, Gc::clone(&meth), bytecode_off);
                self.frame_pop();
                match r {
                    SendReturn::ClosureReturn(_) => unreachable!(),
                    SendReturn::Err(e) => Err(Box::new(*e)),
                    SendReturn::Val => Ok(unsafe { &mut *self.stack.get() }.pop()),
                }
            }
        }
    }

    /// This function should only be called via the `send_args_on_stack!` macro.
    fn send_args_on_stack(&self, rcv: Val, method: Gc<Method>, nargs: usize) -> SendReturn {
        match method.body {
            MethodBody::Primitive(p) => self.exec_primitive(p, rcv),
            MethodBody::User {
                num_vars,
                bytecode_off,
                max_stack,
            } => {
                if unsafe { &*self.stack.get() }.remaining_capacity() < max_stack {
                    panic!("Not enough stack space to execute method.");
                }
                let nframe = Frame::new(self, true, rcv.clone(), None, num_vars, nargs);
                unsafe { &mut *self.frames.get() }.push(nframe);
                let r = self.exec_user(rcv, Gc::clone(&method), bytecode_off);
                self.frame_pop();
                r
            }
        }
    }

    /// Execute a SOM method. Note that the frame for this method must have been created *before*
    /// calling this function.
    fn exec_user(&self, rcv: Val, method: Gc<Method>, meth_start_pc: usize) -> SendReturn {
        let mut pc = meth_start_pc;

        macro_rules! stry {
            ($elem:expr) => {{
                let e = $elem;
                match e {
                    Ok(o) => o,
                    Err(mut e) => {
                        e.backtrace
                            .push((Gc::clone(&method), unsafe { &*self.instr_spans.get() }[pc]));
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
                        e.backtrace
                            .push((Gc::clone(&method), unsafe { &*self.instr_spans.get() }[pc]));
                        return SendReturn::Err(e);
                    }
                    SendReturn::Val => (),
                }
            }};
        }

        let stack_start = unsafe { &*self.stack.get() }.len();
        loop {
            let instr = {
                let instrs = unsafe { &*self.instrs.get() };
                debug_assert!(pc < instrs.len());
                *unsafe { instrs.get_unchecked(pc) }
            };
            match instr {
                Instr::Block(blkinfo_off) => {
                    let (num_params, bytecode_end) = {
                        let blkinfo = &unsafe { &*self.blockinfos.get() }[blkinfo_off];
                        (blkinfo.num_params, blkinfo.bytecode_end)
                    };
                    unsafe { &mut *self.stack.get() }.push(Block::new(
                        self,
                        Gc::clone(&method),
                        rcv.clone(),
                        blkinfo_off,
                        Gc::clone(&self.current_frame().closure),
                        num_params,
                    ));
                    pc = bytecode_end;
                }
                Instr::ClosureReturn(closure_depth) => {
                    // We want to do a non-local return. Before we attempt that, we need to
                    // check that the block hasn't escaped its function (and we know we're in a
                    // block because only a block can attempt a non-local return).
                    // Fortunately, the `closure` pointer in a frame is a perfect proxy for
                    // determining this: if this frame's (i.e. block's!) parent closure is not
                    // consistent with the frame stack, then the block has escaped.
                    let v = unsafe { &mut *self.stack.get() }.pop();
                    let parent_closure = self.current_frame().closure(closure_depth);
                    for (frame_depth, pframe) in
                        unsafe { &*self.frames.get() }.iter().rev().enumerate()
                    {
                        if Gc::ptr_eq(&parent_closure, &pframe.closure) {
                            unsafe { &mut *self.stack.get() }.truncate(pframe.sp());
                            unsafe { &mut *self.stack.get() }.push(v);
                            return SendReturn::ClosureReturn(frame_depth);
                        }
                    }
                    panic!("Return from escaped block");
                }
                Instr::Double(i) => {
                    unsafe { &mut *self.stack.get() }.push(Double::new(self, i));
                    pc += 1;
                }
                Instr::GlobalLookup(i) => {
                    let v = unsafe { &mut *self.globals.get() }[i].clone();
                    if v.valkind() != ValKind::ILLEGAL {
                        // The global value is already set
                        unsafe { &mut *self.stack.get() }.push(v.clone());
                    } else {
                        // We have to call `self unknownGlobal:<symbol name>`.
                        let cls_val = rcv.get_class(self);
                        let cls: &Class = stry!(cls_val.downcast(self));
                        let meth = stry!(cls.get_method(self, "unknownGlobal:"));
                        self.current_frame()
                            .set_sp(unsafe { &*self.stack.get() }.len());
                        let name = {
                            let reverse_globals = unsafe { &mut *self.reverse_globals.get() };
                            // XXX O(n) lookup!
                            reverse_globals
                                .iter()
                                .find(|(_, j)| **j == i)
                                .map(|(n, _)| n)
                                .unwrap()
                                .clone()
                        };
                        let symbol = String_::new(self, name, false);
                        unsafe { &mut *self.stack.get() }.push(symbol);
                        send_args_on_stack!(rcv.clone(), meth, 1);
                    }
                    pc += 1;
                }
                Instr::InstVarLookup(n) => {
                    let inst: &Inst = rcv.downcast(self).unwrap();
                    unsafe { &mut *self.stack.get() }.push(inst.inst_var_lookup(n));
                    pc += 1;
                }
                Instr::InstVarSet(n) => {
                    let inst: &Inst = rcv.downcast(self).unwrap();
                    inst.inst_var_set(n, unsafe { &*self.stack.get() }.peek());
                    pc += 1;
                }
                Instr::Int(i) => {
                    // from_isize(i) cannot fail so the unwrap() is safe.
                    unsafe { &mut *self.stack.get() }.push(Val::from_isize(self, i).unwrap());
                    pc += 1;
                }
                Instr::Pop => {
                    unsafe { &mut *self.stack.get() }.pop();
                    pc += 1;
                }
                Instr::Return => {
                    return SendReturn::Val;
                }
                Instr::Send(send_idx, cache_idx) => {
                    let (send_rcv, nargs, meth) = {
                        debug_assert!(send_idx < unsafe { &*self.sends.get() }.len());
                        let (ref name, nargs) =
                            unsafe { (&*self.sends.get()).get_unchecked(send_idx) };
                        // Note that since we maintain a reference to `name` for the rest of this
                        // block, we mustn't mutate (directly or indirectly) `self.sends` in any
                        // way.
                        let rcv = unsafe { &mut *self.stack.get() }.pop_n(*nargs);
                        let rcv_cls = rcv.get_class(self);

                        let meth = stry!(self.inline_cache_lookup(cache_idx, rcv_cls, name));
                        (rcv, nargs, meth)
                    };

                    if let MethodBody::Primitive(Primitive::Restart) = meth.body {
                        unsafe { &mut *self.stack.get() }.truncate(stack_start);
                        pc = meth_start_pc;
                        continue;
                    }

                    self.current_frame()
                        .set_sp(unsafe { &*self.stack.get() }.len() - nargs);
                    send_args_on_stack!(send_rcv, meth, *nargs);
                    pc += 1;
                }
                Instr::String(string_off) => {
                    debug_assert!(unsafe { &*self.strings.get() }.len() > string_off);
                    let s = unsafe { (&*self.strings.get()).get_unchecked(string_off) }.clone();
                    unsafe { &mut *self.stack.get() }.push(s);
                    pc += 1;
                }
                Instr::Symbol(symbol_off) => {
                    debug_assert!(unsafe { &*self.symbols.get() }.len() > symbol_off);
                    let s = unsafe { (&*self.symbols.get()).get_unchecked(symbol_off) }.clone();
                    unsafe { &mut *self.stack.get() }.push(s);
                    pc += 1;
                }
                Instr::VarLookup(d, n) => {
                    let val = self.current_frame().var_lookup(d, n);
                    unsafe { &mut *self.stack.get() }.push(val);
                    pc += 1;
                }
                Instr::VarSet(d, n) => {
                    let val = unsafe { &*self.stack.get() }.peek();
                    self.current_frame().var_set(d, n, val);
                    pc += 1;
                }
            }
        }
    }

    fn exec_primitive(&self, prim: Primitive, rcv: Val) -> SendReturn {
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
                unsafe { &mut *self.stack.get() }
                    .push(stry!(rcv.add(self, unsafe { &mut *self.stack.get() }.pop())));
                SendReturn::Val
            }
            Primitive::And => {
                unsafe { &mut *self.stack.get() }
                    .push(stry!(rcv.and(self, unsafe { &mut *self.stack.get() }.pop())));
                SendReturn::Val
            }
            Primitive::AsString => {
                unsafe { &mut *self.stack.get() }.push(stry!(rcv.to_strval(self)));
                SendReturn::Val
            }
            Primitive::AsSymbol => {
                unsafe { &mut *self.stack.get() }
                    .push(stry!(stry!(rcv.downcast::<String_>(self)).to_symbol(self)));
                SendReturn::Val
            }
            Primitive::BitXor => {
                unsafe { &mut *self.stack.get() }
                    .push(stry!(rcv.xor(self, unsafe { &mut *self.stack.get() }.pop())));
                SendReturn::Val
            }
            Primitive::Class => {
                unsafe { &mut *self.stack.get() }.push(rcv.get_class(self));
                SendReturn::Val
            }
            Primitive::Concatenate => {
                unsafe { &mut *self.stack.get() }.push(stry!(stry!(rcv.downcast::<String_>(self))
                    .concatenate(self, unsafe { &mut *self.stack.get() }.pop())));
                SendReturn::Val
            }
            Primitive::Div => {
                unsafe { &mut *self.stack.get() }
                    .push(stry!(rcv.div(self, unsafe { &mut *self.stack.get() }.pop())));
                SendReturn::Val
            }
            Primitive::DoubleDiv => {
                unsafe { &mut *self.stack.get() }.push(stry!(
                    rcv.double_div(self, unsafe { &mut *self.stack.get() }.pop())
                ));
                SendReturn::Val
            }
            Primitive::Equals => {
                unsafe { &mut *self.stack.get() }.push(stry!(
                    rcv.equals(self, unsafe { &mut *self.stack.get() }.pop())
                ));
                SendReturn::Val
            }
            Primitive::Exit => {
                let c_val = unsafe { &mut *self.stack.get() }.pop();
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
                    SendReturn::Err(VMError::new(
                        self,
                        VMErrorKind::TypeError {
                            expected: Int::static_objtype(),
                            got: c_val.dyn_objtype(self),
                        },
                    ))
                }
            }
            Primitive::Global => {
                let name_val = unsafe { &mut *self.stack.get() }.pop();
                // XXX This should use Symbols not strings.
                let name: &String_ = stry!(name_val.downcast(self));
                assert!(!name.is_str);
                let g = self.get_global_or_nil(name.as_str());
                unsafe { &mut *self.stack.get() }.push(g);
                SendReturn::Val
            }
            Primitive::GlobalPut => {
                let v = unsafe { &mut *self.stack.get() }.pop();
                let name_val = unsafe { &mut *self.stack.get() }.pop();
                // XXX This should use Symbols not strings.
                let name: &String_ = stry!(name_val.downcast(self));
                assert!(!name.is_str);
                self.set_global(name.as_str(), v);
                unsafe { &mut *self.stack.get() }.push(rcv);
                SendReturn::Val
            }
            Primitive::GreaterThan => {
                unsafe { &mut *self.stack.get() }.push(stry!(
                    rcv.greater_than(self, unsafe { &mut *self.stack.get() }.pop())
                ));
                SendReturn::Val
            }
            Primitive::GreaterThanEquals => {
                unsafe { &mut *self.stack.get() }.push(stry!(
                    rcv.greater_than_equals(self, unsafe { &mut *self.stack.get() }.pop())
                ));
                SendReturn::Val
            }
            Primitive::Halt => unimplemented!(),
            Primitive::Hashcode => unimplemented!(),
            Primitive::Inspect => unimplemented!(),
            Primitive::InstVarAt => unimplemented!(),
            Primitive::InstVarAtPut => unimplemented!(),
            Primitive::InstVarNamed => unimplemented!(),
            Primitive::LessThan => {
                unsafe { &mut *self.stack.get() }.push(stry!(
                    rcv.less_than(self, unsafe { &mut *self.stack.get() }.pop())
                ));
                SendReturn::Val
            }
            Primitive::LessThanEquals => {
                unsafe { &mut *self.stack.get() }.push(stry!(
                    rcv.less_than_equals(self, unsafe { &mut *self.stack.get() }.pop())
                ));
                SendReturn::Val
            }
            Primitive::Load => {
                let name_val = unsafe { &mut *self.stack.get() }.pop();
                // XXX This should use Symbols not strings.
                let name: &String_ = stry!(name_val.downcast(self));
                match self.find_class(name.as_str()) {
                    Ok(ref p) => {
                        let cls = self.compile(p, true);
                        unsafe { &mut *self.stack.get() }.push(cls);
                    }
                    Err(_) => {
                        unsafe { &mut *self.stack.get() }.push(self.nil.clone());
                    }
                }
                SendReturn::Val
            }
            Primitive::Mod => {
                unsafe { &mut *self.stack.get() }.push(stry!(
                    rcv.modulus(self, unsafe { &mut *self.stack.get() }.pop())
                ));
                SendReturn::Val
            }
            Primitive::Mul => {
                unsafe { &mut *self.stack.get() }
                    .push(stry!(rcv.mul(self, unsafe { &mut *self.stack.get() }.pop())));
                SendReturn::Val
            }
            Primitive::Name => {
                unsafe { &mut *self.stack.get() }
                    .push(stry!(stry!(rcv.downcast::<Class>(self)).name(self)));
                SendReturn::Val
            }
            Primitive::New => {
                unsafe { &mut *self.stack.get() }.push(Inst::new(self, rcv));
                SendReturn::Val
            }
            Primitive::NotEquals => {
                unsafe { &mut *self.stack.get() }.push(stry!(
                    rcv.not_equals(self, unsafe { &mut *self.stack.get() }.pop())
                ));
                SendReturn::Val
            }
            Primitive::ObjectSize => unimplemented!(),
            Primitive::Perform => unimplemented!(),
            Primitive::PerformInSuperClass => unimplemented!(),
            Primitive::PerformWithArguments => unimplemented!(),
            Primitive::PerformWithArgumentsInSuperClass => unimplemented!(),
            Primitive::RefEquals => {
                unsafe { &mut *self.stack.get() }.push(stry!(
                    rcv.ref_equals(self, unsafe { &mut *self.stack.get() }.pop())
                ));
                SendReturn::Val
            }
            Primitive::Restart => unreachable!(),
            Primitive::PrintNewline => {
                println!();
                unsafe { &mut *self.stack.get() }.push(self.system.clone());
                SendReturn::Val
            }
            Primitive::PrintString => {
                let v = unsafe { &mut *self.stack.get() }.pop();
                let str_: &String_ = stry!(v.downcast(self));
                print!("{}", str_.as_str());
                unsafe { &mut *self.stack.get() }.push(self.system.clone());
                SendReturn::Val
            }
            Primitive::Shl => {
                unsafe { &mut *self.stack.get() }
                    .push(stry!(rcv.shl(self, unsafe { &mut *self.stack.get() }.pop())));
                SendReturn::Val
            }
            Primitive::Sqrt => {
                unsafe { &mut *self.stack.get() }.push(stry!(rcv.sqrt(self)));
                SendReturn::Val
            }
            Primitive::Sub => {
                unsafe { &mut *self.stack.get() }
                    .push(stry!(rcv.sub(self, unsafe { &mut *self.stack.get() }.pop())));
                SendReturn::Val
            }
            Primitive::Superclass => {
                let cls: &Class = stry!(rcv.downcast(self));
                unsafe { &mut *self.stack.get() }.push(cls.superclass(self));
                SendReturn::Val
            }
            Primitive::Value(nargs) => {
                let rcv_blk: &Block = stry!(rcv.downcast(self));
                let (num_vars, bytecode_off, max_stack) = {
                    let blkinfo = &unsafe { &*self.blockinfos.get() }[rcv_blk.blockinfo_off];
                    (blkinfo.num_vars, blkinfo.bytecode_off, blkinfo.max_stack)
                };
                if unsafe { &*self.stack.get() }.remaining_capacity() < max_stack {
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
                unsafe { &mut *self.frames.get() }.push(frame);
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

    fn current_frame(&self) -> &Frame {
        debug_assert!(!unsafe { &*self.frames.get() }.is_empty());
        let frames_len = unsafe { &*self.frames.get() }.len();
        unsafe { (&*self.frames.get()).get_unchecked(frames_len - 1) }
    }

    fn frame_pop(&self) {
        unsafe { &mut *self.frames.get() }.pop();
    }

    pub fn frames_len(&self) -> usize {
        unsafe { &mut *self.frames.get() }.len()
    }

    /// Add `blkinfo` to the set of known `BlockInfo`s and return its index.
    pub fn push_blockinfo(&self, blkinfo: BlockInfo) -> usize {
        let bis = unsafe { &mut *self.blockinfos.get() };
        let i = bis.len();
        bis.push(blkinfo);
        i
    }

    /// Update the `BlockInfo` at index `idx` to `blkinfo`.
    pub fn set_blockinfo(&self, idx: usize, blkinfo: BlockInfo) {
        let bis = unsafe { &mut *self.blockinfos.get() };
        bis[idx] = blkinfo;
    }

    /// Add an empty inline cache to the VM, returning its index.
    pub fn new_inline_cache(&self) -> usize {
        let ics = unsafe { &mut *self.inline_caches.get() };
        let len = ics.len();
        ics.push(None);
        len
    }

    /// Lookup the method `name` in the class `rcv_cls`, utilising the inline cache at index `idx`.
    ///
    /// # Guarantees for UnsafeCell
    ///
    /// This method guarantees not to mutate `self.sends`.
    pub fn inline_cache_lookup(
        &self,
        idx: usize,
        rcv_cls: Val,
        name: &str,
    ) -> Result<Gc<Method>, Box<VMError>> {
        // Lookup the method in the inline cache.
        {
            let cache = &unsafe { &*self.inline_caches.get() }[idx];
            if let Some((cache_cls, cache_meth)) = cache {
                if cache_cls.bit_eq(&rcv_cls) {
                    return Ok(Gc::clone(cache_meth));
                }
            }
        }
        // The inline cache is empty or out of date, so store a new value in it.
        let meth = rcv_cls.downcast::<Class>(self)?.get_method(self, &name)?;
        let ics = unsafe { &mut *self.inline_caches.get() };
        ics[idx] = Some((rcv_cls, Gc::clone(&meth)));
        Ok(meth)
    }

    /// How many instructions are currently present in the VM?
    pub fn instrs_len(&self) -> usize {
        unsafe { &*self.instrs.get() }.len()
    }

    /// Push `instr` to the end of the current vector of instructions, associating `span` with it
    /// for the purposes of backtraces.
    pub fn instrs_push(&self, instr: Instr, span: Span) {
        debug_assert_eq!(
            unsafe { &mut *self.instrs.get() }.len(),
            unsafe { &mut *self.instr_spans.get() }.len()
        );
        unsafe { &mut *self.instrs.get() }.push(instr);
        unsafe { &mut *self.instr_spans.get() }.push(span);
    }

    /// Add the send `send` to the VM, returning its index. Note that sends are reused, so indexes
    /// are also reused.
    pub fn add_send(&self, send: (String, usize)) -> usize {
        let reverse_sends = unsafe { &mut *self.reverse_sends.get() };
        // We want to avoid `clone`ing `send` in the (hopefully common) case of a cache hit, hence
        // this slightly laborious dance and double-lookup.
        if let Some(i) = reverse_sends.get(&send) {
            *i
        } else {
            let sends = unsafe { &mut *self.sends.get() };
            let len = sends.len();
            reverse_sends.insert(send.clone(), len);
            sends.push(send);
            len
        }
    }

    /// Add the string `s` to the VM, returning its index. Note that strings are reused, so indexes
    /// are also reused.
    pub fn add_string(&self, s: String) -> usize {
        let reverse_strings = unsafe { &mut *self.reverse_strings.get() };
        // We want to avoid `clone`ing `s` in the (hopefully common) case of a cache hit, hence
        // this slightly laborious dance and double-lookup.
        if let Some(i) = reverse_strings.get(&s) {
            *i
        } else {
            let strings = unsafe { &mut *self.strings.get() };
            let len = strings.len();
            reverse_strings.insert(s.clone(), len);
            strings.push(String_::new(self, s, true));
            len
        }
    }

    /// Add the symbol `s` to the VM, returning its index. Note that symbols are reused, so indexes
    /// are also reused.
    pub fn add_symbol(&self, s: String) -> usize {
        let reverse_symbols = unsafe { &mut *self.reverse_symbols.get() };
        // We want to avoid `clone`ing `s` in the (hopefully common) case of a cache hit, hence
        // this slightly laborious dance and double-lookup.
        if let Some(i) = reverse_symbols.get(&s) {
            *i
        } else {
            let symbols = unsafe { &mut *self.symbols.get() };
            let len = symbols.len();
            reverse_symbols.insert(s.clone(), len);
            symbols.push(String_::new(self, s, false));
            len
        }
    }

    /// Add the global `n` to the VM, returning its index. Note that global names (like strings)
    /// are reused, so indexes are also reused.
    pub fn add_global(&self, s: String) -> usize {
        let reverse_globals = unsafe { &mut *self.reverse_globals.get() };
        // We want to avoid `clone`ing `s` in the (hopefully common) case of a cache hit, hence
        // this slightly laborious dance and double-lookup.
        if let Some(i) = reverse_globals.get(&s) {
            *i
        } else {
            let globals = unsafe { &mut *self.globals.get() };
            let len = globals.len();
            reverse_globals.insert(s.clone(), len);
            globals.push(Val::illegal());
            len
        }
    }

    /// Lookup the global `name`: if it has not been added, or has been added but not set, then
    /// `self.nil` will be returned. Notice that this does not change the stored value for this
    /// global.
    pub fn get_global_or_nil(&self, name: &str) -> Val {
        let reverse_globals = unsafe { &mut *self.reverse_globals.get() };
        if let Some(i) = reverse_globals.get(name).cloned() {
            let globals = unsafe { &mut *self.globals.get() };
            let v = &globals[i];
            if v.valkind() != ValKind::ILLEGAL {
                return v.clone();
            }
        }
        self.nil.clone()
    }

    /// Get the global at position `i`: if it has not been set (i.e. is `ValKind::ILLEGAL`) this
    /// will return `Err(...)`.
    pub fn get_legal_global(&self, i: usize) -> Result<Val, Box<VMError>> {
        let globals = unsafe { &mut *self.globals.get() };
        let v = &globals[i];
        if v.valkind() != ValKind::ILLEGAL {
            return Ok(v.clone());
        }
        let reverse_globals = unsafe { &mut *self.reverse_globals.get() };
        Err(VMError::new(
            self,
            VMErrorKind::UnknownGlobal(
                reverse_globals
                    .iter()
                    .find(|(_, j)| **j == i)
                    .map(|(n, _)| n)
                    .unwrap()
                    .clone(),
            ),
        ))
    }

    /// Set the global `name` to the value `v`, overwriting the previous value (if any).
    pub fn set_global(&self, name: &str, v: Val) {
        let globals = unsafe { &mut *self.globals.get() };
        let reverse_globals = unsafe { &mut *self.reverse_globals.get() };
        debug_assert_eq!(globals.len(), reverse_globals.len());
        // We want to avoid `clone`ing `s` in the (hopefully common) case of a cache hit, hence
        // this slightly laborious dance and double-lookup.
        if let Some(i) = reverse_globals.get(name) {
            globals[*i] = v;
        } else {
            reverse_globals.insert(name.to_owned(), globals.len());
            globals.push(v);
        }
    }
}

#[derive(Debug)]
pub struct Frame {
    /// Stack pointer. Note that this is updated lazily (i.e. it might not be accurate at all
    /// points, but it is guaranteed to be correct over function calls).
    sp: UnsafeCell<usize>,
    closure: Gc<Closure>,
}

impl Frame {
    fn new(
        vm: &VM,
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
                vars[num_args - i] = unsafe { &mut *vm.stack.get() }.pop();
            }
            for v in vars.iter_mut().skip(num_args + 1).take(num_vars) {
                *v = vm.nil.clone();
            }
        } else {
            for i in 0..num_args {
                vars[num_args - i - 1] = unsafe { &mut *vm.stack.get() }.pop();
            }
            for v in vars.iter_mut().skip(num_args).take(num_vars) {
                *v = vm.nil.clone();
            }
        }

        Frame {
            sp: UnsafeCell::new(0),
            closure: Gc::new(Closure::new(parent_closure, vars)),
        }
    }

    fn var_lookup(&self, depth: usize, var: usize) -> Val {
        self.closure(depth).get_var(var)
    }

    fn var_set(&self, depth: usize, var: usize, val: Val) {
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
        *unsafe { &*self.sp.get() }
    }

    /// Set this frame's stack pointer to `sp`.
    fn set_sp(&self, sp: usize) {
        *unsafe { &mut *self.sp.get() } = sp;
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
            blockinfos: UnsafeCell::new(Vec::new()),
            classes: UnsafeCell::new(Vec::new()),
            globals: UnsafeCell::new(Vec::new()),
            reverse_globals: UnsafeCell::new(HashMap::new()),
            inline_caches: UnsafeCell::new(Vec::new()),
            instrs: UnsafeCell::new(Vec::new()),
            instr_spans: UnsafeCell::new(Vec::new()),
            sends: UnsafeCell::new(Vec::new()),
            reverse_sends: UnsafeCell::new(HashMap::new()),
            stack: UnsafeCell::new(SOMStack::new()),
            strings: UnsafeCell::new(Vec::new()),
            reverse_strings: UnsafeCell::new(HashMap::new()),
            symbols: UnsafeCell::new(Vec::new()),
            reverse_symbols: UnsafeCell::new(HashMap::new()),
            frames: UnsafeCell::new(Vec::new()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_frame() {
        let vm = VM::new_no_bootstrap();
        let selfv = Val::from_isize(&vm, 42).unwrap();
        unsafe { &mut *vm.stack.get() }.push(Val::from_isize(&vm, 43).unwrap());
        unsafe { &mut *vm.stack.get() }.push(Val::from_isize(&vm, 44).unwrap());
        let f = Frame::new(&vm, true, selfv, None, 3, 2);
        assert_eq!(f.var_lookup(0, 0).as_isize(&vm).unwrap(), 42);
        assert_eq!(f.var_lookup(0, 1).as_isize(&vm).unwrap(), 43);
        assert_eq!(f.var_lookup(0, 2).as_isize(&vm).unwrap(), 44);
    }
}
