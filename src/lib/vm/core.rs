//! The core part of the interpreter.

use std::{
    cell::UnsafeCell,
    collections::HashMap,
    path::{Path, PathBuf},
    process,
};

use abgc::{Gc, GcLayout};

use crate::{
    compiler::{
        compile,
        instrs::{Builtin, Instr, Primitive},
    },
    vm::{
        objects::{
            Block, BlockInfo, Class, Double, Inst, Int, Method, MethodBody, ObjType, String_,
        },
        somstack::SOMStack,
        val::Val,
    },
};

pub const SOM_EXTENSION: &str = "som";

#[derive(Debug, PartialEq)]
pub enum VMError {
    /// A value which can't be represented in an `isize`.
    CantRepresentAsBigInt,
    /// A value which can't be represented in an `f64`.
    CantRepresentAsDouble,
    /// A value which can't be represented in an `isize`.
    CantRepresentAsIsize,
    /// A value which can't be represented in an `usize`.
    CantRepresentAsUsize,
    DivisionByZero,
    /// A value which is mathematically undefined.
    DomainError,
    /// The VM is trying to exit.
    Exit,
    /// Tried to perform a `Val::downcast` operation on a non-boxed `Val`. Note that `expected`
    /// and `got` can reference the same `ObjType`.
    GcBoxTypeError {
        expected: ObjType,
        got: ObjType,
    },
    /// Tried to access a global before it being initialised.
    InvalidSymbol,
    /// Tried to do a shl or shr with a value below zero.
    NegativeShift,
    /// A specialised version of TypeError, because SOM has more than one number type (and casts
    /// between them as necessary) so the `expected` field of `TypeError` doesn't quite work.
    NotANumber {
        got: ObjType,
    },
    /// Something went wrong when trying to execute a primitive.
    PrimitiveError,
    /// Tried to do a shl that would overflow memory and/or not fit in the required integer size.
    ShiftTooBig,
    /// The given string cannot be parsed to produce a number.
    ParseError,
    /// A dynamic type error.
    TypeError {
        expected: ObjType,
        got: ObjType,
    },
    /// An unknown method.
    UnknownMethod(String),
}

#[derive(Debug)]
/// The (internal) result of a SOM send.
enum SendReturn {
    /// A closure wants to perform a return *n* frames up the call stack.
    ClosureReturn(usize),
    /// An error has occurred.
    Err(Box<VMError>),
    /// A return value has been left at the appropriate place on the SOM stack.
    Val,
}

/// A convenience macro for use in the `exec_*` functions.
macro_rules! stry {
    ($elem:expr) => {{
        let e = $elem;
        match e {
            Ok(o) => o,
            Err(e) => return SendReturn::Err(e),
        }
    }};
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
    pub meta_cls: Val,
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
    globals: UnsafeCell<HashMap<usize, Val>>,
    inline_caches: UnsafeCell<Vec<Option<(Val, Gc<Method>)>>>,
    instrs: UnsafeCell<Vec<Instr>>,
    sends: UnsafeCell<Vec<(String, usize)>>,
    /// reverse_sends is an optimisation allowing us to reuse sends: it maps a send `(String,
    /// usize)` to a `usize` where the latter represents the index of the send in `sends`.
    reverse_sends: UnsafeCell<HashMap<(String, usize), usize>>,
    stack: UnsafeCell<SOMStack>,
    strings: UnsafeCell<Vec<Val>>,
    symbols: UnsafeCell<Vec<Val>>,
    /// reverse_strings is an optimisation allowing us to reuse strings: it maps a `String to a
    /// `usize` where the latter represents the index of the string in `strings`.
    reverse_strings: UnsafeCell<HashMap<String, usize>>,
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
            meta_cls: Val::illegal(),
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
            globals: UnsafeCell::new(HashMap::new()),
            inline_caches: UnsafeCell::new(Vec::new()),
            instrs: UnsafeCell::new(Vec::new()),
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
        vm.meta_cls = vm.init_builtin_class("Metaclass", false);
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
        unsafe { &mut *vm.globals.get() }.insert(
            vm.add_symbol("system".to_string()),
            Inst::new(&vm, vm.system_cls.clone()),
        );
        vm.false_ = Inst::new(&vm, vm.false_cls.clone());
        vm.system = Inst::new(&vm, vm.system_cls.clone());
        vm.true_ = Inst::new(&vm, vm.true_cls.clone());

        vm
    }

    /// Compile the file at `path`. `inst_vars_allowed` should be set to `false` only for those
    /// builtin classes which do not lead to run-time instances of `Inst`.
    pub fn compile(&self, path: &Path, inst_vars_allowed: bool) -> Val {
        let cls = compile(self, path);
        if !inst_vars_allowed && cls.num_inst_vars > 0 {
            panic!("No instance vars allowed in {}", path.to_str().unwrap());
        }
        Val::from_obj(self, cls)
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
        let idx = self.add_symbol(name.to_string());
        unsafe { &mut *self.globals.get() }
            .entry(idx)
            .or_insert(val.clone());

        val
    }

    /// Inform the user of the error string `error` and then exit.
    pub fn error(&self, error: &str) -> ! {
        eprintln!("{}", error);
        process::exit(1);
    }

    /// Send the message `msg` to the receiver `rcv` with arguments `args`.
    pub fn send(&self, rcv: Val, msg: &str, args: Vec<Val>) -> Result<Val, Box<VMError>> {
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
                let r = self.exec_user(rcv, bytecode_off);
                self.frame_pop();
                match r {
                    SendReturn::ClosureReturn(_) => unimplemented!(),
                    SendReturn::Err(e) => Err(Box::new(*e)),
                    SendReturn::Val => Ok(unsafe { &mut *self.stack.get() }.pop()),
                }
            }
        }
    }

    /// Execute a SOM method. Note that the frame for this method must have been created *before*
    /// calling this function.
    fn exec_user(&self, rcv: Val, meth_start_pc: usize) -> SendReturn {
        let mut pc = meth_start_pc;
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
                        blkinfo_off,
                        Gc::clone(&self.current_frame().closure),
                        num_params,
                    ));
                    pc = bytecode_end;
                }
                Instr::Builtin(b) => {
                    unsafe { &mut *self.stack.get() }.push(match b {
                        Builtin::Nil => self.nil.clone(),
                        Builtin::False => self.false_.clone(),
                        Builtin::System => self.system.clone(),
                        Builtin::True => self.true_.clone(),
                    });
                    pc += 1;
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
                Instr::Global(symbol_off) => {
                    debug_assert!(unsafe { &*self.symbols.get() }.len() > symbol_off);
                    if let Some(global) = unsafe { &mut *self.globals.get() }.get(&symbol_off) {
                        unsafe { &mut *self.stack.get() }.push(global.clone());
                    } else {
                        return SendReturn::Err(Box::new(VMError::InvalidSymbol));
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
                    unsafe { &mut *self.stack.get() }.push(stry!(Val::from_isize(self, i)));
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
                    let (rcv, nargs, meth) = {
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

                    self.current_frame()
                        .set_sp(unsafe { &*self.stack.get() }.len() - nargs);
                    let r = match meth.body {
                        MethodBody::Primitive(Primitive::Restart) => {
                            unsafe { &mut *self.stack.get() }.truncate(stack_start);
                            pc = meth_start_pc;
                            continue;
                        }
                        MethodBody::Primitive(p) => self.exec_primitive(p, rcv),
                        MethodBody::User {
                            num_vars,
                            bytecode_off,
                            max_stack,
                        } => {
                            if unsafe { &*self.stack.get() }.remaining_capacity() < max_stack {
                                panic!("Not enough stack space to execute method.");
                            }
                            let nframe =
                                Frame::new(self, true, rcv.clone(), None, num_vars, *nargs);
                            unsafe { &mut *self.frames.get() }.push(nframe);
                            let r = self.exec_user(rcv, bytecode_off);
                            self.frame_pop();
                            r
                        }
                    };
                    match r {
                        SendReturn::ClosureReturn(d) => {
                            if d > 0 {
                                return SendReturn::ClosureReturn(d - 1);
                            }
                        }
                        SendReturn::Err(e) => {
                            return SendReturn::Err(e);
                        }
                        SendReturn::Val => (),
                    }
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
            Primitive::FromString => {
                unsafe { &mut *self.stack.get() }.push(stry!(Int::from_str(
                    self,
                    unsafe { &mut *self.stack.get() }.pop()
                )));
                SendReturn::Val
            }
            Primitive::Global => {
                let name = unsafe { &mut *self.stack.get() }.pop();
                let as_string: &String_ = stry!(name.downcast(self));
                let s = as_string.as_str();

                if let Some(i) = unsafe { &mut *self.reverse_symbols.get() }.get(s) {
                    if let Some(val) = unsafe { &mut *self.globals.get() }.get(&i) {
                        unsafe { &mut *self.stack.get() }.push(val.clone());
                        return SendReturn::Val;
                    }
                }
                SendReturn::Err(Box::new(VMError::InvalidSymbol))
            }
            Primitive::GlobalPut => {
                let value = unsafe { &mut *self.stack.get() }.pop();
                let name = unsafe { &mut *self.stack.get() }.pop();
                let as_string: &String_ = stry!(name.downcast(self));
                let s = as_string.as_str();

                if let Some(i) = unsafe { &mut *self.reverse_symbols.get() }.get(s) {
                    unsafe { &mut *self.globals.get() }.insert(*i, value.clone());
                    unsafe { &mut *self.stack.get() }.push(value);
                }
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
                let r = self.exec_user(rcv.clone(), bytecode_off);
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

    /// Push `instr` to the end of the current vector of instructions.
    pub fn instrs_push(&self, instr: Instr) {
        unsafe { &mut *self.instrs.get() }.push(instr);
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

    /// Add the symbols `s` to the VM, returning its index. Note that symbols (like strings) are reused, so indexes
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
        vars.resize_with(num_vars, || Val::illegal());

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
            meta_cls: Val::illegal(),
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
            globals: UnsafeCell::new(HashMap::new()),
            inline_caches: UnsafeCell::new(Vec::new()),
            instrs: UnsafeCell::new(Vec::new()),
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
