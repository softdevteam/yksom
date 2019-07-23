// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

use std::{
    cell::UnsafeCell,
    path::{Path, PathBuf},
    process, ptr,
};

use abgc::{Gc, GcLayout};

use super::objects::{Block, Class, Inst, MethodBody, ObjType, String_, Val};
use crate::compiler::{
    compile,
    instrs::{Builtin, Instr, Primitive},
};

pub const SOM_EXTENSION: &str = "som";

#[derive(Debug, PartialEq)]
pub enum VMError {
    /// A number which can't be represented in an `isize`.
    CantRepresentAsIsize,
    /// A number which can't be represented in an `usize`.
    CantRepresentAsUsize,
    /// The VM is trying to exit.
    Exit,
    /// Tried to perform a `Val::gcbox_cast` operation on a non-boxed `Val`. Note that `expected`
    /// and `got` can reference the same `ObjType`.
    GcBoxTypeError { expected: ObjType, got: ObjType },
    /// Percolate a non-local return up the call stack.
    Return(usize, Val),
    /// A dynamic type error.
    TypeError { expected: ObjType, got: ObjType },
    /// Tried to read from a local variable that hasn't had a value assigned to it yet.
    UnassignedVar(usize),
    /// An unknown method.
    UnknownMethod(String),
}

pub struct VM {
    classpath: Vec<String>,
    pub block_cls: Val,
    pub bool_cls: Val,
    pub cls_cls: Val,
    pub false_cls: Val,
    pub nil_cls: Val,
    pub obj_cls: Val,
    pub str_cls: Val,
    pub true_cls: Val,
    pub false_: Val,
    pub nil: Val,
    pub true_: Val,
    frames: UnsafeCell<Vec<Gc<Frame>>>,
}

impl VM {
    pub fn new(classpath: Vec<String>) -> Self {
        // The bootstrapping phase is delicate: we need to bootstrap the Object, Class, and Nil
        // classes before we can create basic objects like nil. We thus perform bootstrapping in
        // two phases: the "very delicate" phase (with very strict rules on what is possible)
        // followed by the "slightly delicate phase" (with looser, but still fairly strict, rules
        // on what is possible).
        //
        let mut vm = VM {
            classpath,
            block_cls: Val::illegal(),
            bool_cls: Val::illegal(),
            cls_cls: Val::illegal(),
            false_cls: Val::illegal(),
            nil_cls: Val::illegal(),
            obj_cls: Val::illegal(),
            str_cls: Val::illegal(),
            true_cls: Val::illegal(),
            false_: Val::illegal(),
            nil: Val::illegal(),
            true_: Val::illegal(),
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
        vm.bool_cls = vm.init_builtin_class("Boolean", false);
        vm.false_cls = vm.init_builtin_class("False", false);
        vm.str_cls = vm.init_builtin_class("String", false);
        vm.true_cls = vm.init_builtin_class("True", false);
        vm.false_ = Inst::new(&vm, vm.false_cls.clone());
        vm.true_ = Inst::new(&vm, vm.true_cls.clone());

        vm
    }

    /// Compile the file at `path`. `inst_vars_allowed` should be set to `false` only for those
    /// builtin classes which do not lead to run-time instances of `Inst`.
    pub fn compile(&self, path: &Path, inst_vars_allowed: bool) -> Val {
        let ccls = compile(path);
        if !inst_vars_allowed && ccls.num_inst_vars > 0 {
            panic!("No instance vars allowed in {}", path.to_str().unwrap());
        }
        Class::from_ccls(self, ccls).unwrap_or_else(|e| {
            panic!(
                "Fatal compilation error for {}: {:?}",
                path.to_str().unwrap(),
                e
            )
        })
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
        self.compile(&path, inst_vars_allowed)
    }

    /// Inform the user of the error string `error` and then exit.
    pub fn error(&self, error: &str) -> ! {
        eprintln!("{}", error);
        process::exit(1);
    }

    /// Send the message `msg` to the receiver `rcv` with arguments `args`.
    pub fn send(&self, rcv: Val, msg: &str, args: &[Val]) -> Result<Val, VMError> {
        let cls_tobj = rcv.tobj(self)?.get_class(self).tobj(self)?;
        let cls: &Class = cls_tobj.cast()?;
        let (meth_cls_val, meth) = cls.get_method(self, msg)?;

        match meth.body {
            MethodBody::Primitive(p) => self.exec_primitive(p, rcv, args),
            MethodBody::User {
                num_vars,
                bytecode_off,
            } => {
                let meth_cls_tobj = meth_cls_val.tobj(self)?;
                let meth_cls: &Class = meth_cls_tobj.cast()?;
                self.exec_user(meth_cls, bytecode_off, rcv, None, num_vars, args)
            }
        }
    }

    fn exec_primitive(&self, prim: Primitive, rcv: Val, args: &[Val]) -> Result<Val, VMError> {
        match prim {
            Primitive::Class => {
                let rcv_tobj = rcv.tobj(self)?;
                Ok(rcv_tobj.get_class(self))
            }
            Primitive::Concatenate => {
                let rcv_tobj = rcv.tobj(self)?;
                let rcv_str: &String_ = rcv_tobj.cast()?;
                rcv_str.concatenate(self, args[0].clone())
            }
            Primitive::Name => rcv.tobj(self)?.cast::<Class>()?.name(self),
            Primitive::New => {
                assert_eq!(args.len(), 0);
                Ok(Inst::new(self, rcv))
            }
            Primitive::PrintLn => {
                // XXX println should be on System, not on string
                let str_tobj = rcv.tobj(self)?;
                let str_: &String_ = str_tobj.cast()?;
                println!("{}", str_.as_str());
                Ok(rcv)
            }
            Primitive::Value => {
                let rcv_tobj = rcv.tobj(self)?;
                let rcv_blk: &Block = rcv_tobj.cast()?;
                let blk_cls_tobj = rcv_blk.blockinfo_cls.tobj(self)?;
                let blk_cls: &Class = blk_cls_tobj.cast()?;
                let blkinfo = blk_cls.blockinfo(rcv_blk.blockinfo_off);
                self.exec_user(
                    blk_cls,
                    blkinfo.bytecode_off,
                    rcv,
                    Some(Gc::clone(&rcv_blk.parent_closure)),
                    blkinfo.num_vars,
                    &[],
                )
            }
        }
    }

    fn exec_user(
        &self,
        cls: &Class,
        mut pc: usize,
        rcv: Val,
        parent_closure: Option<Gc<Closure>>,
        num_vars: usize,
        args: &[Val],
    ) -> Result<Val, VMError> {
        let frame = Gc::new(Frame::new(
            self,
            parent_closure,
            num_vars,
            rcv.clone(),
            args,
        ));
        unsafe { &mut *self.frames.get() }.push(Gc::clone(&frame));
        while pc < cls.instrs.len() {
            match cls.instrs[pc] {
                Instr::Block(blkinfo_off) => {
                    frame.stack_push(Block::new(
                        self,
                        Val::recover(cls),
                        blkinfo_off,
                        Gc::clone(&frame.closure),
                    ));
                    pc = cls.blockinfo(blkinfo_off).bytecode_end;
                }
                Instr::Builtin(b) => {
                    frame.stack_push(match b {
                        Builtin::Nil => self.nil.clone(),
                        Builtin::False => self.false_.clone(),
                        Builtin::True => self.true_.clone(),
                    });
                    pc += 1;
                }
                Instr::Const(coff) => {
                    frame.stack_push(cls.consts[coff].clone());
                    pc += 1;
                }
                Instr::InstVarLookup(n) => {
                    let inst: &Inst = rcv.gcbox_cast(self).unwrap();
                    frame.stack_push(inst.inst_var_lookup(n));
                    pc += 1;
                }
                Instr::InstVarSet(n) => {
                    let inst: &Inst = rcv.gcbox_cast(self).unwrap();
                    inst.inst_var_set(n, frame.stack_peek());
                    pc += 1;
                }
                Instr::Pop => {
                    frame.stack_pop();
                    pc += 1;
                }
                Instr::Send(moff) => {
                    let (ref name, nargs) = &cls.sends[moff];
                    let args = frame.stack_drain_rev(frame.stack_len() - nargs);
                    let rcv = frame.stack_pop();
                    let r = match self.send(rcv, &name, &args) {
                        Ok(r) => r,
                        Err(VMError::Return(depth, val)) => {
                            if depth == 0 {
                                val
                            } else {
                                unsafe { &mut *self.frames.get() }.pop();
                                return Err(VMError::Return(depth - 1, val));
                            }
                        }
                        Err(e) => {
                            unsafe { &mut *self.frames.get() }.pop();
                            return Err(e);
                        }
                    };
                    frame.stack_push(r);
                    pc += 1;
                }
                Instr::Return(closure_depth) => {
                    let v = frame.stack_pop();
                    if closure_depth == 0 {
                        unsafe { &mut *self.frames.get() }.pop();
                        return Ok(v);
                    } else {
                        // We want to do a non-local return. Before we attempt that, we need to
                        // check that the block hasn't escaped its function (and we know we're in a
                        // block because only a block can attempt a non-local return).
                        // Fortunately, the `closure` pointer in a frame is a perfect proxy for
                        // determining this: if this frame's (i.e. block's!) parent closure is not
                        // consistent with the frame stack, then the block has escaped.
                        let parent_closure = frame.closure(closure_depth);
                        for (frame_depth, pframe) in
                            unsafe { &*self.frames.get() }.iter().rev().enumerate()
                        {
                            if Gc::ptr_eq(&parent_closure, &pframe.closure) {
                                return Err(VMError::Return(frame_depth, v));
                            }
                        }
                        panic!("Return from escaped block");
                    }
                }
                Instr::VarLookup(d, n) => {
                    let val = frame.var_lookup(d, n)?;
                    frame.stack_push(val);
                    pc += 1;
                }
                Instr::VarSet(d, n) => {
                    let val = frame.stack_peek();
                    frame.var_set(d, n, val);
                    pc += 1;
                }
            }
        }
        Err(VMError::Exit)
    }
}

#[derive(Debug)]
pub struct Frame {
    stack: UnsafeCell<Vec<Val>>,
    closure: Gc<Closure>,
}

impl GcLayout for Frame {
    fn layout(&self) -> std::alloc::Layout {
        std::alloc::Layout::new::<Self>()
    }
}

impl Frame {
    fn new(
        _: &VM,
        parent_closure: Option<Gc<Closure>>,
        num_vars: usize,
        self_val: Val,
        args: &[Val],
    ) -> Self {
        let mut vars = Vec::new();
        vars.resize(num_vars, Val::illegal());
        // The VM makes some strong assumptions about variables: that the first variable is
        // "self" and that arguments 1..n+1 are the first n arguments to the method in
        // reverse order.
        vars[0] = self_val;
        for (i, arg) in args.iter().enumerate() {
            vars[i + 1] = arg.clone();
        }

        Frame {
            stack: UnsafeCell::new(Vec::new()),
            closure: Gc::new(Closure::new(parent_closure, vars)),
        }
    }

    fn stack_len(&self) -> usize {
        unsafe { &*self.stack.get() }.len()
    }

    fn stack_push(&self, v: Val) {
        unsafe { &mut *self.stack.get() }.push(v);
    }

    fn stack_peek(&self) -> Val {
        let stack = unsafe { &*self.stack.get() };
        debug_assert!(stack.len() > 0);
        let i = stack.len() - 1;
        unsafe { stack.get_unchecked(i) }.clone()
    }

    fn stack_pop(&self) -> Val {
        // Since we know that there will be at least one element in the stack, we can use our own
        // simplified version of pop() which avoids a branch and the wrapping of values in an
        // Option.
        unsafe {
            let stack = &mut *self.stack.get();
            debug_assert!(stack.len() > 0);
            let i = stack.len() - 1;
            let v = ptr::read(stack.get_unchecked(i));
            stack.set_len(i);
            v
        }
    }

    fn stack_drain_rev(&self, start: usize) -> Vec<Val> {
        unsafe { &mut *self.stack.get() }
            .drain(start..)
            .rev()
            .collect()
    }

    fn var_lookup(&self, depth: usize, var: usize) -> Result<Val, VMError> {
        let cl = self.closure(depth);
        let v = cl.get_var(var);
        if v.is_illegal() {
            Err(VMError::UnassignedVar(var))
        } else {
            Ok(v.clone())
        }
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
            bool_cls: Val::illegal(),
            cls_cls: Val::illegal(),
            false_cls: Val::illegal(),
            obj_cls: Val::illegal(),
            nil_cls: Val::illegal(),
            str_cls: Val::illegal(),
            true_cls: Val::illegal(),
            false_: Val::illegal(),
            nil: Val::illegal(),
            true_: Val::illegal(),
            frames: UnsafeCell::new(Vec::new()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{super::objects::Int, *};

    #[test]
    fn test_frame() {
        let vm = VM::new_no_bootstrap();
        let selfv = Int::from_isize(&vm, 42).unwrap();
        let v1 = Int::from_isize(&vm, 43).unwrap();
        let v2 = Int::from_isize(&vm, 44).unwrap();
        let f = Frame::new(&vm, None, 4, selfv, &[v1, v2]);
        assert_eq!(f.var_lookup(0, 0).unwrap().as_isize(&vm).unwrap(), 42);
        assert_eq!(f.var_lookup(0, 1).unwrap().as_isize(&vm).unwrap(), 43);
        assert_eq!(f.var_lookup(0, 2).unwrap().as_isize(&vm).unwrap(), 44);
        assert!(f.var_lookup(0, 3).is_err());
    }
}
