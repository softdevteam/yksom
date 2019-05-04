// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

use std::{
    mem::size_of,
    ops::RangeBounds,
    path::{Path, PathBuf},
    process,
    vec::Drain,
};

use static_assertions::const_assert_eq;

use super::objects::{Class, Inst, MethodBody, ObjType, String_, Val};
use crate::compiler::{
    compile,
    instrs::{Instr, Primitive, SELF_VAR},
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
    /// A dynamic type error.
    TypeError { expected: ObjType, got: ObjType },
    /// An unknown method.
    UnknownMethod(String),
}

pub struct VM {
    classpath: Vec<String>,
    pub nil: Val,
    pub cls_cls: Val,
    pub obj_cls: Val,
    pub str_cls: Val,
}

impl VM {
    pub fn new(classpath: Vec<String>) -> Self {
        let mut vm = VM {
            classpath,
            nil: Val::illegal(),
            cls_cls: Val::illegal(),
            obj_cls: Val::illegal(),
            str_cls: Val::illegal(),
        };
        // XXX wrong class!
        vm.nil = Inst::new(&vm, Val::illegal());
        vm.obj_cls = vm.init_builtin_class("Object");
        vm.cls_cls = vm.init_builtin_class("Class");
        vm.str_cls = vm.init_builtin_class("String");

        vm
    }

    /// Compile the file at `path`.
    pub fn compile(&self, path: &Path) -> Val {
        let ccls = compile(path);
        Class::from_ccls(self, ccls)
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
    fn init_builtin_class(&self, name: &str) -> Val {
        let path = self
            .find_class(name)
            .unwrap_or_else(|_| panic!("Can't find builtin class '{}'", name));
        self.compile(&path)
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
            MethodBody::User(pc) => {
                let meth_cls_tobj = meth_cls_val.tobj(self)?;
                let meth_cls: &Class = meth_cls_tobj.cast()?;
                self.exec_user(meth_cls, pc, rcv, args)
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
        }
    }

    fn exec_user(
        &self,
        cls: &Class,
        mut pc: usize,
        rcv: Val,
        _args: &[Val],
    ) -> Result<Val, VMError> {
        let mut frame = Frame::new(rcv);
        while pc < cls.instrs.len() {
            match cls.instrs[pc] {
                Instr::Const(coff) => {
                    frame.stack_push(cls.consts[coff].clone());
                    pc += 1;
                }
                Instr::Send(moff) => {
                    let (ref name, nargs) = &cls.sends[moff];
                    let args = frame
                        .stack_drain(frame.stack_len() - nargs..)
                        .collect::<Vec<_>>();
                    let rcv = frame.stack_pop();
                    let r = self.send(rcv, &name, &args)?;
                    frame.stack_push(r);
                    pc += 1;
                }
                Instr::Return => {
                    return Ok(frame.stack_pop());
                }
                Instr::VarLookup(n) => {
                    let val = frame.var_lookup(n);
                    frame.stack_push(val);
                    pc += 1;
                }
                Instr::VarSet(n) => {
                    let val = frame.stack_pop();
                    frame.var_set(n, val);
                    pc += 1;
                }
                _ => unimplemented!(),
            }
        }
        Err(VMError::Exit)
    }
}

pub struct Frame {
    stack: Vec<Val>,
    vars: Vec<Val>,
}

impl Frame {
    fn new(self_val: Val) -> Self {
        const_assert_eq!(SELF_VAR, 0);
        Frame {
            stack: Vec::new(),
            vars: vec![self_val],
        }
    }

    fn stack_len(&self) -> usize {
        self.stack.len()
    }

    fn stack_push(&mut self, v: Val) {
        self.stack.push(v);
    }

    fn stack_pop(&mut self) -> Val {
        self.stack.pop().unwrap()
    }

    fn stack_drain<R>(&mut self, range: R) -> Drain<'_, Val>
    where
        R: RangeBounds<usize>,
    {
        self.stack.drain(range)
    }

    fn var_lookup(&mut self, var: u32) -> Val {
        debug_assert!(size_of::<usize>() > size_of::<u32>());
        self.vars[var as usize].clone()
    }

    fn var_set(&mut self, var: u32, val: Val) {
        debug_assert!(size_of::<usize>() > size_of::<u32>());
        self.vars[var as usize] = val;
    }
}

#[cfg(test)]
impl VM {
    pub fn new_no_bootstrap() -> Self {
        VM {
            classpath: vec![],
            nil: Val::illegal(),
            cls_cls: Val::illegal(),
            obj_cls: Val::illegal(),
            str_cls: Val::illegal(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{super::objects::Int, *};

    #[test]
    fn test_frame() {
        let vm = VM::new_no_bootstrap();
        let v = Int::from_isize(&vm, 42).unwrap();
        let mut f = Frame::new(v);
        assert_eq!(f.var_lookup(SELF_VAR).as_isize(&vm), Ok(42));
    }
}
