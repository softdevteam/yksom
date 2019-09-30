// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

#![allow(clippy::new_ret_no_self)]

use std::{collections::HashMap, path::PathBuf, str};

use abgc_derive::GcLayout;

use crate::{
    compiler::{cobjects, instrs::Instr},
    vm::{
        objects::{Method, MethodBody, Obj, ObjType, StaticObjType, String_},
        val::{NotUnboxable, Val, ValResult},
        vm::{VMError, VM},
    },
};

#[derive(Debug, GcLayout)]
pub struct Class {
    pub name: Val,
    pub path: PathBuf,
    pub supercls: Option<Val>,
    pub num_inst_vars: usize,
    pub methods: HashMap<String, Method>,
    pub blockinfos: Vec<BlockInfo>,
    pub instrs: Vec<Instr>,
    pub consts: Vec<Val>,
    pub sends: Vec<(String, usize)>,
}

/// Minimal information about a SOM block.
#[derive(Debug)]
pub struct BlockInfo {
    pub bytecode_off: usize,
    pub bytecode_end: usize,
    pub num_params: usize,
    pub num_vars: usize,
}

impl Obj for Class {
    fn dyn_objtype(&self) -> ObjType {
        ObjType::Class
    }

    fn get_class(&self, vm: &VM) -> Val {
        vm.cls_cls.clone()
    }
}

impl NotUnboxable for Class {}

impl StaticObjType for Class {
    fn static_objtype() -> ObjType {
        ObjType::Class
    }
}

impl Class {
    pub fn from_ccls(vm: &VM, ccls: cobjects::Class) -> ValResult {
        let supercls = match ccls.supercls {
            Some(ref x) => match x.as_str() {
                "Block" => Some(vm.block_cls.clone()),
                "Boolean" => Some(vm.bool_cls.clone()),
                "nil" => None,
                _ => unimplemented!(),
            },
            None => Some(vm.obj_cls.clone()),
        };

        let mut inst_vars = Vec::with_capacity(ccls.num_inst_vars);
        inst_vars.resize(ccls.num_inst_vars, Val::illegal());

        let mut methods = HashMap::with_capacity(ccls.methods.len());
        for cmeth in ccls.methods.into_iter() {
            let body = match cmeth.body {
                cobjects::MethodBody::Primitive(p) => MethodBody::Primitive(p),
                cobjects::MethodBody::User {
                    num_vars,
                    bytecode_off,
                } => MethodBody::User {
                    num_vars,
                    bytecode_off,
                },
            };
            let meth = Method {
                name: cmeth.name.clone(),
                body,
            };
            methods.insert(cmeth.name, meth);
        }

        let blockinfos = ccls
            .blocks
            .into_iter()
            .map(|b| BlockInfo {
                bytecode_off: b.bytecode_off,
                bytecode_end: b.bytecode_end,
                num_params: b.num_params,
                num_vars: b.num_vars,
            })
            .collect();

        let mut consts = Vec::with_capacity(ccls.consts.len());
        for c in ccls.consts {
            consts.push(match c {
                cobjects::Const::String(s) => String_::new(vm, s),
                cobjects::Const::Int(i) => vtry!(Val::from_isize(vm, i)),
            });
        }
        ValResult::from_val(Val::from_obj(
            vm,
            Class {
                name: String_::new(vm, ccls.name),
                path: ccls.path,
                supercls,
                num_inst_vars: ccls.num_inst_vars,
                methods,
                blockinfos,
                instrs: ccls.instrs,
                consts,
                sends: ccls.sends,
            },
        ))
    }

    pub fn name(&self, _: &VM) -> ValResult {
        ValResult::from_val(self.name.clone())
    }

    pub fn get_method(&self, vm: &VM, msg: &str) -> Result<(Val, &Method), Box<VMError>> {
        self.methods
            .get(msg)
            .map(|x| Ok((Val::recover(self), x)))
            .unwrap_or_else(|| match &self.supercls {
                Some(scls) => scls.downcast::<Class>(vm)?.get_method(vm, msg),
                None => Err(Box::new(VMError::UnknownMethod(msg.to_owned()))),
            })
    }

    pub fn blockinfo(&self, blockinfo_off: usize) -> &BlockInfo {
        &self.blockinfos[blockinfo_off]
    }
}
