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

use abgc::Gc;
use abgc_derive::GcLayout;

use crate::vm::{
    core::{VMError, VM},
    objects::{Method, Obj, ObjType, StaticObjType},
    val::{NotUnboxable, Val},
};

#[derive(Debug, GcLayout)]
pub struct Class {
    pub name: Val,
    pub path: PathBuf,
    pub supercls: Option<Val>,
    pub num_inst_vars: usize,
    pub methods: HashMap<String, Gc<Method>>,
    pub sends: Vec<(String, usize)>,
    pub strings: Vec<Val>,
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
    pub fn name(&self, _: &VM) -> Result<Val, Box<VMError>> {
        Ok(self.name.clone())
    }

    pub fn get_method(&self, vm: &VM, msg: &str) -> Result<(Val, Gc<Method>), Box<VMError>> {
        self.methods
            .get(msg)
            .map(|x| Ok((Val::recover(self), Gc::clone(x))))
            .unwrap_or_else(|| match &self.supercls {
                Some(scls) => scls.downcast::<Class>(vm)?.get_method(vm, msg),
                None => Err(Box::new(VMError::UnknownMethod(msg.to_owned()))),
            })
    }
}
