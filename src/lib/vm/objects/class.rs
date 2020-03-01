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
    pub class: Option<Val>,
    pub name: Val,
    pub path: PathBuf,
    pub supercls: Option<Val>,
    pub num_inst_vars: usize,
    pub methods: HashMap<String, Gc<Method>>,
}

impl Obj for Class {
    fn dyn_objtype(&self) -> ObjType {
        ObjType::Class
    }

    fn get_class(&self, vm: &VM) -> Val {
        match &self.class {
            Some(cls) => cls.clone(),
            None => vm.meta_cls.clone(),
        }
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

    pub fn get_method(&self, vm: &VM, msg: &str) -> Result<Gc<Method>, Box<VMError>> {
        if self.class == None && self.supercls == None {
            let cls: &Class = vm.cls_cls.downcast(vm).unwrap();
            return cls.get_method(vm, msg);
        }
        self.methods
            .get(msg)
            .map(|x| Ok(Gc::clone(x)))
            .unwrap_or_else(|| match &self.supercls {
                Some(scls) => scls.downcast::<Class>(vm)?.get_method(vm, msg),
                None => Err(Box::new(VMError::UnknownMethod(msg.to_owned()))),
            })
    }

    pub fn superclass(&self, vm: &VM) -> Val {
        if let Some(superclass) = &self.supercls {
            return superclass.clone();
        }
        if self.class == None {
            return vm.cls_cls.clone();
        }
        vm.nil.clone()
    }
}
