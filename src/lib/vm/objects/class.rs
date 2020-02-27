#![allow(clippy::new_ret_no_self)]

use std::{collections::HashMap, path::PathBuf, str};

use abgc::Gc;
use abgc_derive::GcLayout;

use crate::vm::{
    core::{VMError, VM},
    objects::{Method, Obj, ObjType, StaticObjType, String_},
    val::{NotUnboxable, Val},
};

#[derive(Debug, GcLayout)]
pub struct Class {
    pub metaclass: bool,
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
        let name: &String_ = self.name.downcast(vm).unwrap();
        let s = name.as_str();

        if !self.metaclass {
            return Val::from_obj(
                vm,
                Class {
                    metaclass: true,
                    name: String_::new(vm, s.to_string() + " class", true),
                    path: self.path.clone(),
                    supercls: Some(vm.cls_cls.clone()),
                    num_inst_vars: self.num_inst_vars,
                    methods: HashMap::clone(&self.methods),
                },
            );
        }
        vm.meta_cls.clone()
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
        vm.nil.clone()
    }
}
