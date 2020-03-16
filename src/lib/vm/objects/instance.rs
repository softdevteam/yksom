#![allow(clippy::new_ret_no_self)]

use std::cell::UnsafeCell;

use abgc_derive::GcLayout;

use crate::vm::{
    core::VM,
    objects::{Class, Obj, ObjType, StaticObjType},
    val::{NotUnboxable, Val},
};

/// An instance of a user class.
#[derive(Debug, GcLayout)]
pub struct Inst {
    class: Val,
    inst_vars: UnsafeCell<Vec<Val>>,
}

impl Obj for Inst {
    fn dyn_objtype(&self) -> ObjType {
        ObjType::Inst
    }

    fn get_class(&self, _: &mut VM) -> Val {
        self.class.clone()
    }

    fn inst_var_lookup(&self, n: usize) -> Val {
        let inst_vars = unsafe { &mut *self.inst_vars.get() };
        inst_vars[n].clone()
    }

    fn inst_var_set(&self, n: usize, v: Val) {
        let inst_vars = unsafe { &mut *self.inst_vars.get() };
        inst_vars[n] = v;
    }
}

impl NotUnboxable for Inst {}

impl StaticObjType for Inst {
    fn static_objtype() -> ObjType {
        ObjType::Inst
    }
}

impl Inst {
    pub fn new(vm: &mut VM, class: Val) -> Val {
        let cls: &Class = class.downcast(vm).unwrap();
        let mut inst_vars = Vec::with_capacity(cls.num_inst_vars);
        inst_vars.resize(cls.num_inst_vars, Val::illegal());
        let inst = Inst {
            class,
            inst_vars: UnsafeCell::new(inst_vars),
        };
        Val::from_obj(vm, inst)
    }
}
