#![allow(clippy::new_ret_no_self)]

use std::{cell::UnsafeCell, collections::hash_map::DefaultHasher, hash::Hasher};

use rboehm::Gc;

use crate::vm::{
    core::VM,
    objects::{Class, Obj, ObjType, StaticObjType},
    val::{NotUnboxable, Val, ValKind},
};

/// An instance of a user class.
#[derive(Debug)]
pub struct Inst {
    class: Val,
    inst_vars: UnsafeCell<Vec<Val>>,
}

impl Obj for Inst {
    fn dyn_objtype(self: Gc<Self>) -> ObjType {
        ObjType::Inst
    }

    fn get_class(self: Gc<Self>, _: &mut VM) -> Val {
        self.class
    }

    fn num_inst_vars(self: Gc<Self>) -> usize {
        unsafe { &*self.inst_vars.get() }.len()
    }

    unsafe fn unchecked_inst_var_get(self: Gc<Self>, n: usize) -> Val {
        let inst_vars = &mut *self.inst_vars.get();
        debug_assert!(n < inst_vars.len());
        debug_assert!(inst_vars[n].valkind() != ValKind::ILLEGAL);
        inst_vars[n]
    }

    unsafe fn unchecked_inst_var_set(self: Gc<Self>, n: usize, v: Val) {
        let inst_vars = &mut *self.inst_vars.get();
        debug_assert!(n < inst_vars.len());
        inst_vars[n] = v;
    }

    fn hashcode(self: Gc<Self>) -> u64 {
        let mut hasher = DefaultHasher::new();
        hasher.write_usize(Gc::into_raw(self) as *const _ as usize);
        hasher.finish()
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
        let cls: Gc<Class> = class.downcast(vm).unwrap();
        let mut inst_vars = Vec::with_capacity(cls.inst_vars_map.len());
        inst_vars.resize(cls.inst_vars_map.len(), vm.nil);
        let inst = Inst {
            class,
            inst_vars: UnsafeCell::new(inst_vars),
        };
        Val::from_obj(vm, inst)
    }
}
