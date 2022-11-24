#![allow(clippy::new_ret_no_self)]

use std::{cell::SyncUnsafeCell, collections::hash_map::DefaultHasher, hash::Hasher};

use std::gc::Gc;

use crate::vm::{
    core::VM,
    objects::{Class, Obj, ObjType, StaticObjType},
    val::{NotUnboxable, Val, ValKind},
};

/// An instance of a user class.
#[derive(Debug)]
pub struct Inst {
    class: Val,
    inst_vars: SyncUnsafeCell<Vec<Val>>,
}

unsafe impl std::gc::FinalizerOptional for Inst {}

impl Obj for Inst {
    fn dyn_objtype(self: Gc<Self>) -> ObjType {
        ObjType::Inst
    }

    fn get_class(self: Gc<Self>, _: &mut VM) -> Val {
        self.class
    }

    fn num_inst_vars(self: Gc<Self>, vm: &VM) -> usize {
        let cls: Gc<Class> = self.class.downcast(vm).unwrap();
        cls.inst_vars_map.len()
    }

    unsafe fn unchecked_inst_var_get(self: Gc<Self>, vm: &VM, n: usize) -> Val {
        debug_assert!(n < self.num_inst_vars(vm));
        let v = (&*self.inst_vars.get()).get_unchecked(n);
        debug_assert!(v.valkind() != ValKind::ILLEGAL);
        *v
    }

    unsafe fn unchecked_inst_var_set(self: Gc<Self>, vm: &VM, n: usize, v: Val) {
        debug_assert!(n < self.num_inst_vars(vm));
        *(&mut *self.inst_vars.get()).get_unchecked_mut(n) = v;
    }

    fn hashcode(self: Gc<Self>) -> u64 {
        let mut hasher = DefaultHasher::new();
        hasher.write_usize(Gc::as_ptr(&self) as *const _ as usize);
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
        let len = cls.inst_vars_map.len();
        debug_assert!(vm.nil.valkind() != ValKind::ILLEGAL || len == 0);
        Val::from_obj(Inst {
            class,
            inst_vars: SyncUnsafeCell::new(vec![vm.nil; len]),
        })
    }
}
