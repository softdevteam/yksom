#![allow(clippy::new_ret_no_self)]

use std::{cell::Cell, collections::hash_map::DefaultHasher, hash::Hasher};

use std::gc::Gc;

use crate::vm::{
    core::VM,
    function::Function,
    objects::{Obj, ObjType, StaticObjType, String_},
    val::{NotUnboxable, Val},
};

#[derive(Debug)]
pub struct Method {
    sig: Cell<Val>,
    pub func: Function,
}

impl Obj for Method {
    fn dyn_objtype(self: Gc<Self>) -> ObjType {
        ObjType::Method
    }

    fn get_class(self: Gc<Self>, vm: &mut VM) -> Val {
        vm.method_cls
    }

    fn hashcode(self: Gc<Self>) -> u64 {
        let mut hasher = DefaultHasher::new();
        hasher.write_usize(Gc::into_raw(self) as *const _ as usize);
        hasher.finish()
    }
}

impl NotUnboxable for Method {}

impl StaticObjType for Method {
    fn static_objtype() -> ObjType {
        ObjType::Method
    }
}

impl Method {
    pub fn new(_: &VM, sig: Val, func: Function) -> Val {
        Val::from_obj(Method {
            sig: Cell::new(sig),
            func,
        })
    }

    pub fn bootstrap(&self, vm: &VM) {
        self.sig
            .get()
            .downcast::<String_>(vm)
            .unwrap()
            .set_cls(vm.sym_cls);
    }

    pub fn sig(&self, _: &VM) -> Val {
        self.sig.get()
    }
}
