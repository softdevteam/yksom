#![allow(clippy::new_ret_no_self)]

use std::{collections::hash_map::DefaultHasher, hash::Hasher};

use rboehm::Gc;

use crate::vm::{
    core::{Closure, VM},
    function::Function,
    objects::{Obj, ObjType, StaticObjType},
    val::{NotUnboxable, Val},
};

#[derive(Debug)]
pub struct Block {
    /// This `Block`'s `self` val. XXX This should probably be part of the corresponding closure's
    /// variables.
    pub inst: Val,
    pub func: Gc<Function>,
    pub parent_closure: Gc<Closure>,
}

impl Obj for Block {
    fn dyn_objtype(self: Gc<Self>) -> ObjType {
        ObjType::Block
    }

    fn get_class(self: Gc<Self>, vm: &mut VM) -> Val {
        match self.func.num_params() {
            0 => vm.block1_cls,
            1 => vm.block2_cls,
            2 => vm.block3_cls,
            _ => unreachable!(),
        }
    }

    fn hashcode(self: Gc<Self>) -> u64 {
        let mut hasher = DefaultHasher::new();
        hasher.write_usize(Gc::into_raw(self) as *const _ as usize);
        hasher.finish()
    }
}

impl NotUnboxable for Block {}

impl StaticObjType for Block {
    fn static_objtype() -> ObjType {
        ObjType::Block
    }
}

impl Block {
    pub fn new(_: &mut VM, inst: Val, func: Gc<Function>, parent_closure: Gc<Closure>) -> Val {
        Val::from_obj(Block {
            inst,
            func,
            parent_closure,
        })
    }
}
