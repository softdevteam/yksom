#![allow(clippy::new_ret_no_self)]

use std::{collections::hash_map::DefaultHasher, hash::Hasher};

use rboehm::Gc;

use crate::vm::{
    core::{Closure, VM},
    objects::{Method, Obj, ObjType, StaticObjType},
    val::{NotUnboxable, Val},
};

/// Minimal information about a SOM block.
#[derive(Debug)]
pub struct BlockInfo {
    pub bytecode_off: usize,
    pub bytecode_end: usize,
    pub num_params: usize,
    pub num_vars: usize,
    pub max_stack: usize,
    /// The method this block is contained within (note that it does not matter if a block is
    /// nested within other blocks: this refers to a method, not an intermediate block).
    pub method: Option<Gc<Method>>,
}

#[derive(Debug)]
pub struct Block {
    /// This `Block`'s `self` val. XXX This should probably be part of the corresponding closure's
    /// variables.
    pub inst: Val,
    /// Does this Block represent Block, Block2, or Block3?
    pub blockn_cls: Val,
    pub blockinfo_off: usize,
    pub parent_closure: Gc<Closure>,
}

impl Obj for Block {
    fn dyn_objtype(self: Gc<Self>) -> ObjType {
        ObjType::Block
    }

    fn get_class(self: Gc<Self>, _: &mut VM) -> Val {
        self.blockn_cls
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
    pub fn new(
        vm: &mut VM,
        inst: Val,
        blockinfo_off: usize,
        parent_closure: Gc<Closure>,
        num_params: usize,
    ) -> Val {
        let blockn_cls = match num_params {
            0 => vm.block1_cls,
            1 => vm.block2_cls,
            2 => vm.block3_cls,
            _ => unimplemented!(),
        };

        Val::from_obj(Block {
            inst,
            blockn_cls,
            blockinfo_off,
            parent_closure,
        })
    }
}
