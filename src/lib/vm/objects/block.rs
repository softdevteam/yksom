#![allow(clippy::new_ret_no_self)]

use abgc::Gc;
use abgc_derive::GcLayout;

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
}

#[derive(Debug, GcLayout)]
pub struct Block {
    pub method: Gc<Method>,
    /// This `Block`'s `self` val. XXX This should probably be part of the corresponding closure's
    /// variables.
    pub inst: Val,
    /// Does this Block represent Block, Block2, or Block3?
    pub blockn_cls: Val,
    pub blockinfo_off: usize,
    pub parent_closure: Gc<Closure>,
}

impl Obj for Block {
    fn dyn_objtype(&self) -> ObjType {
        ObjType::Block
    }

    fn get_class(&self, _: &mut VM) -> Val {
        self.blockn_cls.clone()
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
        method: Gc<Method>,
        inst: Val,
        blockinfo_off: usize,
        parent_closure: Gc<Closure>,
        num_params: usize,
    ) -> Val {
        let blockn_cls = match num_params {
            0 => vm.block_cls.clone(),
            1 => vm.block2_cls.clone(),
            2 => vm.block3_cls.clone(),
            _ => unimplemented!(),
        };
        Val::from_obj(
            vm,
            Block {
                method,
                inst,
                blockn_cls,
                blockinfo_off,
                parent_closure,
            },
        )
    }
}
