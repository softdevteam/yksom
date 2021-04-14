#![allow(clippy::new_ret_no_self)]

use std::{cell::Cell, collections::hash_map::DefaultHasher, hash::Hasher};

#[cfg(feature = "rustgc")]
use std::gc::NoFinalize;

use libgc::Gc;

use crate::vm::{
    core::VM,
    function::Function,
    objects::{Obj, ObjType, StaticObjType},
    val::{NotUnboxable, Val, ValKind},
};

/// An UpVar references either a variable on the stack or, if the UpVar is closed, a copy of that
/// variable inside the struct itself (the `closed` field). This scheme is very similar to that
/// used in Lua; the best explanation I know of can
/// be found at: http://www.craftinginterpreters.com/closures.html.
#[derive(Clone, Debug)]
pub struct UpVar {
    prev: Cell<Option<Gc<UpVar>>>,
    ptr: Cell<Gc<Val>>,
    closed: Cell<Val>,
}

impl UpVar {
    pub fn new(prev: Option<Gc<UpVar>>, ptr: Gc<Val>) -> Self {
        UpVar {
            prev: Cell::new(prev),
            ptr: Cell::new(ptr),
            closed: Cell::new(Val::illegal()),
        }
    }

    pub fn to_gc(&self) -> Gc<Val> {
        debug_assert_ne!(self.ptr.get().valkind(), ValKind::ILLEGAL);
        self.ptr.get()
    }

    pub fn close(&self) {
        self.closed.set(*self.to_gc());
        self.ptr
            .set(Gc::from_raw(&self.closed as *const Cell<_> as *const _));
    }

    pub fn is_closed(&self) -> bool {
        Gc::into_raw(self.ptr.get()) == &self.closed as *const Cell<_> as *const _
    }

    pub fn prev(&self) -> Option<Gc<UpVar>> {
        self.prev.get()
    }

    pub fn set_prev(&self, prev: Option<Gc<UpVar>>) {
        self.prev.set(prev);
    }
}

#[derive(Debug)]
pub struct Block {
    /// This `Block`'s `self` val. XXX This should probably be part of the corresponding closure's
    /// variables.
    pub inst: Val,
    pub func: Gc<Function>,
    pub upvars: Vec<Gc<UpVar>>,
    /// For closures which perform a method return (i.e. they cause the method they are contained
    /// within to return), we have to reset the stack to the method's stack base, so we have to
    /// cart that around with the Block.
    pub method_stack_base: usize,
}

#[cfg(feature = "rustgc")]
impl NoFinalize for Block {}

impl Obj for Block {
    fn dyn_objtype(self: Gc<Self>) -> ObjType {
        ObjType::Block
    }

    fn get_class(self: Gc<Self>, vm: &mut VM) -> Val {
        match self.func.num_params() {
            1 => vm.block1_cls,
            2 => vm.block2_cls,
            3 => vm.block3_cls,
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
    pub fn new(
        _: &mut VM,
        inst: Val,
        func: Gc<Function>,
        upvars: Vec<Gc<UpVar>>,
        method_stack_base: usize,
    ) -> Val {
        Val::from_obj(Block {
            inst,
            func,
            upvars,
            method_stack_base,
        })
    }
}
