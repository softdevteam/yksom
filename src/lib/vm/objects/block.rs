#![allow(clippy::new_ret_no_self)]

use std::{alloc::Layout, collections::hash_map::DefaultHasher, hash::Hasher, mem::size_of};

use rboehm::Gc;

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
    prev: Option<Gc<UpVar>>,
    ptr: Gc<Val>,
    closed: Val,
}

impl UpVar {
    pub fn new(prev: Option<Gc<UpVar>>, ptr: Gc<Val>) -> Self {
        UpVar {
            prev,
            ptr,
            closed: Val::illegal(),
        }
    }

    pub fn to_gc(&self) -> Gc<Val> {
        debug_assert_ne!(self.ptr.valkind(), ValKind::ILLEGAL);
        self.ptr
    }

    pub fn close(&mut self) {
        self.closed = *self.to_gc();
        self.ptr = Gc::from_raw(&self.closed);
    }

    pub fn is_closed(&self) -> bool {
        Gc::into_raw(self.ptr) == &self.closed
    }

    pub fn prev(&self) -> Option<Gc<UpVar>> {
        self.prev
    }

    pub fn set_prev(&mut self, prev: Option<Gc<UpVar>>) {
        self.prev = prev;
    }
}

// Since blocks have a fixed number of upvars, we do not need to allocate a separate vector: we can
// fit both in a single allocation. We thus use a custom layout where the `Block` comes first,
// followed immediately by the `UpVar`s. On a 64-bit machine this looks roughly as follows:
//
//   0: Inst
//   8: Val [representing UpVar 0]
//   16: Val [representing UpVar 1]
//   ...

macro_rules! upvars_store {
    ($self:ident) => {
        // We assume that the pvars immediately follow the `Block` without padding. This invariant
        // is enforced in `Block::new`. This saves us having to create a full `Layout`, which would
        // require us having to know how many upvars this particular `Block` has.
        (Gc::into_raw($self) as *mut u8).add(::std::mem::size_of::<Block>()) as *const Gc<UpVar>
    };
}

#[derive(Debug)]
pub struct Block {
    /// This `Block`'s `self` val. XXX This should probably be part of the corresponding closure's
    /// variables.
    pub inst: Val,
    pub func: Gc<Function>,
    /// For closures which perform a method return (i.e. they cause the method they are contained
    /// within to return), we have to reset the stack to the method's stack base, so we have to
    /// cart that around with the Block.
    pub method_stack_base: usize,
}

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
    pub fn new<F>(
        vm: &mut VM,
        inst: Val,
        func: Gc<Function>,
        method_stack_base: usize,
        upvars_gen: F,
    ) -> Val
    where
        F: FnOnce(&mut VM, *mut Gc<UpVar>),
    {
        let len = func.upvar_defs().len();
        let (upvars_layout, upvars_dist) = Layout::new::<Val>().repeat(len).unwrap();
        // We require the Upvars to be laid out as a C-like contiguous array.
        debug_assert_eq!(upvars_dist, size_of::<Val>());
        let (layout, upvars_off) = Layout::new::<Block>().extend(upvars_layout).unwrap();
        // We require the upvars to be positioned immediately after the `Block` with no padding
        // in-between. This assumption is relied upon by the `upvars!` macro.
        debug_assert_eq!(upvars_off, size_of::<Block>());
        unsafe {
            Val::new_from_layout(layout, |basep: *mut Block| {
                *basep = Block {
                    inst,
                    func,
                    method_stack_base,
                };
                let upvars_store = (basep as *mut u8).add(size_of::<Block>()) as *mut Gc<UpVar>;
                upvars_gen(vm, upvars_store);
            })
        }
    }

    pub fn upvar(self: Gc<Self>, n: usize) -> Gc<UpVar> {
        unsafe { *upvars_store!(self).add(n) }
    }
}
