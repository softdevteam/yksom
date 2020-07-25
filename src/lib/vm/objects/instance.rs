#![allow(clippy::new_ret_no_self)]

use std::{alloc::Layout, collections::hash_map::DefaultHasher, hash::Hasher, mem::size_of};

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
}

// Since instances have a fixed number of instance variables, we do not need to allocate a separate
// object and backing store: we can fit both in a single block.  We thus use a custom layout where
// the `Inst` comes first, followed immediately by the `Val`s representing instance variables. On a
// 64-bit machine this looks roughly as follows:
//
//   0: Inst
//   8: Val [representing instance field 0]
//   16: Val [representing instance field 1]
//   ...

macro_rules! inst_vars {
    ($self:ident) => {
        // We assume that the instance variables immediately follow the `Inst` without padding.
        // This invariant is enforced in `Inst::new`. This saves us having to create a full
        // `Layout`, which would require us having to know how many instance variables this
        // particular `Inst` has.
        (Gc::into_raw($self) as *mut u8).add(::std::mem::size_of::<Inst>()) as *mut Val
    };
}

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
        let v = inst_vars!(self).add(n).read();
        debug_assert!(v.valkind() != ValKind::ILLEGAL);
        v
    }

    unsafe fn unchecked_inst_var_set(self: Gc<Self>, vm: &VM, n: usize, v: Val) {
        debug_assert!(n < self.num_inst_vars(vm));
        inst_vars!(self).add(n).write(v);
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
        let len = cls.inst_vars_map.len();
        debug_assert!(vm.nil.valkind() != ValKind::ILLEGAL || len == 0);
        let (vals_layout, vals_dist) = Layout::new::<Val>().repeat(len).unwrap();
        // We require the instance variables to be laid out as a C-like contiguous array.
        debug_assert_eq!(vals_dist, size_of::<Val>());
        let (layout, inst_vars_off) = Layout::new::<Inst>().extend(vals_layout).unwrap();
        // We require the instance variables to be positioned immediately after the `Inst` with no
        // padding in-between. This assumption is relied upon by the `inst_vars!` macro.
        debug_assert_eq!(inst_vars_off, size_of::<Inst>());
        unsafe {
            Val::new_from_layout(layout, |basep: *mut Inst| {
                *(&raw mut *basep) = Inst { class };
                let mut inst_vars = (basep as *mut u8).add(size_of::<Inst>()) as *mut Val;
                for _ in 0..len {
                    inst_vars.write(vm.nil);
                    inst_vars = inst_vars.add(1);
                }
            })
        }
    }
}
