#![allow(clippy::new_ret_no_self)]

use std::cell::UnsafeCell;

use crate::vm::{
    core::VM,
    error::{VMError, VMErrorKind},
    objects::{Obj, ObjType, StaticObjType},
    val::{NotUnboxable, Val},
};

#[derive(Debug)]
pub struct Array {
    store: UnsafeCell<Vec<Val>>,
}

impl Obj for Array {
    fn dyn_objtype(&self) -> ObjType {
        ObjType::Array
    }

    fn get_class(&self, vm: &mut VM) -> Val {
        vm.array_cls
    }

    fn length(&self) -> usize {
        let store = unsafe { &*self.store.get() };
        store.len()
    }
}

impl NotUnboxable for Array {}

impl StaticObjType for Array {
    fn static_objtype() -> ObjType {
        ObjType::Array
    }
}

impl Array {
    pub fn new(vm: &mut VM, len: usize) -> Val {
        let mut store = Vec::with_capacity(len);
        store.resize(len, vm.nil);
        Val::from_obj(
            vm,
            Array {
                store: UnsafeCell::new(store),
            },
        )
    }

    pub fn from_vec(vm: &mut VM, store: Vec<Val>) -> Val {
        Val::from_obj(
            vm,
            Array {
                store: UnsafeCell::new(store),
            },
        )
    }

    pub fn at(&self, vm: &VM, mut idx: usize) -> Result<Val, Box<VMError>> {
        let store = unsafe { &*self.store.get() };
        if idx > 0 && idx <= store.len() {
            idx -= 1;
            Ok(*unsafe { store.get_unchecked(idx) })
        } else {
            Err(VMError::new(
                vm,
                VMErrorKind::IndexError {
                    tried: idx,
                    max: store.len(),
                },
            ))
        }
    }

    pub fn at_put(&self, vm: &VM, mut idx: usize, val: Val) -> Result<(), Box<VMError>> {
        let store = unsafe { &mut *self.store.get() };
        if idx > 0 && idx <= store.len() {
            idx -= 1;
            *unsafe { store.get_unchecked_mut(idx) } = val;
            Ok(())
        } else {
            Err(VMError::new(
                vm,
                VMErrorKind::IndexError {
                    tried: idx,
                    max: store.len(),
                },
            ))
        }
    }
}
