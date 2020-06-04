#![allow(clippy::new_ret_no_self)]

use std::cell::UnsafeCell;

use crate::vm::{
    core::VM,
    error::{VMError, VMErrorKind},
    objects::{Obj, ObjType, StaticObjType},
    val::{NotUnboxable, Val},
};

pub trait Array {
    fn at(&self, vm: &VM, idx: usize) -> Result<Val, Box<VMError>>;
    unsafe fn unchecked_at(&self, idx: usize) -> Val;
    fn at_put(&self, vm: &mut VM, idx: usize, val: Val) -> Result<(), Box<VMError>>;
}

#[derive(Debug)]
pub struct NormalArray {
    store: UnsafeCell<Vec<Val>>,
}

impl Obj for NormalArray {
    fn dyn_objtype(&self) -> ObjType {
        ObjType::Array
    }

    fn get_class(&self, vm: &mut VM) -> Val {
        vm.array_cls
    }

    fn to_array(&self) -> Result<&dyn Array, Box<VMError>> {
        Ok(self)
    }

    fn length(&self) -> usize {
        let store = unsafe { &*self.store.get() };
        store.len()
    }
}

impl NotUnboxable for NormalArray {}

impl StaticObjType for NormalArray {
    fn static_objtype() -> ObjType {
        ObjType::Array
    }
}

impl Array for NormalArray {
    /// Return the item at index `idx` (using SOM indexing starting at 1) or an error if the index
    /// is invalid.
    fn at(&self, vm: &VM, mut idx: usize) -> Result<Val, Box<VMError>> {
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

    /// Return the item at index `idx` (using SOM indexing starting at 1). This will lead to
    /// undefined behaviour if the index is invalid.
    unsafe fn unchecked_at(&self, mut idx: usize) -> Val {
        debug_assert!(idx > 0);
        let store = &*self.store.get();
        debug_assert!(idx <= store.len());
        idx -= 1;
        *store.get_unchecked(idx)
    }

    /// Set the item at index `idx` (using SOM indexing starting at 1) to `val` or return an error
    /// if the index is invalid.
    fn at_put(&self, vm: &mut VM, mut idx: usize, val: Val) -> Result<(), Box<VMError>> {
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

impl NormalArray {
    pub fn new(vm: &mut VM, len: usize) -> Val {
        let mut store = Vec::with_capacity(len);
        store.resize(len, vm.nil);
        Val::from_obj(
            vm,
            NormalArray {
                store: UnsafeCell::new(store),
            },
        )
    }

    pub fn from_vec(vm: &mut VM, store: Vec<Val>) -> Val {
        Val::from_obj(
            vm,
            NormalArray {
                store: UnsafeCell::new(store),
            },
        )
    }
}

#[derive(Debug)]
pub struct MethodsArray {
    store: UnsafeCell<Vec<Val>>,
}

impl Obj for MethodsArray {
    fn dyn_objtype(&self) -> ObjType {
        ObjType::Array
    }

    fn get_class(&self, vm: &mut VM) -> Val {
        vm.array_cls
    }

    fn to_array(&self) -> Result<&dyn Array, Box<VMError>> {
        Ok(self)
    }

    fn length(&self) -> usize {
        let store = unsafe { &*self.store.get() };
        store.len()
    }
}

impl NotUnboxable for MethodsArray {}

impl StaticObjType for MethodsArray {
    fn static_objtype() -> ObjType {
        ObjType::Array
    }
}

impl Array for MethodsArray {
    /// Return the item at index `idx` (using SOM indexing starting at 1) or an error if the index
    /// is invalid.
    fn at(&self, vm: &VM, mut idx: usize) -> Result<Val, Box<VMError>> {
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

    /// Return the item at index `idx` (using SOM indexing starting at 1). This will lead to
    /// undefined behaviour if the index is invalid.
    unsafe fn unchecked_at(&self, mut idx: usize) -> Val {
        debug_assert!(idx > 0);
        let store = &*self.store.get();
        debug_assert!(idx <= store.len());
        idx -= 1;
        *store.get_unchecked(idx)
    }

    /// Set the item at index `idx` (using SOM indexing starting at 1) to `val` or return an error
    /// if the index is invalid.
    fn at_put(&self, vm: &mut VM, mut idx: usize, val: Val) -> Result<(), Box<VMError>> {
        let store = unsafe { &mut *self.store.get() };
        if idx > 0 && idx <= store.len() {
            idx -= 1;
            *unsafe { store.get_unchecked_mut(idx) } = val;
            vm.flush_inline_caches();
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

impl MethodsArray {
    pub fn from_vec(vm: &mut VM, store: Vec<Val>) -> Val {
        Val::from_obj(
            vm,
            MethodsArray {
                store: UnsafeCell::new(store),
            },
        )
    }

    /// Iterate over this array's values.
    pub fn iter<'a>(&'a self) -> MethodsArrayIterator<'a> {
        MethodsArrayIterator { arr: self, i: 0 }
    }
}

pub struct MethodsArrayIterator<'a> {
    arr: &'a MethodsArray,
    i: usize,
}

impl<'a> Iterator for MethodsArrayIterator<'a> {
    type Item = Val;

    fn next(&mut self) -> Option<Val> {
        if self.i < self.arr.length() {
            self.i += 1;
            Some(unsafe { self.arr.unchecked_at(self.i) })
        } else {
            None
        }
    }
}
