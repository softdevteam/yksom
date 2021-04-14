#![allow(clippy::new_ret_no_self)]

use std::{
    alloc::Layout, cell::UnsafeCell, collections::hash_map::DefaultHasher, hash::Hasher,
    mem::size_of, ptr::copy_nonoverlapping,
};

use libgc::Gc;

use crate::vm::{
    core::VM,
    error::{VMError, VMErrorKind},
    objects::{Obj, ObjType, StaticObjType},
    val::{NotUnboxable, Val},
};

pub trait Array: Send {
    /// Return the item at index `idx` (using SOM indexing starting at 1) or an error if the index
    /// is invalid.
    fn at(self: Gc<Self>, vm: &VM, idx: usize) -> Result<Val, Box<VMError>>
    where
        Self: Send;

    /// Return the item at index `idx` (using SOM indexing starting at 1). This will lead to
    /// undefined behaviour if the index is invalid.
    unsafe fn unchecked_at(self: Gc<Self>, idx: usize) -> Val
    where
        Self: Send;

    /// Set the item at index `idx` (using SOM indexing starting at 1) to `val` or return an error
    /// if the index is invalid.
    fn at_put(self: Gc<Self>, vm: &mut VM, idx: usize, val: Val) -> Result<(), Box<VMError>>
    where
        Self: Send;

    /// Iterate over this array's values.
    fn iter(self: Gc<Self>) -> ArrayIterator
    where
        Self: Send;
}

#[derive(Debug)]
pub struct NormalArray {
    len: usize,
}

// Since arrays have a fixed number of elements in their store, we do not need to allocate a separate
// object and store: we can fit both in a single block. We thus use a custom layout where
// the `NormalArray` comes first, followed immediately by a contiguous array of `Val`s. On a
// 64-bit machine this looks roughly as follows:
//
//   0: NormalArray { len: ... }
//   8: Val_0
//   16: Val_1
//   ...

macro_rules! narr_store {
    ($self:ident) => {
        // We assume that the backing store immediately follows the `NormalArray` without padding.
        // This invariant is enforced in `NormalArray::alloc`. This saves us having to create a
        // full `Layout`, which would require us having to know how many elements are stored in
        // this array.
        (Gc::into_raw($self) as *mut u8).add(::std::mem::size_of::<NormalArray>()) as *mut Val
    };
}

impl Obj for NormalArray {
    fn dyn_objtype(self: Gc<Self>) -> ObjType {
        ObjType::Array
    }

    fn get_class(self: Gc<Self>, vm: &mut VM) -> Val {
        vm.array_cls
    }

    fn to_array(self: Gc<Self>) -> Result<Gc<dyn Array>, Box<VMError>> {
        Ok(self)
    }

    fn hashcode(self: Gc<Self>) -> u64 {
        let mut hasher = DefaultHasher::new();
        hasher.write_usize(Gc::into_raw(self) as *const _ as usize);
        hasher.finish()
    }

    fn length(self: Gc<Self>) -> usize {
        self.len
    }
}

impl NotUnboxable for NormalArray {}

impl StaticObjType for NormalArray {
    fn static_objtype() -> ObjType {
        ObjType::Array
    }
}

impl Array for NormalArray {
    fn at(self: Gc<Self>, vm: &VM, idx: usize) -> Result<Val, Box<VMError>> {
        if idx > 0 && idx <= self.len {
            Ok(unsafe { self.unchecked_at(idx) })
        } else {
            Err(VMError::new(
                vm,
                VMErrorKind::IndexError {
                    tried: idx,
                    max: self.len,
                },
            ))
        }
    }

    unsafe fn unchecked_at(self: Gc<Self>, idx: usize) -> Val {
        debug_assert!(idx > 0 && idx <= self.len);
        narr_store!(self).add(idx - 1).read()
    }

    fn at_put(self: Gc<Self>, vm: &mut VM, idx: usize, val: Val) -> Result<(), Box<VMError>> {
        if idx > 0 && idx <= self.len {
            unsafe {
                narr_store!(self).add(idx - 1).write(val);
            }
            Ok(())
        } else {
            Err(VMError::new(
                vm,
                VMErrorKind::IndexError {
                    tried: idx,
                    max: self.len,
                },
            ))
        }
    }

    fn iter(self: Gc<Self>) -> ArrayIterator {
        ArrayIterator {
            arr: self,
            len: self.len,
            i: 0,
        }
    }
}

impl NormalArray {
    pub fn new(vm: &VM, len: usize) -> Val {
        unsafe {
            NormalArray::alloc(len, |mut store: *mut Val| {
                for _ in 0..len {
                    store.write(vm.nil);
                    store = store.add(1);
                }
            })
        }
    }

    pub fn from_vec(v: Vec<Val>) -> Val {
        unsafe {
            NormalArray::alloc(v.len(), |store: *mut Val| {
                copy_nonoverlapping(v.as_ptr(), store, v.len());
            })
        }
    }

    /// Create a new `NormalArray` with a backing store of `len` elements. `init` will be called
    /// with a pointer to the uninitialised backing store. After `init` completes, the backing
    /// store will be considered fully initialised: failure to fully initialise it causes undefined
    /// behaviour.
    pub unsafe fn alloc<F>(len: usize, init: F) -> Val
    where
        F: FnOnce(*mut Val),
    {
        let (vals_layout, vals_dist) = Layout::new::<Val>().repeat(len).unwrap();
        // We require the store to be laid out as a C-like contiguous array.
        debug_assert_eq!(vals_dist, size_of::<Val>());
        let (layout, store_off) = Layout::new::<NormalArray>().extend(vals_layout).unwrap();
        // We require the store to be positioned immediately after the `NormalArray` with no
        // padding in-between. This assumption is relied upon by the `narr_store!` macro.
        debug_assert_eq!(store_off, size_of::<NormalArray>());
        Val::new_from_layout(layout, |ptr: *mut NormalArray| {
            let ptr = &raw mut *ptr;
            (*ptr).len = len;
            let store = (ptr as *mut u8).add(size_of::<NormalArray>()) as *mut Val;
            init(store);
        })
    }
}

#[derive(Debug)]
pub struct MethodsArray {
    store: UnsafeCell<Vec<Val>>,
}

impl Obj for MethodsArray {
    fn dyn_objtype(self: Gc<Self>) -> ObjType
    where
        Self: Send,
    {
        ObjType::Array
    }

    fn get_class(self: Gc<Self>, vm: &mut VM) -> Val
    where
        Self: Send,
    {
        vm.array_cls
    }

    fn to_array(self: Gc<Self>) -> Result<Gc<dyn Array>, Box<VMError>>
    where
        Self: Send,
    {
        Ok(self)
    }

    fn hashcode(self: Gc<Self>) -> u64
    where
        Self: Send,
    {
        let mut hasher = DefaultHasher::new();
        hasher.write_usize(Gc::into_raw(self) as *const _ as usize);
        hasher.finish()
    }

    fn length(self: Gc<Self>) -> usize
    where
        Self: Send,
    {
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
    fn at(self: Gc<Self>, vm: &VM, mut idx: usize) -> Result<Val, Box<VMError>> {
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

    unsafe fn unchecked_at(self: Gc<Self>, mut idx: usize) -> Val {
        debug_assert!(idx > 0);
        let store = &*self.store.get();
        debug_assert!(idx <= store.len());
        idx -= 1;
        *store.get_unchecked(idx)
    }

    fn at_put(self: Gc<Self>, vm: &mut VM, mut idx: usize, val: Val) -> Result<(), Box<VMError>> {
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

    fn iter(self: Gc<Self>) -> ArrayIterator {
        ArrayIterator {
            arr: self,
            len: self.length(),
            i: 0,
        }
    }
}

impl MethodsArray {
    pub fn from_vec(_vm: &mut VM, store: Vec<Val>) -> Val {
        Val::from_obj(MethodsArray {
            store: UnsafeCell::new(store),
        })
    }
}

pub struct ArrayIterator {
    arr: Gc<dyn Array>,
    len: usize,
    i: usize,
}

impl Iterator for ArrayIterator {
    type Item = Val;

    fn next(&mut self) -> Option<Val> {
        if self.i < self.len {
            self.i += 1;
            Some(unsafe { self.arr.unchecked_at(self.i) })
        } else {
            None
        }
    }
}
