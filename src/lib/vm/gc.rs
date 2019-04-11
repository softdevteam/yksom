// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

use std::{
    alloc::{alloc, dealloc, Layout},
    marker::PhantomData,
    mem::{forget, size_of},
    ops::Deref,
};

/// Since Rust's alloc system requires us to tell it the `Layout` of a region of memory upon
/// deallocation, we either have to store the `Layout` or calculate it when needed. We choose the
/// latter, which forces every GCable thing to implement this trait.
pub trait GcLayout {
    fn layout(&self) -> Layout;
}

#[derive(Debug)]
pub struct Gc<T: GcLayout> {
    ptr: *mut GcBox<T>,
}

impl<T: GcLayout> Gc<T> {
    /// Consumes the `Gc` returning a pointer which can be later used to recreate a `Gc` using
    /// either `from_raw` or `clone_from_raw`. Failing to recreate the `Gc` will lead to a memory
    /// leak.
    pub fn into_raw(self) -> *const GcBox<T> {
        let ptr = self.ptr;
        forget(self);
        ptr
    }

    /// Create a `Gc` from a raw pointer previously created by `blank_alloc` or `into_raw`. Note
    /// that this does not increment the reference count.
    pub unsafe fn from_raw(ptr: *const GcBox<T>) -> Self {
        Gc {
            ptr: ptr as *mut GcBox<T>,
        }
    }

    /// Create a `Gc` from a raw pointer previously created by `into_raw`, incrementing the
    /// reference count at the same time.
    pub unsafe fn clone_from_raw(ptr: *const GcBox<T>) -> Self {
        (*(ptr as *mut GcBox<T>)).clones += 1;
        Gc {
            ptr: ptr as *mut GcBox<T>,
        }
    }

    /// Clone the GC object `gcc`. Note that this is an associated method.
    pub fn clone(gcc: &Gc<T>) -> Self {
        unsafe { &mut *gcc.ptr }.clones += 1;
        Gc { ptr: gcc.ptr }
    }
}

impl<T: GcLayout> Drop for Gc<T> {
    fn drop(&mut self) {
        let clones = unsafe { &mut *self.ptr }.clones;
        if clones == 1 {
            unsafe { dealloc(self.ptr as *mut u8, self.layout()) };
        } else {
            unsafe { &mut *self.ptr }.clones = clones - 1;
        }
    }
}

impl<T: GcLayout> Deref for Gc<T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.ptr }.deref()
    }
}

#[derive(Debug)]
pub struct GcBox<T: ?Sized> {
    clones: usize,
    phantom: PhantomData<T>,
}

impl<T: GcLayout> GcBox<T> {
    /// Allocate a `GcBox` with enough size to store `l`, returning a tuple whose first element
    /// must later be passed to `GcBox::from_raw` and whose second element is a raw pointer to
    /// storage sufficient to store `l`.
    #[allow(clippy::cast_ptr_alignment)]
    pub fn alloc_blank(l: Layout) -> (*mut Self, *mut T) {
        let (layout, valoff) = Layout::new::<GcBox<T>>().extend(l).unwrap();
        debug_assert_eq!(valoff, size_of::<GcBox<T>>());
        let gcbptr = unsafe { alloc(layout) as *mut Self };
        if gcbptr.is_null() {
            panic!("Can't allocate memory.");
        }
        unsafe { &mut *gcbptr }.clones = 1;
        let valptr = unsafe { (gcbptr as *mut u8).add(valoff) } as *mut T;
        (gcbptr, valptr)
    }
}

impl<T: GcLayout> Deref for GcBox<T> {
    type Target = T;

    fn deref(&self) -> &T {
        let valptr = unsafe { (self as *const GcBox<T> as *const u8).add(size_of::<GcBox<T>>()) }
            as *const T;
        unsafe { &*valptr }
    }
}
