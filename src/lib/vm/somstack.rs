use std::{
    alloc::{alloc, dealloc, Layout},
    mem::forget,
    ptr,
};

use crate::vm::val::Val;

pub const SOM_STACK_LEN: usize = 4096;

/// A fixed size stack of SOM values. This stack does minimal or no checking on important
/// operations and users must ensure that they obey the constraints on each function herein, or
/// undefined behaviour will occur.
pub struct SOMStack {
    storage: *mut Val,
    /// How many items are used? Note that the stack has an implicit capacity of [`SOM_STACK_LEN`].
    len: usize,
}

impl SOMStack {
    pub fn new() -> SOMStack {
        #![allow(clippy::cast_ptr_alignment)]
        let storage = unsafe { alloc(Layout::array::<Val>(SOM_STACK_LEN).unwrap()) as *mut Val };
        SOMStack { storage, len: 0 }
    }

    /// Returns `true` if the stack contains no elements.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the number of elements in the stack.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns the number of elements the stack can store before running out of room.
    pub fn remaining_capacity(&self) -> usize {
        SOM_STACK_LEN - self.len()
    }

    /// Returns the top-most value of the stack without removing it. If the stack is empty, calling
    /// this function will lead to undefined behaviour.
    pub fn peek(&self) -> Val {
        debug_assert!(!self.is_empty());
        let v = unsafe { ptr::read(self.storage.add(self.len - 1)) };
        let v2 = v.clone();
        forget(v);
        v2
    }

    /// Pops the top-most value of the stack and returns it. If the stack is empty, calling
    /// this function will lead to undefined behaviour.
    pub fn pop(&mut self) -> Val {
        debug_assert!(!self.is_empty());
        self.len -= 1;
        unsafe { ptr::read(self.storage.add(self.len)) }
    }

    /// Pops the top-most value of the stack and returns it. If the stack is empty, calling
    /// this function will lead to undefined behaviour.
    pub fn pop_n(&mut self, n: usize) -> Val {
        debug_assert!(n < self.len());
        self.len -= 1;
        let i = self.len - n;
        let v = unsafe { ptr::read(self.storage.add(i)) };
        unsafe { ptr::copy(self.storage.add(i + 1), self.storage.add(i), n) };
        v
    }

    /// Push `v` onto the end of the stack. You must previously have checked (using
    /// [`SOMStack::remaining_capacity`]) that there is room for this value: if there is not,
    /// undefined behaviour will occur.
    pub fn push(&mut self, v: Val) {
        debug_assert!(self.remaining_capacity() > 0);
        unsafe { ptr::write(self.storage.add(self.len), v) };
        self.len += 1;
    }

    /// Shortens the stack, keeping the first len elements and dropping the rest.
    pub fn truncate(&mut self, len: usize) {
        debug_assert!(len <= self.len());
        for i in len..self.len {
            unsafe {
                ptr::read(self.storage.add(i));
            }
        }
        self.len = len;
    }
}

impl Drop for SOMStack {
    fn drop(&mut self) {
        unsafe {
            dealloc(
                self.storage as *mut _,
                Layout::array::<Val>(SOM_STACK_LEN).unwrap(),
            )
        };
    }
}
