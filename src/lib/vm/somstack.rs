use std::{alloc::Layout, mem::size_of, ptr};

use rboehm::Gc;

use crate::vm::{objects::NormalArray, val::Val};

pub const SOM_STACK_LEN: usize = 4096;

/// A contiguous stack of SOM values. This stack does minimal or no checking on important
/// operations and users must ensure that they obey the constraints on each function herein, or
/// undefined behaviour will occur.
///
/// The basic layout of the stack is as a series of function frames growing from the beginning of
/// the stack upwards. On a 64-bit machine, a function frame looks roughly like:
///
///   0    :     <arg 0>
///               ...
///              <arg n>
///   n * 8:     <var 0>
///              ...
///              <var m>
///   (n+m) * 8: <working stack>
///
/// The compiler and VM treat <arg 0> as special: it always contains a reference to `self` (hence
/// all functions have 1 extra parameter over those specified by the user). Functions are expected
/// to be called with their arguments already in place on the stack, and the stack pointer pointing
/// to after the arguments but before the variables (i.e. the function will then set up its
/// variables however it wants). Similarly, when a function is returned, the return value is
/// expected to be placed where <arg 0> was originally found (i.e. at the end of the previous
/// function's working stack).
pub struct SOMStack {
    /// How many items are used? Note that the stack has an implicit capacity of [`SOM_STACK_LEN`].
    len: usize,
}

macro_rules! storage {
    ($self:ident) => {
        // We assume that the stack immediately follows the `SOMStack` without padding. This
        // invariant is enforced in `SOMStack::new`. This saves us having to create a full `Layout`
        // each time.
        (Gc::into_raw($self) as *mut u8).add(::std::mem::size_of::<SOMStack>()) as *mut Val
    };
}

impl SOMStack {
    pub fn new() -> Gc<Self> {
        #![allow(clippy::cast_ptr_alignment)]
        let layout = Layout::new::<Self>();
        let (layout, off) = layout
            .extend(Layout::array::<Val>(SOM_STACK_LEN).unwrap())
            .unwrap();
        assert_eq!(off, size_of::<usize>());
        let gc = Gc::<Self>::new_from_layout(layout);
        unsafe {
            *(&raw mut *(Gc::into_raw(gc) as *mut Self)) = SOMStack { len: 0 };
            gc.assume_init()
        }
    }

    /// Returns `true` if the stack contains no elements.
    pub fn is_empty(self: Gc<Self>) -> bool {
        self.len() == 0
    }

    /// Returns the number of elements in the stack.
    pub fn len(self: Gc<Self>) -> usize {
        self.len
    }

    /// Returns the number of elements the stack can store before running out of room.
    pub fn remaining_capacity(self: Gc<Self>) -> usize {
        SOM_STACK_LEN - self.len()
    }

    pub unsafe fn addr_of(self: Gc<Self>, n: usize) -> Gc<Val> {
        Gc::from_raw(storage!(self).add(n))
    }

    /// Returns the top-most value of the stack without removing it. If the stack is empty, calling
    /// this function will lead to undefined behaviour.
    pub fn peek(self: Gc<Self>) -> Val {
        self.peek_n(0)
    }

    /// Peeks at a value `n` items from the top of the stack.
    pub fn peek_at(self: Gc<Self>, off: usize) -> Val {
        debug_assert!(off < self.len());
        unsafe { ptr::read(storage!(self).add(off)) }
    }

    /// Peeks at a value `n` items from the top of the stack.
    pub fn peek_n(self: Gc<Self>, n: usize) -> Val {
        debug_assert!(n < self.len());
        unsafe { ptr::read(storage!(self).add(self.len - n - 1)) }
    }

    /// Pops the top-most value of the stack and returns it. If the stack is empty, calling
    /// this function will lead to undefined behaviour.
    pub fn pop(mut self: Gc<Self>) -> Val {
        debug_assert!(!self.is_empty());
        self.len -= 1;
        unsafe { ptr::read(storage!(self).add(self.len)) }
    }

    /// Pops the top-most value of the stack and returns it. If the stack is empty, calling
    /// this function will lead to undefined behaviour.
    pub fn pop_n(mut self: Gc<Self>, n: usize) -> Val {
        debug_assert!(n < self.len());
        self.len -= 1;
        let i = self.len - n;
        let v = unsafe { ptr::read(storage!(self).add(i)) };
        unsafe { ptr::copy(storage!(self).add(i + 1), storage!(self).add(i), n) };
        v
    }

    /// Push `v` onto the end of the stack. You must previously have checked (using
    /// [`SOMStack::remaining_capacity`]) that there is room for this value: if there is not,
    /// undefined behaviour will occur.
    pub fn push(mut self: Gc<Self>, v: Val) {
        debug_assert!(self.remaining_capacity() > 0);
        unsafe { ptr::write(storage!(self).add(self.len), v) };
        self.len += 1;
    }

    pub fn set(self: Gc<Self>, n: usize, v: Val) {
        debug_assert!(n < self.len());
        unsafe {
            ptr::write(storage!(self).add(n), v);
        }
    }

    /// Splits the collection into two at the given index.
    ///
    /// Returns a newly allocated `NormalArray` containing the elements in the range [at, len).
    /// After the call, the SOM stack will be left containing the elements [0, at) with its
    /// previous capacity unchanged.
    pub fn split_off(mut self: Gc<Self>, at: usize) -> Val {
        let arr = unsafe {
            NormalArray::alloc(self.len() - at, |arr_store: *mut Val| {
                ptr::copy_nonoverlapping(storage!(self).add(at), arr_store, self.len() - at);
            })
        };
        self.len = at;
        arr
    }

    /// Shortens the stack, keeping the first len elements and dropping the rest.
    pub fn truncate(mut self: Gc<Self>, len: usize) {
        debug_assert!(len <= self.len());
        for i in len..self.len {
            unsafe {
                ptr::read(storage!(self).add(i));
            }
        }
        self.len = len;
    }
}
