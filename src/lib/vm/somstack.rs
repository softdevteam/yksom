use std::cell::{Cell, UnsafeCell};

use std::gc::Gc;

use crate::vm::{objects::NormalArray, val::Val};

pub const SOM_STACK_LEN: usize = 4096;

/// A contiguous stack of SOM values. This stack does minimal or no checking on important
/// operations and users must ensure that they obey the constraints on each function herein, or
/// undefined behaviour will occur. Note also that `UpVar`s store interior pointers into the
/// stack: it must not, therefore, ever be moved in memory.
///
/// The basic layout of the stack is as a series of function frames growing from the beginning of
/// the stack upwards. A function frame looks roughly like:
///
///   0    : <arg 0>
///           ...
///          <arg n>
///   n    : <var 0>
///          ...
///          <var m>
///   (n+m): <working stack>
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
    len: Cell<usize>,
    /// The stack itself. Notice that we store this as *part of the `SOMStack` struct, so when we
    /// take interior pointers (in [`SOMStack::addr_of`]) they are interior pointers to `SOMStack`
    /// itself.
    store: UnsafeCell<[Val; SOM_STACK_LEN]>,
}

impl SOMStack {
    pub fn new() -> Gc<Self> {
        Gc::new(SOMStack {
            len: Cell::new(0),
            store: UnsafeCell::new([Val::illegal(); SOM_STACK_LEN]),
        })
    }

    /// Returns `true` if the stack contains no elements.
    pub fn is_empty(self: Gc<Self>) -> bool {
        self.len() == 0
    }

    /// Returns the number of elements in the stack.
    pub fn len(self: Gc<Self>) -> usize {
        self.len.get()
    }

    /// Returns the number of elements the stack can store before running out of room.
    pub fn remaining_capacity(self: Gc<Self>) -> usize {
        SOM_STACK_LEN - self.len()
    }

    pub unsafe fn addr_of(self: Gc<Self>, n: usize) -> Gc<Val> {
        Gc::from_raw((&*self.store.get()).get_unchecked(n))
    }

    /// Returns the top-most value of the stack without removing it. If the stack is empty, calling
    /// this function will lead to undefined behaviour.
    pub fn peek(self: Gc<Self>) -> Val {
        self.peek_n(0)
    }

    /// Peeks at a value `n` items from the start of the stack.
    pub fn peek_at(self: Gc<Self>, off: usize) -> Val {
        debug_assert!(off < self.len());
        *unsafe { (&*self.store.get()).get_unchecked(off) }
    }

    /// Peeks at a value `n` items from the top of the stack.
    pub fn peek_n(self: Gc<Self>, n: usize) -> Val {
        debug_assert!(n < self.len());
        *unsafe { (&*self.store.get()).get_unchecked(self.len() - n - 1) }
    }

    /// Pops the top-most value of the stack and returns it. If the stack is empty, calling
    /// this function will lead to undefined behaviour.
    pub fn pop(self: Gc<Self>) -> Val {
        debug_assert!(!self.is_empty());
        let len = self.len() - 1;
        self.len.set(len);
        unsafe {
            let p = (&mut *self.store.get()).get_unchecked_mut(len);
            let v = *p;
            *p = Val::illegal();
            v
        }
    }

    /// Push `v` onto the end of the stack. You must previously have checked (using
    /// [`SOMStack::remaining_capacity`]) that there is room for this value: if there is not,
    /// undefined behaviour will occur.
    pub fn push(self: Gc<Self>, v: Val) {
        debug_assert!(self.remaining_capacity() > 0);
        let len = self.len();
        *unsafe { (&mut *self.store.get()).get_unchecked_mut(len) } = v;
        self.len.set(len + 1);
    }

    pub fn set(self: Gc<Self>, n: usize, v: Val) {
        debug_assert!(n < self.len());
        *unsafe { (&mut *self.store.get()).get_unchecked_mut(n) } = v;
    }

    /// Splits the collection into two at the given index.
    ///
    /// Returns a newly allocated `NormalArray` containing the elements in the range [at, len).
    /// After the call, the SOM stack will be left containing the elements [0, at) with its
    /// previous capacity unchanged.
    pub fn split_off(self: Gc<Self>, at: usize) -> Val {
        let v = Vec::from(&unsafe { &*self.store.get() }[at..self.len()]);
        self.truncate(at);
        NormalArray::from_vec(v)
    }

    /// Shortens the stack, keeping the first len elements and dropping the rest.
    pub fn truncate(self: Gc<Self>, len: usize) {
        debug_assert!(len <= self.len());
        for i in len..self.len() {
            // Since `Val`s don't have a `drop` implementation, we can simply discard them without
            // worrying about them being dropped.
            self.set(i, Val::illegal());
        }
        self.len.set(len);
    }
}
