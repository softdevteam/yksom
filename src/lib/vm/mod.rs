//! The yksom run-time. The run-time uses trait objects but stores them as thin pointers (using the
//! experimental [natrob library](https://github.com/softdevteam/natrob). This allows integer
//! tagging to be used. The [`Val`](vm::val::Val) struct stores tagged integers / pointers to boxed
//! objects. The [`Obj`](vm::objects::Obj) trait is the "supertype" trait of all objects, but it is
//! not intended that most parts of the VM call [`Obj`](vm::objects::Obj) directly: one should use
//! the identically named methods on [`Val`](vm::val::Val). As this suggests, users should, in most
//! cases, either operate directly on a [`Val`](vm::val::Val) or
//! [`Val::downcast`](vm::val::Val::downcast) (or
//! [`Val::try_downcast`](vm::val::Val::try_downcast)) it to a concrete implementation of `Obj`.

pub mod core;
pub mod error;
pub mod function;
pub mod objects;
pub mod somstack;
pub mod val;

pub use crate::vm::{
    core::VM,
    error::{VMError, VMErrorKind},
};
