// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

//! This module contains the core SOM objects. Note that there is a fundamental constraint that
//! *must* be obeyed by the programmer at all times: upon their creation, instances of the `Obj`
//! trait must immediately be passed to `Val::from_obj`. In other words this is safe:
//!
//! ```rust,ignore
//! let x = Val::from_obj(vm, String_{ s: "a".to_owned() });
//! dbg!(x.tobj().as_str());
//! ```
//!
//! but this leads to undefined behaviour:
//!
//! ```rust,ignore
//! let x = String_{ s: "a".to_owned() };
//! dbg!(x.tobj().as_str());
//! ```
//!
//! The reason for this is that methods on `Obj`s can call `Val::restore` which converts an `Obj`
//! reference back into a `Val`.
//!
//! Although this constraint is not enforced through the type system, it is not hard to obey: as
//! soon as you create an `Obj` instance, pass it to `Val::from_obj`.

mod block;
mod class;
mod double;
mod instance;
mod integers;
mod method;
mod string_;

pub use block::Block;
pub use class::Class;
pub use double::Double;
pub use instance::Inst;
pub use integers::{ArbInt, Int};
pub use method::{Method, MethodBody};
pub use string_::String_;

use abgc::{self, Gc};
use natrob::narrowable_abgc;

use crate::vm::{
    core::{VMError, VM},
    val::Val,
};

/// The SOM type of objects.
#[derive(Debug, PartialEq)]
pub enum ObjType {
    ArbInt,
    Block,
    Class,
    Double,
    Method,
    Inst,
    Int,
    String_,
}

/// The main SOM Object trait. Notice that code should almost never call these functions directly:
/// you should instead call the equivalent function in the `Val` struct.
#[narrowable_abgc(ThinObj)]
pub trait Obj: std::fmt::Debug + abgc::GcLayout {
    /// What `ObjType` does this `Val` represent?
    fn dyn_objtype(&self) -> ObjType;
    /// What class is this object an instance of?
    fn get_class(&self, vm: &VM) -> Val;

    /// Convert this object to a `Val` that represents a SOM string.
    fn to_strval(&self, _: &VM) -> Result<Val, Box<VMError>> {
        unimplemented!();
    }

    /// Produce a new `Val` which performs a bitwise xor with `other` and this
    fn xor(&self, _: &VM, _: Val) -> Result<Val, Box<VMError>> {
        unimplemented!();
    }

    /// Produce a new `Val` which adds `other` to this.
    fn add(&self, _: &VM, _: Val) -> Result<Val, Box<VMError>> {
        unimplemented!();
    }

    /// Produce a new `Val` which performs a bitwise and with `other` and this.
    fn and(&self, _: &VM, _: Val) -> Result<Val, Box<VMError>> {
        unimplemented!();
    }

    /// Produce a new `Val` which divides `other` from this.
    fn div(&self, _: &VM, _: Val) -> Result<Val, Box<VMError>> {
        unimplemented!();
    }

    /// Produce a new `Val` which multiplies `other` to this.
    fn mul(&self, _: &VM, _: Val) -> Result<Val, Box<VMError>> {
        unimplemented!();
    }

    /// Produce a new `Val` which shifts `self` `other` bits to the left.
    fn shl(&self, _: &VM, _: Val) -> Result<Val, Box<VMError>> {
        unimplemented!();
    }

    /// Produces a new `Val` which is the square root of this.
    fn sqrt(&self, _: &VM) -> Result<Val, Box<VMError>> {
        unimplemented!();
    }

    /// Produce a new `Val` which subtracts `other` from this.
    fn sub(&self, _: &VM, _: Val) -> Result<Val, Box<VMError>> {
        unimplemented!();
    }

    /// Is this `Val` reference equality equal to `other`? Only number types are likely to want to
    /// override this.
    fn ref_equals(&self, vm: &VM, other: Val) -> Result<Val, Box<VMError>> {
        let other_tobj = other.tobj(vm)?;
        let other_data =
            unsafe { std::mem::transmute::<&dyn Obj, (*const u8, usize)>(&**other_tobj).0 };
        Ok(Val::from_bool(
            vm,
            (self as *const _ as *const u8) == other_data,
        ))
    }

    /// Does this `Val` equal `other`?
    fn equals(&self, _: &VM, _: Val) -> Result<Val, Box<VMError>> {
        unimplemented!();
    }

    /// Does this `Val` not equal `other`?
    fn not_equals(&self, _: &VM, _: Val) -> Result<Val, Box<VMError>> {
        unimplemented!();
    }

    /// Is this `Val` greater than `other`?
    fn greater_than(&self, _: &VM, _: Val) -> Result<Val, Box<VMError>> {
        unimplemented!();
    }

    /// Is this `Val` greater than or equal to `other`?
    fn greater_than_equals(&self, _: &VM, _: Val) -> Result<Val, Box<VMError>> {
        unimplemented!();
    }

    /// Is this `Val` less than `other`?
    fn less_than(&self, _: &VM, _: Val) -> Result<Val, Box<VMError>> {
        unimplemented!();
    }

    /// Is this `Val` less than or equal to `other`?
    fn less_than_equals(&self, _: &VM, _: Val) -> Result<Val, Box<VMError>> {
        unimplemented!();
    }
}

pub trait StaticObjType {
    /// Return this trait type's static `ObjType`
    fn static_objtype() -> ObjType;
}
