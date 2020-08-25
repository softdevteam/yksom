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

mod array;
mod block;
mod class;
mod double;
mod instance;
mod integers;
mod method;
mod string_;

pub use array::{Array, MethodsArray, NormalArray};
pub use block::Block;
pub use class::Class;
pub use double::Double;
pub use instance::Inst;
pub use integers::{ArbInt, Int};
pub use method::Method;
pub use string_::String_;

use natrob::narrowable_rboehm;
use rboehm::Gc;

use crate::vm::{
    core::VM,
    error::{VMError, VMErrorKind},
    val::Val,
};

/// The SOM type of objects.
#[derive(Debug, PartialEq)]
pub enum ObjType {
    ArbInt,
    Array,
    Block,
    Class,
    Double,
    Method,
    Inst,
    Int,
    String_,
}

impl ObjType {
    pub fn as_str(&self) -> &'static str {
        match *self {
            ObjType::ArbInt => "ArbInt",
            ObjType::Array => "Array",
            ObjType::Block => "Block",
            ObjType::Class => "Class",
            ObjType::Double => "Double",
            ObjType::Method => "Method",
            ObjType::Inst => "Inst",
            ObjType::Int => "Int",
            ObjType::String_ => "String_",
        }
    }
}

/// The main SOM Object trait. Notice that code should almost never call these functions directly:
/// you should instead call the equivalent function in the `Val` struct.
#[narrowable_rboehm(ThinObj)]
pub trait Obj: std::fmt::Debug {
    /// What `ObjType` does this `Val` represent?
    fn dyn_objtype(self: Gc<Self>) -> ObjType;
    /// What class is this object an instance of?
    fn get_class(self: Gc<Self>, vm: &mut VM) -> Val;

    /// If (and only if) this object implements the [Array] trait then return a reference to this
    /// object as an [Array] trait object.
    fn to_array(self: Gc<Self>) -> Result<Gc<dyn Array>, Box<VMError>> {
        todo!();
    }

    /// Convert this object to a `Val` that represents a SOM string.
    fn to_strval(self: Gc<Self>, _: &mut VM) -> Result<Val, Box<VMError>> {
        unreachable!();
    }

    /// How many instance variables does this object contain?
    fn num_inst_vars(self: Gc<Self>, _: &VM) -> usize {
        unreachable!();
    }

    /// Return the instance variable at `i` (using SOM indexing).
    fn inst_var_at(self: Gc<Self>, vm: &VM, i: usize) -> Result<Val, Box<VMError>> {
        if i > 0 && i <= self.num_inst_vars(vm) {
            Ok(unsafe { self.unchecked_inst_var_get(vm, i - 1) })
        } else {
            Err(VMError::new(
                vm,
                VMErrorKind::IndexError {
                    tried: i,
                    max: self.num_inst_vars(vm),
                },
            ))
        }
    }

    /// Return the instance variable at `i` (using SOM indexing).
    fn inst_var_at_put(self: Gc<Self>, vm: &VM, i: usize, v: Val) -> Result<(), Box<VMError>> {
        if i > 0 && i <= self.num_inst_vars(vm) {
            unsafe { self.unchecked_inst_var_set(vm, i - 1, v) };
            Ok(())
        } else {
            Err(VMError::new(
                vm,
                VMErrorKind::IndexError {
                    tried: i,
                    max: self.num_inst_vars(vm),
                },
            ))
        }
    }

    /// Lookup an instance variable in this object. If `usize` exceeds the number of instance
    /// variables this will lead to undefined behaviour.
    unsafe fn unchecked_inst_var_get(self: Gc<Self>, _: &VM, _: usize) -> Val {
        unreachable!();
    }

    /// Set an instance variable in this object. If `usize` exceeds the number of instance
    /// variables this will lead to undefined behaviour.
    unsafe fn unchecked_inst_var_set(self: Gc<Self>, _: &VM, _: usize, _: Val) {
        unreachable!();
    }

    /// What is this object's length?
    fn length(self: Gc<Self>) -> usize {
        unreachable!();
    }

    /// What is this object's hashcode?
    fn hashcode(self: Gc<Self>) -> u64 {
        unreachable!();
    }

    /// Produce a new `Val` which adds `other` to this.
    fn add(self: Gc<Self>, _: &mut VM, _: Val) -> Result<Val, Box<VMError>> {
        unreachable!();
    }

    /// Produce a new `Val` which performs a bitwise and with `other` and this.
    fn and(self: Gc<Self>, _: &mut VM, _: Val) -> Result<Val, Box<VMError>> {
        unreachable!();
    }

    /// Produce a new `Val` which divides `other` from this.
    fn div(self: Gc<Self>, _: &mut VM, _: Val) -> Result<Val, Box<VMError>> {
        unreachable!();
    }

    fn double_div(self: Gc<Self>, _: &mut VM, _: Val) -> Result<Val, Box<VMError>> {
        unreachable!();
    }

    /// Produce a new `Val` which performs a mod operation on this with `other`.
    fn modulus(self: Gc<Self>, _: &mut VM, _: Val) -> Result<Val, Box<VMError>> {
        unreachable!();
    }

    /// Produce a new `Val` which multiplies `other` to this.
    fn mul(self: Gc<Self>, _: &mut VM, _: Val) -> Result<Val, Box<VMError>> {
        unreachable!();
    }

    /// Produce a new `Val` which returns the remainder of dividing this with `other`.
    fn remainder(self: Gc<Self>, _: &mut VM, _: Val) -> Result<Val, Box<VMError>> {
        unreachable!();
    }

    /// Produce a new `Val` which shifts `self` `other` bits to the left.
    fn shl(self: Gc<Self>, _: &mut VM, _: Val) -> Result<Val, Box<VMError>> {
        unreachable!();
    }

    /// Produce a new `Val` which shifts `self` `other` bits to the right, treating `self` as if it
    /// did not have a sign bit.
    fn shr(self: Gc<Self>, _: &mut VM, _: Val) -> Result<Val, Box<VMError>> {
        unreachable!();
    }

    /// Produces a new `Val` which is the square root of this.
    fn sqrt(self: Gc<Self>, _: &mut VM) -> Result<Val, Box<VMError>> {
        unreachable!();
    }

    /// Produce a new `Val` which subtracts `other` from this.
    fn sub(self: Gc<Self>, _: &mut VM, _: Val) -> Result<Val, Box<VMError>> {
        unreachable!();
    }

    /// Produce a new `Val` which performs a bitwise xor with `other` and this
    fn xor(self: Gc<Self>, _: &mut VM, _: Val) -> Result<Val, Box<VMError>> {
        unreachable!();
    }

    /// Is this `Val` reference equality equal to `other`? Only immutable SOM types are likely to
    /// want to override this.
    fn ref_equals(self: Gc<Self>, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        let other_tobj = other.tobj(vm)?;
        let other_data =
            unsafe { std::mem::transmute::<&dyn Obj, (*const u8, usize)>(&**other_tobj).0 };
        Ok(Val::from_bool(
            vm,
            (Gc::into_raw(self) as *const _ as *const u8) == other_data,
        ))
    }

    /// Does this `Val` equal `other`?
    fn equals(self: Gc<Self>, _: &mut VM, _: Val) -> Result<Val, Box<VMError>> {
        unreachable!();
    }

    /// Does this `Val` not equal `other`?
    fn not_equals(self: Gc<Self>, _: &mut VM, _: Val) -> Result<Val, Box<VMError>> {
        unreachable!();
    }

    /// Is this `Val` greater than `other`?
    fn greater_than(self: Gc<Self>, _: &mut VM, _: Val) -> Result<Val, Box<VMError>> {
        unreachable!();
    }

    /// Is this `Val` greater than or equal to `other`?
    fn greater_than_equals(self: Gc<Self>, _: &mut VM, _: Val) -> Result<Val, Box<VMError>> {
        unreachable!();
    }

    /// Is this `Val` less than `other`?
    fn less_than(self: Gc<Self>, _: &mut VM, _: Val) -> Result<Val, Box<VMError>> {
        unreachable!();
    }

    /// Is this `Val` less than or equal to `other`?
    fn less_than_equals(self: Gc<Self>, _: &mut VM, _: Val) -> Result<Val, Box<VMError>> {
        unreachable!();
    }
}

pub trait StaticObjType {
    /// Return this trait type's static `ObjType`
    fn static_objtype() -> ObjType;
}
