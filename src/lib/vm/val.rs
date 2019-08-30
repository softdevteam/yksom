// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

#![allow(clippy::new_ret_no_self)]

//! This file contains the core SOM objects. Note that there is a fundamental constraint that
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

use std::{
    mem::{size_of, transmute},
    ops::Deref,
};

use abgc::{self, Gc};
use num_enum::{IntoPrimitive, UnsafeFromPrimitive};

use super::{
    objects::{Int, NotUnboxable, Obj, StaticObjType, ThinObj},
    vm::{VMError, VM},
};

// We use a fairly standard pointer tagging model where the low `TAG_BITSIZE` bits of a machine
// word (represented as a Rust `usize`) are used to store the type of the value (with the
// possibilities enumerated in `ValKind` below).

#[cfg(target_pointer_width = "64")]
pub const BITSIZE: usize = 64;
#[cfg(target_pointer_width = "64")]
pub const TAG_BITSIZE: usize = 3; // Number of bits
#[cfg(target_pointer_width = "64")]
pub const TAG_BITMASK: usize = (1 << 3) - 1;

#[cfg(target_pointer_width = "64")]
#[derive(Debug, PartialEq, IntoPrimitive, UnsafeFromPrimitive)]
#[repr(usize)]
pub enum ValKind {
    // All of the values here must fit inside TAG_BITSIZE bits and be safely convert to usize
    // using "as".
    GCBOX = 0b000,
    // Anything which can be stored unboxed *must* not have the `NotUnboxable` trait implemented
    // for them. In other words, if an existing type is added to the list of unboxable things, you
    // need to check whether it implemented `NotUnboxable` and, if so, remove that implementation.
    INT = 0b001,
}

/// The core struct representing values in the language runtime: boxed and unboxed values are
/// hidden behind this, such that they can be treated in exactly the same way.
#[derive(Debug, PartialEq)]
pub struct Val {
    // We use this usize for pointer tagging. Needless to say, this is highly dangerous, and needs
    // several parts of the code to cooperate in order to be correct.
    pub(crate) val: usize,
}

impl Val {
    /// Create a `Val` from a given instance of the `Obj` trait.
    ///
    /// [In an ideal world, this would be a function on `Obj` itself, but that would mean that
    /// `Obj` couldn't be a trait object. Oh well.]
    pub fn from_obj<T: Obj + 'static>(_: &VM, obj: T) -> Self {
        debug_assert_eq!(ValKind::GCBOX as usize, 0);
        debug_assert_eq!(size_of::<*const ThinObj>(), size_of::<usize>());
        let ptr = ThinObj::new(obj).into_raw();
        Val {
            val: unsafe { transmute::<*const ThinObj, usize>(ptr) },
        }
    }

    /// Convert `obj` into a `Val`. `Obj` must previously have been created via `Val::from_obj` and
    /// then turned into an actual object with `tobj`: failure to follow these steps will result in
    /// undefined behaviour.
    pub fn recover(obj: &dyn Obj) -> Self {
        unsafe {
            let ptr = ThinObj::recover(obj).into_raw();
            Val {
                val: transmute::<*const ThinObj, usize>(ptr),
            }
        }
    }

    /// Create a value upon which all operations are invalid. This can be used as a sentinel or
    /// while initialising part of the system.
    pub fn illegal() -> Val {
        Val { val: 0 }
    }

    /// Is this `Var` illegal i.e. is it an empty placeholder waiting for a "proper" value?
    pub fn is_illegal(&self) -> bool {
        self.val == 0
    }

    pub fn valkind(&self) -> ValKind {
        // Since it should be impossible to create incorrect tags, in release mode, we want to make
        // this a zero-cost function (i.e. we get guarantees from the static type system but
        // without any run-time overhead). However, just in case someone does something silly, in
        // debug mode we explicitly check the tags.

        #[cfg(debug_assertions)]
        match self.val & TAG_BITMASK {
            x if x == ValKind::GCBOX as usize => (),
            x if x == ValKind::INT as usize => (),
            _ => panic!("Invalid tag {}", self.val & TAG_BITMASK),
        }

        unsafe { ValKind::from_unchecked(self.val & TAG_BITMASK) }
    }

    /// Cast a `Val` into an instance of type `T` (where `T` must statically be a type that cannot
    /// be boxed) or `None` otherwise.
    ///
    /// If you need to downcast a type `T` which can be boxed, you will need to call `tobj` and
    /// `downcast` that.
    pub fn downcast<T: Obj + StaticObjType + NotUnboxable>(&self, _: &VM) -> Result<&T, VMError> {
        debug_assert_eq!(self.valkind(), ValKind::GCBOX);
        debug_assert_eq!(ValKind::GCBOX as usize, 0);
        debug_assert_eq!(size_of::<*const ThinObj>(), size_of::<usize>());
        debug_assert_ne!(self.val, 0);
        let tobj = unsafe { &*transmute::<usize, *const ThinObj>(self.val) };

        tobj.downcast().ok_or_else(|| VMError::TypeError {
            expected: T::static_objtype(),
            got: tobj.deref().dyn_objtype(),
        })
    }

    /// Return this `Val`'s box. If the `Val` refers to an unboxed value, this will box it.
    pub fn tobj(&self, vm: &VM) -> Result<Gc<ThinObj>, VMError> {
        match self.valkind() {
            ValKind::GCBOX => {
                debug_assert_eq!(ValKind::GCBOX as usize, 0);
                debug_assert_eq!(size_of::<*const ThinObj>(), size_of::<usize>());
                debug_assert_ne!(self.val, 0);
                Ok(unsafe { Gc::clone_from_raw(self.val as *const _) })
            }
            ValKind::INT => Int::boxed_isize(vm, self.as_isize(vm).unwrap())?.tobj(vm),
        }
    }

    /// If possible, return this `Val` as an `isize`.
    pub fn as_isize(&self, vm: &VM) -> Result<isize, VMError> {
        match self.valkind() {
            ValKind::GCBOX => Ok(self.tobj(vm)?.as_isize()?),
            ValKind::INT => {
                if self.val & 1 << (BITSIZE - 1) == 0 {
                    Ok((self.val >> TAG_BITSIZE) as isize)
                } else {
                    // For negative integers we need to pad the top TAG_BITSIZE bits with 1s.
                    Ok(
                        ((self.val >> TAG_BITSIZE) | (TAG_BITMASK << (BITSIZE - TAG_BITSIZE)))
                            as isize,
                    )
                }
            }
        }
    }

    /// If possible, return this `Val` as an `usize`.
    pub fn as_usize(&self, vm: &VM) -> Result<usize, VMError> {
        match self.valkind() {
            ValKind::GCBOX => Ok(self.tobj(vm)?.as_usize()?),
            ValKind::INT => {
                if self.val & 1 << (BITSIZE - 1) == 0 {
                    Ok(self.val >> TAG_BITSIZE)
                } else {
                    Err(VMError::CantRepresentAsUsize)
                }
            }
        }
    }
}

impl Clone for Val {
    fn clone(&self) -> Self {
        let val = match self.valkind() {
            ValKind::GCBOX => {
                if self.val != 0 {
                    unsafe {
                        transmute::<*const ThinObj, usize>(
                            Gc::<ThinObj>::clone_from_raw(self.val as *const _).into_raw(),
                        )
                    }
                } else {
                    0
                }
            }
            ValKind::INT => self.val,
        };
        Val { val }
    }
}

impl Drop for Val {
    fn drop(&mut self) {
        match self.valkind() {
            ValKind::GCBOX => {
                if self.val != 0 {
                    drop(unsafe { Gc::<ThinObj>::from_raw(self.val as *const _) });
                }
            }
            ValKind::INT => (),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm::{
        objects::{Class, ObjType, String_},
        vm::VM,
    };

    #[test]
    fn test_recovery() {
        let vm = VM::new_no_bootstrap();

        let v = {
            let v = String_::new(&vm, "s".to_owned());
            let v_tobj = v.tobj(&vm).unwrap();
            let v_int: &dyn Obj = v_tobj.deref().deref();
            let v_recovered = Val::recover(v_int);
            assert_eq!(v_recovered.val, v.val);
            v_recovered
        };
        // At this point, we will have dropped one of the references to the String above so the
        // assertion below is really checking that we're not doing a read after free.
        assert_eq!(v.downcast::<String_>(&vm).unwrap().as_str(), "s");
    }

    #[test]
    fn test_cast() {
        let vm = VM::new_no_bootstrap();
        let v = String_::new(&vm, "s".to_owned());
        assert!(v.downcast::<String_>(&vm).is_ok());
        assert_eq!(
            v.downcast::<Class>(&vm).unwrap_err(),
            VMError::TypeError {
                expected: ObjType::Class,
                got: ObjType::String_
            }
        );
    }

    #[test]
    fn test_downcast() {
        let vm = VM::new_no_bootstrap();
        let v = String_::new(&vm, "s".to_owned());
        assert!(v.downcast::<String_>(&vm).is_ok());
        assert!(v.downcast::<Class>(&vm).is_err());
    }
}