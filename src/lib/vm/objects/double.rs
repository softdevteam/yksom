#![allow(clippy::new_ret_no_self)]

use std::{collections::hash_map::DefaultHasher, hash::Hasher};

use num_bigint::BigInt;
use num_traits::{FromPrimitive, ToPrimitive, Zero};

use std::gc::Gc;

use crate::vm::{
    core::VM,
    error::{VMError, VMErrorKind},
    objects::{ArbInt, Obj, ObjType, StaticObjType, String_},
    val::{NotUnboxable, Val},
};

#[derive(Debug)]
/// A boxed Double (which is synonymous with a f64 in yksom).
pub struct Double {
    val: f64,
}

impl NotUnboxable for Double {}

impl Obj for Double {
    fn dyn_objtype(self: Gc<Self>) -> ObjType {
        ObjType::Double
    }

    fn get_class(self: Gc<Self>, vm: &mut VM) -> Val {
        vm.double_cls
    }

    fn to_strval(self: Gc<Self>, vm: &mut VM) -> Result<Val, Box<VMError>> {
        let mut buf = ryu::Buffer::new();
        Ok(String_::new_str(vm, String::from(buf.format(self.val))))
    }

    fn hashcode(self: Gc<Self>) -> u64 {
        let mut hasher = DefaultHasher::new();
        hasher.write_u64(self.val.to_bits());
        hasher.finish()
    }

    fn add(self: Gc<Self>, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Ok(rhs) = other.as_isize(vm) {
            Ok(Double::new(vm, self.val + (rhs as f64)))
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            Ok(Double::new(vm, self.val + rhs.val))
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            Ok(Double::new(vm, self.val + rhs.to_f64(vm)?))
        } else {
            let got = other.dyn_objtype(vm);
            Err(VMError::new(vm, VMErrorKind::NotANumber { got }))
        }
    }

    fn double_div(self: Gc<Self>, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Ok(rhs) = other.as_isize(vm) {
            if rhs == 0 {
                Err(VMError::new(vm, VMErrorKind::DivisionByZero))
            } else {
                Ok(Double::new(vm, self.val / (rhs as f64)))
            }
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            if rhs.val == 0f64 {
                Err(VMError::new(vm, VMErrorKind::DivisionByZero))
            } else {
                Ok(Double::new(vm, self.val / rhs.val))
            }
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            if Zero::is_zero(rhs.bigint()) {
                Err(VMError::new(vm, VMErrorKind::DivisionByZero))
            } else {
                Ok(Double::new(vm, self.val / rhs.to_f64(vm)?))
            }
        } else {
            let got = other.dyn_objtype(vm);
            Err(VMError::new(vm, VMErrorKind::NotANumber { got }))
        }
    }

    fn modulus(self: Gc<Self>, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Ok(rhs) = other.as_isize(vm) {
            Ok(Double::new(vm, self.val % (rhs as f64)))
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            Ok(Double::new(vm, self.val % rhs.val))
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            Ok(Double::new(vm, self.val % rhs.to_f64(vm)?))
        } else {
            let got = other.dyn_objtype(vm);
            Err(VMError::new(vm, VMErrorKind::NotANumber { got }))
        }
    }

    fn mul(self: Gc<Self>, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Ok(rhs) = other.as_isize(vm) {
            Ok(Double::new(vm, self.val * (rhs as f64)))
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            Ok(Double::new(vm, self.val * rhs.val))
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            Ok(Double::new(vm, self.val * rhs.to_f64(vm)?))
        } else {
            let got = other.dyn_objtype(vm);
            Err(VMError::new(vm, VMErrorKind::NotANumber { got }))
        }
    }

    fn sqrt(self: Gc<Self>, vm: &mut VM) -> Result<Val, Box<VMError>> {
        Ok(Double::new(vm, self.val.sqrt()))
    }

    fn sub(self: Gc<Self>, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        if let Ok(rhs) = other.as_isize(vm) {
            Ok(Double::new(vm, self.val - (rhs as f64)))
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            Ok(Double::new(vm, self.val - rhs.val))
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            Ok(Double::new(vm, self.val - rhs.to_f64(vm)?))
        } else {
            let got = other.dyn_objtype(vm);
            Err(VMError::new(vm, VMErrorKind::NotANumber { got }))
        }
    }

    fn ref_equals(self: Gc<Self>, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        self.equals(vm, other)
    }

    fn equals(self: Gc<Self>, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        let b = if let Ok(rhs) = other.as_isize(vm) {
            self.val == (rhs as f64)
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            self.val == rhs.double()
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            match rhs.bigint().to_f64() {
                Some(i) => self.val == i,
                None => false,
            }
        } else {
            false
        };

        Ok(Val::from_bool(vm, b))
    }

    fn less_than(self: Gc<Self>, vm: &mut VM, other: Val) -> Result<Val, Box<VMError>> {
        let b = if let Ok(rhs) = other.as_isize(vm) {
            self.val < (rhs as f64)
        } else if let Some(rhs) = other.try_downcast::<Double>(vm) {
            self.val < rhs.double()
        } else if let Some(rhs) = other.try_downcast::<ArbInt>(vm) {
            match rhs.bigint().to_f64() {
                Some(i) => self.val < i,
                None => false,
            }
        } else {
            let got = other.dyn_objtype(vm);
            return Err(VMError::new(vm, VMErrorKind::NotANumber { got }));
        };

        Ok(Val::from_bool(vm, b))
    }
}

impl StaticObjType for Double {
    fn static_objtype() -> ObjType {
        ObjType::Double
    }
}

impl Double {
    pub fn new(_: &mut VM, val: f64) -> Val {
        Val::from_obj(Double { val })
    }

    pub fn double(&self) -> f64 {
        self.val
    }

    pub fn as_integer(&self, vm: &mut VM) -> Val {
        // This could be done more efficiently in the common case that self.val will fit in an
        // isize.
        if let Some(bi) = BigInt::from_f64(self.val) {
            ArbInt::new(vm, bi)
        } else {
            todo!();
        }
    }

    pub fn round(&self, vm: &mut VM) -> Val {
        // This could be done more efficiently in the common case that self.val will fit in an
        // isize.
        if let Some(bi) = BigInt::from_f64(self.val.round()) {
            ArbInt::new(vm, bi)
        } else {
            todo!();
        }
    }

    pub fn cos(&self, vm: &mut VM) -> Val {
        Double::new(vm, self.val.cos())
    }

    pub fn sin(&self, vm: &mut VM) -> Val {
        Double::new(vm, self.val.sin())
    }
}
