#![allow(clippy::new_ret_no_self)]

use std::{cell::UnsafeCell, collections::HashMap, path::PathBuf, str};

use abgc::Gc;
use abgc_derive::GcLayout;

use crate::vm::{
    core::VM,
    error::{VMError, VMErrorKind},
    objects::{Method, Obj, ObjType, StaticObjType},
    val::{NotUnboxable, Val, ValKind},
};

#[derive(Debug, GcLayout)]
pub struct Class {
    metacls: UnsafeCell<Val>,
    pub name: Val,
    pub path: PathBuf,
    /// Offset to this class's instructions in VM::instrs.
    pub instrs_off: usize,
    supercls: UnsafeCell<Val>,
    pub num_inst_vars: usize,
    pub methods: HashMap<String, Gc<Method>>,
}

impl Obj for Class {
    fn dyn_objtype(&self) -> ObjType {
        ObjType::Class
    }

    fn get_class(&self, _: &mut VM) -> Val {
        debug_assert!(unsafe { &*self.metacls.get() }.valkind() != ValKind::ILLEGAL);
        unsafe { &*self.metacls.get() }.clone()
    }
}

impl NotUnboxable for Class {}

impl StaticObjType for Class {
    fn static_objtype() -> ObjType {
        ObjType::Class
    }
}

impl Class {
    pub fn new(
        _: &VM,
        metacls: Val,
        name: Val,
        path: PathBuf,
        instrs_off: usize,
        supercls: Val,
        num_inst_vars: usize,
        methods: HashMap<String, Gc<Method>>,
    ) -> Self {
        Class {
            metacls: UnsafeCell::new(metacls),
            name,
            path,
            instrs_off,
            supercls: UnsafeCell::new(supercls),
            num_inst_vars,
            methods,
        }
    }

    pub fn name(&self, _: &VM) -> Result<Val, Box<VMError>> {
        Ok(self.name.clone())
    }

    pub fn get_method(&self, vm: &VM, msg: &str) -> Result<Gc<Method>, Box<VMError>> {
        self.methods
            .get(msg)
            .map(|x| Ok(Gc::clone(x)))
            .unwrap_or_else(|| {
                let supercls = self.supercls(vm);
                if supercls != vm.nil {
                    supercls.downcast::<Class>(vm)?.get_method(vm, msg)
                } else {
                    Err(VMError::new(vm, VMErrorKind::UnknownMethod(msg.to_owned())))
                }
            })
    }

    pub fn set_metacls(&self, _: &VM, cls: Val) {
        *unsafe { &mut *self.metacls.get() } = cls;
    }

    pub fn supercls(&self, _: &VM) -> Val {
        unsafe { &*self.supercls.get() }.clone()
    }

    pub fn set_supercls(&self, _: &VM, cls: Val) {
        *unsafe { &mut *self.supercls.get() } = cls;
    }
}
