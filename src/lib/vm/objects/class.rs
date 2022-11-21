#![allow(clippy::new_ret_no_self)]

use std::{
    cell::{Cell, UnsafeCell},
    collections::hash_map::{DefaultHasher, HashMap},
    hash::Hasher,
    path::PathBuf,
    str,
};

use smartstring::alias::String as SmartString;
use std::gc::{Gc, NonFinalizable};

use crate::vm::{
    core::VM,
    error::{VMError, VMErrorKind},
    objects::{Array, Method, MethodsArray, NormalArray, Obj, ObjType, StaticObjType, String_},
    val::{NotUnboxable, Val, ValKind},
};

#[derive(Debug)]
pub struct Class {
    metacls: Cell<Val>,
    name: Cell<Val>,
    pub path: PathBuf,
    /// Offset to this class's instructions in VM::instrs.
    pub instrs_off: usize,
    supercls: Cell<Val>,
    pub inst_vars_map: NonFinalizable<HashMap<SmartString, usize>>,
    /// A SOM Array of methods (though note that it is *not* guaranteed that these definitely point
    /// to SOM `Method` instances -- anything can be stored in this array!).
    methods: Val,
    /// A map from method names to indexes into the methods SOM Array. Note that indexes are stored
    /// with SOM indexing (starting from 1). We guarantee that the indexes are valid indexes for
    /// the `methods` array.
    methods_map: NonFinalizable<HashMap<SmartString, usize>>,
    inst_vars: UnsafeCell<Vec<Val>>,
}

// This is safe because there is no non-GC'd shared ownership inside `Class`.
// This means that even though a finalizer will call its drop methods in another
// thread, it is guaranteed that the finalizer thread will be the only thread
// accessing its data.
unsafe impl FinalizerSafe for Class {}

impl Obj for Class {
    fn dyn_objtype(self: Gc<Self>) -> ObjType {
        ObjType::Class
    }

    fn get_class(self: Gc<Self>, _: &mut VM) -> Val {
        debug_assert!(self.metacls.get().valkind() != ValKind::ILLEGAL);
        self.metacls.get()
    }

    fn num_inst_vars(self: Gc<Self>, _: &VM) -> usize {
        let inst_vars = unsafe { &*self.inst_vars.get() };
        inst_vars.len()
    }

    unsafe fn unchecked_inst_var_get(self: Gc<Self>, vm: &VM, n: usize) -> Val {
        debug_assert!(n < self.num_inst_vars(vm));
        let inst_vars = &mut *self.inst_vars.get();
        inst_vars[n]
    }

    unsafe fn unchecked_inst_var_set(self: Gc<Self>, vm: &VM, n: usize, v: Val) {
        debug_assert!(n < self.num_inst_vars(vm));
        let inst_vars = &mut *self.inst_vars.get();
        inst_vars[n] = v;
    }

    fn hashcode(self: Gc<Self>) -> u64 {
        let mut hasher = DefaultHasher::new();
        hasher.write_usize(Gc::as_ptr(&self) as *const _ as usize);
        hasher.finish()
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
        vm: &VM,
        metacls: Val,
        name: Val,
        path: PathBuf,
        instrs_off: usize,
        supercls: Val,
        inst_vars_map: NonFinalizable<HashMap<SmartString, usize>>,
        methods: Val,
        methods_map: NonFinalizable<HashMap<SmartString, usize>>,
    ) -> Val {
        #[cfg(debug_assertions)]
        {
            // We later use the indexes in methods_map with Array::unchecked_at, so we make sure at
            // this point that they really are safe to use.
            let arr = methods.downcast::<MethodsArray>(vm).unwrap();
            for i in methods_map.values() {
                debug_assert!(*i > 0);
                debug_assert!(*i <= arr.length());
            }
        }

        let cls_val = Val::from_obj(Class {
            metacls: Cell::new(metacls),
            name: Cell::new(name),
            path,
            instrs_off,
            supercls: Cell::new(supercls),
            inst_vars_map,
            methods,
            methods_map,
            inst_vars: UnsafeCell::new(vec![]),
        });
        let cls = cls_val.downcast::<Class>(vm).unwrap();
        cls.set_metacls(vm, metacls);
        cls_val
    }

    pub fn name(&self, _: &VM) -> Result<Val, Box<VMError>> {
        Ok(self.name.get())
    }

    pub fn get_method(&self, vm: &VM, msg: &str) -> Result<Gc<Method>, Box<VMError>> {
        match self.methods_map.get(msg) {
            Some(i) => {
                let arr = self.methods.downcast::<MethodsArray>(vm).unwrap();
                unsafe { arr.unchecked_at(*i) }.downcast(vm)
            }
            None => {
                let supercls = self.supercls(vm);
                if supercls != vm.nil {
                    if let Ok(m) = supercls.downcast::<Class>(vm)?.get_method(vm, msg) {
                        return Ok(m);
                    }
                }
                Err(VMError::new(vm, VMErrorKind::UnknownMethod))
            }
        }
    }

    pub fn set_metacls(&self, vm: &VM, cls_val: Val) {
        // This method is called during VM bootstrapping when not all objects have valid
        // references.
        if cls_val.valkind() != ValKind::ILLEGAL {
            let cls: Gc<Class> = cls_val.downcast(vm).unwrap();
            let mut inst_vars = Vec::with_capacity(cls.inst_vars_map.len());
            inst_vars.resize(cls.inst_vars_map.len(), vm.nil);
            self.metacls.set(cls_val);
            *unsafe { &mut *self.inst_vars.get() } = inst_vars;
        }
    }

    pub fn supercls(&self, _: &VM) -> Val {
        self.supercls.get()
    }

    pub fn set_supercls(&self, _: &VM, cls: Val) {
        self.supercls.set(cls);
    }

    pub fn set_methods_class(&self, vm: &VM, cls: Val) {
        for meth_val in self.methods.downcast::<MethodsArray>(vm).unwrap().iter() {
            let meth = meth_val.downcast::<Method>(vm).unwrap();
            meth.func.set_holder(vm, cls);
        }
    }

    pub fn bootstrap(&self, vm: &VM) {
        self.name
            .get()
            .downcast::<String_>(vm)
            .unwrap()
            .set_cls(vm.sym_cls);
        for meth_val in self.methods.downcast::<MethodsArray>(vm).unwrap().iter() {
            let meth = meth_val.downcast::<Method>(vm).unwrap();
            meth.bootstrap(vm);
        }
    }

    pub fn fields(&self, vm: &mut VM) -> Val {
        let field_strs = self
            .inst_vars_map
            .keys()
            .map(|k| String_::new_sym(vm, k.clone()))
            .collect();
        NormalArray::from_vec(field_strs)
    }

    pub fn methods(&self, _: &VM) -> Val {
        self.methods
    }
}
