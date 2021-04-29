use std::cell::Cell;

use std::gc::Gc;

use crate::{
    compiler::instrs::{Primitive, UpVarDef},
    vm::{core::VM, objects::Method, val::Val},
};

/// The VM's underlying notion of a SOM function. SOM has two types of functions: methods and
/// blocks. Roughly speaking, methods have names, may reference primitives, but can't be nested;
/// blocks are anonymous, can't reference primitives, but can be nested. Although at a SOM level
/// methods and blocks are separate types, they share nearly everything that makes them
/// function-esque, so to avoid having two separate internal representations, both methods and
/// blocks store `Function`s.
///
/// The main complication in representation is that a `Function` can reference a SOM primitive,
/// which is a very different type of `Function` to a non-primitive. Rather than have two types of
/// `Function`, we store both together: the [Function::is_primitive()] can be used to differentiate
/// the two.
#[derive(Debug)]
pub struct Function {
    /// The number of parameters. Note: always includes the implicit "self" parameter.
    num_params: usize,
    /// The class this function is contained within. Note that we ensure this is set properly for
    /// both methods and blocks.
    holder: Cell<Val>,
    /// The method this function is contained within. Note that for a top-level method this simply
    /// points to the method itself (i.e. it's effectively circular). `Option` is used here solely
    /// to aid bootstrapping: every "live" `Function` is guaranteed to have a containing method.
    containing_method: Cell<Option<Gc<Method>>>,
    // If num_vars==usize::MAX then this is a Primitive function:
    primitive: Option<Primitive>,
    // If num_vars<usize::MAX then this is a bytecode function:
    num_vars: usize,
    /// The offset of this method's bytecode in its parent class.
    bytecode_off: usize,
    /// If this function is a block, this specifies the end of the block's bytecode.
    bytecode_end: usize,
    max_stack: usize,
    upvar_defs: Vec<UpVarDef>,
    /// This function's blocks.
    block_funcs: Vec<Gc<Function>>,
}

impl Function {
    pub fn new_bytecode(
        vm: &VM,
        num_params: usize,
        num_vars: usize,
        bytecode_off: usize,
        bytecode_end: Option<usize>,
        max_stack: usize,
        upvar_defs: Vec<UpVarDef>,
        block_funcs: Vec<Gc<Function>>,
    ) -> Function {
        Function {
            num_params,
            holder: Cell::new(vm.nil),
            containing_method: Cell::new(None),
            primitive: None,
            num_vars,
            bytecode_off,
            bytecode_end: bytecode_end.unwrap_or(usize::MAX),
            max_stack,
            upvar_defs,
            block_funcs,
        }
    }

    pub fn new_primitive(vm: &VM, num_params: usize, primitive: Primitive) -> Function {
        Function {
            num_params,
            holder: Cell::new(vm.nil),
            containing_method: Cell::new(None),
            primitive: Some(primitive),
            num_vars: usize::MAX,
            bytecode_off: usize::MAX,
            bytecode_end: usize::MAX,
            max_stack: usize::MAX,
            upvar_defs: Vec::new(),
            block_funcs: Vec::new(),
        }
    }

    /// Is this `Function` a SOM primitive?
    pub fn is_primitive(&self) -> bool {
        self.num_vars == usize::MAX
    }

    /// If this `Function` is a SOM primitive, return the `Primitive`. Calling this function
    /// without first having confirmed that this `Function` is a SOM primitive is undefined
    /// behaviour.
    pub fn primitive(&self) -> Primitive {
        debug_assert!(self.is_primitive());
        self.primitive.unwrap()
    }

    pub fn num_params(&self) -> usize {
        self.num_params
    }

    pub fn holder(&self) -> Val {
        self.holder.get()
    }

    /// Set this function, and recursively all its nested functions, holder.
    pub fn set_holder(&self, vm: &VM, class: Val) {
        self.holder.set(class);
        for blk in &self.block_funcs {
            blk.set_holder(vm, class);
        }
    }

    pub fn containing_method(&self) -> Gc<Method> {
        self.containing_method.get().unwrap()
    }

    pub fn set_containing_method(&self, meth: Gc<Method>) {
        self.containing_method.set(Some(meth));
    }

    /// If this `Function` is not a SOM primitive, return its number of local variables. Calling
    /// this function without first having confirmed that this `Function` is not a SOM primitive is
    /// undefined behaviour.
    pub fn num_vars(&self) -> usize {
        debug_assert!(!self.is_primitive());
        self.num_vars
    }

    /// If this `Function` is not a SOM primitive, return the start of its bytecode. Calling this
    /// function without first having confirmed that this `Function` is not a SOM primitive is
    /// undefined behaviour.
    pub fn bytecode_off(&self) -> usize {
        debug_assert!(!self.is_primitive());
        self.bytecode_off
    }

    /// If this `Function` is not a SOM primitive, and if this `Function` represents a block,
    /// return the end of its bytecode. Calling this function without first having confirmed that
    /// this `Function` is not a SOM primitive and that it is a block is undefined behaviour.
    pub fn bytecode_end(&self) -> usize {
        debug_assert!(!self.is_primitive());
        self.bytecode_end
    }

    /// If this `Function` is not a SOM primitive, return the maximum number of SOM stack entries
    /// it requires. Calling this function without first having confirmed that this `Function` is
    /// not a SOM primitive is undefined behaviour.
    pub fn max_stack(&self) -> usize {
        debug_assert!(!self.is_primitive());
        self.max_stack
    }

    pub fn block_func(&self, idx: usize) -> Gc<Function> {
        debug_assert!(idx < self.block_funcs.len());
        *unsafe { self.block_funcs.get_unchecked(idx) }
    }

    pub fn upvar_defs(&self) -> &Vec<UpVarDef> {
        &self.upvar_defs
    }

    pub fn block_funcs(&self) -> &Vec<Gc<Function>> {
        &self.block_funcs
    }
}
