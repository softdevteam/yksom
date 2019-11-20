//! A [SOM](http://som-st.github.io/) VM in Rust. SOM is a cut-down Smalltalk-like
//! language. yksom is eventually intended to be used with
//! [Yorick](https://github.com/softdevteam/yk/) to produce a JIT-compiling VM,
//! though it is currently an entirely stand-alone interpreter. Currently it is
//! partly a test bed to experiment with good ways of structuring Rust
//! interpreters, balancing correctness, performance, and readability.
//!
//! yksom is split into a compiler and run-time. The compiler parses SOM programs and creates the
//! run-time structures that the run-time can then execute. As this suggests, the compiler can
//! operate at run-time, so there is a fairly tight inter-weaving between the compiler and
//! run-time.

#![feature(alloc_layout_extra)]
#![feature(allocator_api)]
#![feature(coerce_unsized)]
#![feature(specialization)]
#![feature(unsize)]
#![allow(clippy::cognitive_complexity)]
#![allow(clippy::float_cmp)]
#![allow(clippy::never_loop)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]

pub mod compiler;
pub mod vm;
