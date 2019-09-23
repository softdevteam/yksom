// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

//! A [SOM](http://som-st.github.io/) VM in Rust. SOM is a cut-down Smalltalk-like
//! language. yksom is eventually intended to be used with
//! [Yorick](https://github.com/softdevteam/yk/) to produce a JIT-compiling VM,
//! though it is currently an entirely stand-alone interpreter. Currently it is
//! partly a test bed to experiment with good ways of structuring Rust
//! interpreters, balancing correctness, performance, and readability.
//!
//! yksom is split into a compiler and run-time. The compiler parses SOM programs
//! and converts them into an internal format that the run-time can then execute.

#![feature(alloc_layout_extra)]
#![feature(allocator_api)]
#![feature(coerce_unsized)]
#![feature(specialization)]
#![feature(unsize)]
#![allow(clippy::cognitive_complexity)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]

pub mod compiler;
pub mod vm;
