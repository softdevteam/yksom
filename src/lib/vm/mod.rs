// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

/// If a `ValResult` represents an error, percolate it up the call stack.
#[macro_export]
macro_rules! vtry {
    ($elem:expr) => {{
        let o = $elem;
        if o.is_val() {
            unsafe { o.unwrap_unsafe() }
        } else {
            return o;
        }
    }};
}

/// If a `Result<T, Box<VMError>>` represents an error, then convert the `Box<VMError>` into a
/// `ValResult` and percolate that up the call stack.
#[macro_export]
macro_rules! rtry {
    ($elem:expr) => {{
        let e = $elem;
        match e {
            Ok(o) => o,
            Err(e) => return ValResult::from_boxvmerror(e),
        }
    }};
}

pub mod objects;
pub mod val;
pub mod vm;

pub use crate::vm::vm::VM;
