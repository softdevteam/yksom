// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

//! A SOM compiler. This is currently fairly simplistic, particularly in terms of code generation
//! (though it does at least use [lrpar](https://crates.io/crates/lrpar), so one gets decent error
//! messages). The interchange format between the compiler and the VM currently uses a Rust `enum`
//! and is probably fairly inefficient.

use std::{fs, path::Path, process};

use lrlex::lrlex_mod;
use lrpar::lrpar_mod;

mod ast;
mod ast_to_instrs;
pub mod cobjects;
pub mod instrs;

lrlex_mod!(som_l);
lrpar_mod!(som_y);

type StorageT = u32;

/// Compile a class. Should only be called by the `VM`.
pub fn compile(path: &Path) -> cobjects::Class {
    let bytes = fs::read(path).unwrap_or_else(|_| panic!("Can't read {}.", path.to_str().unwrap()));
    let txt = String::from_utf8_lossy(&bytes);

    let lexerdef = som_l::lexerdef();
    let mut lexer = lexerdef.lexer(&txt);
    let (astopt, errs) = som_y::parse(&mut lexer);
    for e in &errs {
        eprintln!("{}", e.pp(&lexer, &som_y::token_epp));
    }
    match astopt {
        Some(Ok(astcls)) => {
            let cls =
                ast_to_instrs::Compiler::compile(&lexer, &path, &astcls).unwrap_or_else(|msg| {
                    eprintln!("{}", msg);
                    process::exit(1);
                });
            if errs.is_empty() {
                cls
            } else {
                process::exit(1);
            }
        }
        _ => {
            eprintln!("Unable to compile {}", path.to_str().unwrap());
            process::exit(1);
        }
    }
}
