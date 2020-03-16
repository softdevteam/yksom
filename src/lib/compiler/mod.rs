//! A SOM compiler. This is currently fairly simplistic, particularly in terms of code generation
//! (though it does at least use [lrpar](https://crates.io/crates/lrpar), so one gets decent error
//! messages). The interchange format between the compiler and the VM currently uses a Rust `enum`
//! and is probably fairly inefficient.

use std::{fs, path::Path, process};

use lrlex::lrlex_mod;
use lrpar::lrpar_mod;

use crate::vm::{val::Val, VM};

mod ast;
mod ast_to_instrs;
pub mod instrs;

lrlex_mod!("lib/compiler/som.l");
lrpar_mod!("lib/compiler/som.y");

type StorageT = u32;

/// Compile a class. Should only be called by the `VM`.
pub fn compile(vm: &mut VM, path: &Path) -> (String, Val) {
    let bytes = fs::read(path).unwrap_or_else(|_| panic!("Can't read {}.", path.to_str().unwrap()));
    let txt = String::from_utf8_lossy(&bytes);

    let lexerdef = som_l::lexerdef();
    let lexer = lexerdef.lexer(&txt);
    let (astopt, errs) = som_y::parse(&lexer);
    for e in &errs {
        eprintln!("{}", e.pp(&lexer, &som_y::token_epp));
    }
    match astopt {
        Some(Ok(astcls)) => {
            let (name, cls) = ast_to_instrs::Compiler::compile(vm, &lexer, &path, &astcls)
                .unwrap_or_else(|msg| {
                    eprintln!("{}", msg);
                    process::exit(1);
                });
            if errs.is_empty() {
                (name, cls)
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
