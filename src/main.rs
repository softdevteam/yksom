#![feature(allocator_api)]
#![feature(gc)]
#![feature(box_patterns)]
#![feature(rustc_private)]

use std::{
    env,
    io::{stderr, Write},
    path::{Path, PathBuf},
    process,
    str::FromStr,
};

use getopts::Options;
use smartstring::alias::String as SmartString;

use yksom::vm::{
    objects::{NormalArray, String_},
    VMError, VMErrorKind, VM,
};

use std::gc::GcAllocator;

#[global_allocator]
static ALLOCATOR: GcAllocator = GcAllocator;

fn usage(prog: &str) -> ! {
    let path = Path::new(prog);
    let leaf = path
        .file_name()
        .map(|x| x.to_str().unwrap_or("yksom"))
        .unwrap_or("yksom");
    writeln!(
        &mut stderr(),
        "Usage: {} [-h] --cp <path> <file.som> [-- <arg_1> [... <arg_n>]]",
        leaf
    )
    .ok();
    process::exit(1)
}

fn main() {
    let args = env::args().collect::<Vec<_>>();
    let prog = &args[0];
    let matches = Options::new()
        .reqopt(
            "",
            "cp",
            "Path to System classes (directories separated by ':')",
            "<path>",
        )
        .optflag("h", "help", "")
        .parse(&args[1..])
        .unwrap_or_else(|_| usage(prog));
    if matches.opt_present("h") || matches.free.is_empty() {
        usage(prog);
    }

    let src_path = &Path::new(&matches.free[0]).canonicalize().unwrap();
    let mut cp = match src_path.parent() {
        Some(p) => vec![p.to_owned()],
        None => vec![],
    };
    cp.extend(
        matches
            .opt_str("cp")
            .unwrap()
            .split(":")
            .map(|x| PathBuf::from_str(x).unwrap()),
    );

    let mut vm = VM::new(cp);
    let system = vm.get_global_or_nil("system");
    let src_fname = match src_path.file_name().and_then(|x| x.to_str()) {
        Some(x) => x,
        None => todo!(),
    };
    let mut src_fname = PathBuf::from(src_fname);
    src_fname.set_extension("");
    let src_fname_val = String_::new_str(&mut vm, SmartString::from(src_fname.to_str().unwrap()));
    let mut args_vec = vec![src_fname_val];
    args_vec.extend(
        matches
            .free
            .iter()
            .skip(1)
            .map(|x| String_::new_str(&mut vm, SmartString::from(x))),
    );
    let args = NormalArray::from_vec(args_vec);
    match vm.top_level_send(system, "initialize:", vec![args]) {
        Ok(_) => (),
        Err(e) => {
            let code = if let box VMError {
                kind: VMErrorKind::Exit(code),
                ..
            } = e
            {
                code
            } else {
                1
            };
            if code != 0 {
                e.console_print(&vm);
            }
            process::exit(code);
        }
    }
}
