#![feature(box_patterns)]

use std::{
    env,
    io::{stderr, Write},
    path::{Path, PathBuf},
    process,
    str::FromStr,
};

use getopts::Options;

use yksom::vm::{
    objects::{NormalArray, String_},
    VMError, VMErrorKind, VM,
};

use rboehm::BoehmAllocator;

#[global_allocator]
static ALLOCATOR: BoehmAllocator = BoehmAllocator;

fn usage(prog: &str) -> ! {
    let path = Path::new(prog);
    let leaf = path
        .file_name()
        .map(|x| x.to_str().unwrap_or("yksom"))
        .unwrap_or("yksom");
    writeln!(&mut stderr(), "Usage: {} [-h] --cp <path> <file.som>", leaf).ok();
    process::exit(1)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let prog = &args[0];
    let matches = Options::new()
        .optmulti("", "cp", "Path to System classes", "<path>")
        .optflag("h", "help", "")
        .parse(&args[1..])
        .unwrap_or_else(|_| usage(prog));
    if matches.opt_present("h") || matches.free.len() != 1 {
        usage(prog);
    }

    let src_path = &Path::new(&matches.free[0]).canonicalize().unwrap();
    let mut cp = match src_path.parent() {
        Some(p) => vec![p.to_owned()],
        None => vec![],
    };
    cp.extend(
        matches
            .opt_strs("cp")
            .iter()
            .map(|x| PathBuf::from_str(x).unwrap()),
    );

    let mut vm = VM::new(cp);
    let system = vm.get_global_or_nil("system");
    let src_fname = match src_path.file_name().and_then(|x| x.to_str()) {
        Some(x) => x,
        None => todo!(),
    };
    let src_fname_val = String_::new_sym(&mut vm, src_fname.to_owned());
    let args = NormalArray::from_vec(&mut vm, vec![src_fname_val]);
    match vm.top_level_send(system, "initialize:", vec![args]) {
        Ok(_)
        | Err(box VMError {
            kind: VMErrorKind::Exit,
            ..
        }) => (),
        Err(e) => {
            e.console_print(&vm);
            process::exit(1);
        }
    }
}
