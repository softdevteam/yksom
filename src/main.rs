#![feature(box_patterns)]

use std::{
    env,
    io::{stderr, Write},
    path::Path,
    process,
};

use getopts::Options;

use yksom::vm::{objects::Inst, VMError, VMErrorKind, VM};

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

    let vm = VM::new(matches.opt_strs("cp"));
    let cls = vm.compile(&Path::new(&matches.free[0]).canonicalize().unwrap(), true);
    let app = Inst::new(&vm, cls);
    match vm.top_level_send(app, "run", vec![]) {
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
