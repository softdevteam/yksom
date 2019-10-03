// Copyright (c) 2019 King's College London created by the Software Development Team
// <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

use std::{
    env,
    io::{stderr, Write},
    path::Path,
    process,
};

use getopts::Options;

use yksom::vm::{objects::Inst, VMError, VM};

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
    let vr = vm.send(app, "run", vec![]);
    if vr.is_err() {
        match *vr.unwrap_err() {
            VMError::Exit => (),
            e => {
                eprintln!("{:?}", e);
                process::exit(1);
            }
        }
    }
}
