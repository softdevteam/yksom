use std::{env, path::PathBuf, process::Command};

use lang_tester::LangTester;
use lazy_static::lazy_static;
use regex::{Regex, RegexBuilder};

const SOM_LIBS_PATH: &'static str = "lib/SOM/";

lazy_static! {
    static ref EXPECTED: Regex = RegexBuilder::new(r#"^"(.*?)^"[ \t]*$"#)
        .multi_line(true)
        .dot_matches_new_line(true)
        .build()
        .unwrap();
}

fn main() {
    LangTester::new()
        .test_dir("lang_tests")
        .test_file_filter(|p| p.extension().unwrap().to_str().unwrap() == "som")
        .test_extract(|s| {
            EXPECTED
                .captures(s)
                .map(|x| x.get(1).unwrap().as_str().trim().to_owned())
        })
        .test_cmds(|p| {
            // We call target/[debug|release]/yksom directly, because it's noticeably faster than
            // calling `cargo run`.
            let mut yksom_bin = PathBuf::new();
            yksom_bin.push(env::var("CARGO_MANIFEST_DIR").unwrap());
            yksom_bin.push("target");
            #[cfg(debug_assertions)]
            yksom_bin.push("debug");
            #[cfg(not(debug_assertions))]
            yksom_bin.push("release");
            yksom_bin.push("yksom");
            let mut vm = Command::new(yksom_bin);
            vm.args(&["--cp", SOM_LIBS_PATH, p.to_str().unwrap()]);
            vec![("VM", vm)]
        })
        .run();
}
