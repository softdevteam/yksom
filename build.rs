use cfgrammar::yacc::YaccKind;
use lrlex::{CTLexerBuilder, DefaultLexerTypes};
use rerun_except::rerun_except;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    rerun_except(&["/lang_tests/*.som", "SOM"])?;

    CTLexerBuilder::<DefaultLexerTypes<u8>>::new_with_lexemet()
        .lrpar_config(|ctp| {
            ctp.yacckind(YaccKind::Grmtools)
                .grammar_in_src_dir("lib/compiler/som.y")
                .unwrap()
        })
        .lexer_in_src_dir("lib/compiler/som.l")?
        .build()?;

    Ok(())
}
