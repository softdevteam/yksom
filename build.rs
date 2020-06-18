use cfgrammar::yacc::YaccKind;
use lrlex::LexerBuilder;
use lrpar::CTParserBuilder;
use rerun_except::rerun_except;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    rerun_except(&["/lang_tests/*.som", "SOM"])?;

    let lex_rule_ids_map = CTParserBuilder::new()
        .yacckind(YaccKind::Grmtools)
        .process_file_in_src("lib/compiler/som.y")?;
    LexerBuilder::new()
        .rule_ids_map(lex_rule_ids_map)
        .process_file_in_src("lib/compiler/som.l")?;

    Ok(())
}
