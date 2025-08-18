use std::collections::BTreeMap;

use pest::Parser;

use super::{LangParser, ParseError, Rule, parse_function, remove_comments};
use crate::parser::{Program, parse_constant_declaration};

pub fn parse_program(input: &str) -> Result<Program, ParseError> {
    let input = remove_comments(input);
    let mut pairs = LangParser::parse(Rule::program, &input)?;
    let program_pair = pairs.next().unwrap();

    let mut constants = BTreeMap::new();
    let mut functions = BTreeMap::new();
    let mut trash_var_count = 0;

    for pair in program_pair.into_inner() {
        match pair.as_rule() {
            Rule::constant_declaration => {
                let (name, value) = parse_constant_declaration(pair, &constants)?;
                constants.insert(name, value);
            }
            Rule::function => {
                let function = parse_function(pair, &constants, &mut trash_var_count)?;
                functions.insert(function.name.clone(), function);
            }
            Rule::EOI => break,
            _ => {}
        }
    }

    Ok(Program { functions })
}
