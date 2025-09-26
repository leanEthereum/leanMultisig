use super::function::FunctionParser;
use super::literal::ConstantDeclarationParser;
use super::{Parse, ParseContext};
use crate::{
    lang::Program,
    parser::{
        error::{ParseResult, SemanticError},
        grammar::{ParsePair, Rule},
    },
};
use std::collections::BTreeMap;

/// Parser for complete programs.
pub struct ProgramParser;

impl Parse<(Program, BTreeMap<usize, String>)> for ProgramParser {
    fn parse(
        pair: ParsePair<'_>,
        _ctx: &mut ParseContext,
    ) -> ParseResult<(Program, BTreeMap<usize, String>)> {
        let mut ctx = ParseContext::new();
        let mut functions = BTreeMap::new();
        let mut function_locations = BTreeMap::new();

        for item in pair.into_inner() {
            match item.as_rule() {
                Rule::constant_declaration => {
                    let (name, value) = ConstantDeclarationParser::parse(item, &mut ctx)?;
                    ctx.add_constant(name, value)?;
                }
                Rule::function => {
                    let location = item.line_col().0;
                    let function = FunctionParser::parse(item, &mut ctx)?;
                    let name = function.name.clone();

                    function_locations.insert(location, name.clone());

                    if functions.insert(name.clone(), function).is_some() {
                        return Err(SemanticError::with_context(
                            format!("Multiply defined function: {}", name),
                            "function definition",
                        )
                        .into());
                    }
                }
                Rule::EOI => break,
                _ => {} // Skip other rules
            }
        }

        Ok((Program { functions }, function_locations))
    }
}
