use std::collections::BTreeMap;

use pest::iterators::Pair;

use super::{
    ParseError, Rule, parse_assert_eq, parse_assert_not_eq, parse_assignment, parse_for_statement,
    parse_function_call,
};
use crate::{
    lang::Line,
    parser::{parse_array_assign, parse_condition, parse_return_statement},
};

pub(crate) fn parse_statement(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
    trash_var_count: &mut usize,
) -> Result<Line, ParseError> {
    let inner = pair.into_inner().next().unwrap();

    match inner.as_rule() {
        Rule::single_assignment => parse_assignment(inner, constants),
        Rule::array_assign => parse_array_assign(inner, constants),
        Rule::if_statement => parse_if_statement(inner, constants, trash_var_count),
        Rule::for_statement => parse_for_statement(inner, constants, trash_var_count),
        Rule::return_statement => parse_return_statement(inner, constants),
        Rule::function_call => parse_function_call(&inner, constants, trash_var_count),
        Rule::assert_eq_statement => parse_assert_eq(inner, constants),
        Rule::assert_not_eq_statement => parse_assert_not_eq(inner, constants),
        Rule::break_statement => Ok(Line::Break),
        Rule::continue_statement => todo!("Continue statement not implemented yet"),
        _ => Err(ParseError::SemanticError("Unknown statement".to_string())),
    }
}

pub(crate) fn parse_if_statement(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
    trash_var_count: &mut usize,
) -> Result<Line, ParseError> {
    let mut inner = pair.into_inner();
    let condition = parse_condition(inner.next().unwrap(), constants)?;

    let mut then_branch = Vec::new();
    let mut else_branch = Vec::new();

    for item in inner {
        match item.as_rule() {
            Rule::statement => then_branch.push(parse_statement(item, constants, trash_var_count)?),
            Rule::else_clause => {
                for else_item in item.into_inner() {
                    if else_item.as_rule() == Rule::statement {
                        else_branch.push(parse_statement(else_item, constants, trash_var_count)?);
                    }
                }
            }
            _ => {}
        }
    }

    Ok(Line::IfCondition {
        condition,
        then_branch,
        else_branch,
    })
}
