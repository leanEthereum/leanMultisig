use std::collections::BTreeMap;

use pest::iterators::Pair;

use super::{ParseError, Rule, parse_binary_expr, parse_primary};
use crate::{intermediate_bytecode::HighLevelOperation, lang::Expression};

pub(crate) fn parse_expression(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<Expression, ParseError> {
    match pair.as_rule() {
        Rule::expression => parse_expression(pair.into_inner().next().unwrap(), constants),
        Rule::add_expr => parse_binary_expr(pair, constants, HighLevelOperation::Add),
        Rule::sub_expr => parse_binary_expr(pair, constants, HighLevelOperation::Sub),
        Rule::mul_expr => parse_binary_expr(pair, constants, HighLevelOperation::Mul),
        Rule::div_expr => parse_binary_expr(pair, constants, HighLevelOperation::Div),
        Rule::exp_expr => parse_binary_expr(pair, constants, HighLevelOperation::Exp),
        Rule::primary => parse_primary(pair, constants),
        _ => Err(ParseError::SemanticError("Invalid expression".to_string())),
    }
}
