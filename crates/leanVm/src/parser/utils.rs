use std::collections::BTreeMap;

use p3_field::{PrimeCharacteristicRing, PrimeField};
use pest::iterators::Pair;

use super::{ParseError, Rule, parse_expression, parse_statement};
use crate::{
    constant::F,
    intermediate_bytecode::HighLevelOperation,
    lang::{Boolean, ConstExpression, ConstantValue, Expression, Line, SimpleExpr},
};

pub(crate) fn remove_comments(input: &str) -> String {
    input
        .lines()
        .map(|line| line.find("//").map_or(line, |pos| &line[..pos]))
        .collect::<Vec<_>>()
        .join("\n")
}

pub(crate) fn parse_var_list(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<Vec<SimpleExpr>, ParseError> {
    pair.into_inner()
        .map(|item| parse_var_or_constant(item, constants))
        .collect()
}

pub(crate) fn parse_assert_not_eq(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<Line, ParseError> {
    let mut inner = pair.into_inner();
    let left = parse_expression(inner.next().unwrap(), constants)?;
    let right = parse_expression(inner.next().unwrap(), constants)?;
    Ok(Line::Assert(Boolean::Different { left, right }))
}

pub(crate) fn parse_assert_eq(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<Line, ParseError> {
    let mut inner = pair.into_inner();
    let left = parse_expression(inner.next().unwrap(), constants)?;
    let right = parse_expression(inner.next().unwrap(), constants)?;
    Ok(Line::Assert(Boolean::Equal { left, right }))
}

pub(crate) fn parse_tuple_expression(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<Vec<Expression>, ParseError> {
    pair.into_inner()
        .map(|item| parse_expression(item, constants))
        .collect()
}

pub(crate) fn parse_constant_declaration(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<(String, usize), ParseError> {
    let mut inner = pair.into_inner();
    let name = inner.next().unwrap().as_str().to_string();
    let value = parse_expression(inner.next().unwrap(), constants)?;
    let value = value
        .eval_with(
            &|simple_expr| match simple_expr {
                SimpleExpr::Constant(cst) => cst.naive_eval(),
                SimpleExpr::Var(var) => constants.get(var).map(|f| F::from_usize(*f)),
                SimpleExpr::ConstMallocAccess { .. } => unreachable!(),
            },
            &|_, _| None,
        )
        .unwrap_or_else(|| panic!("Failed to evaluate constant: {name}"))
        .as_canonical_biguint()
        .try_into()
        .unwrap();
    Ok((name, value))
}

pub(crate) fn parse_parameter(pair: Pair<'_, Rule>) -> Result<(String, bool), ParseError> {
    let mut inner = pair.into_inner();
    let first = inner.next().unwrap();

    if first.as_rule() == Rule::const_keyword {
        // If the first token is "const", the next one should be the identifier
        let identifier = inner.next().ok_or_else(|| {
            ParseError::SemanticError("Expected identifier after 'const'".to_string())
        })?;
        return Ok((identifier.as_str().to_string(), true));
    }

    Ok((first.as_str().to_string(), false))
}

pub(crate) fn parse_assignment(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<Line, ParseError> {
    let mut inner = pair.into_inner();
    let var = inner.next().unwrap().as_str().to_string();
    let expr = inner.next().unwrap();
    let value = parse_expression(expr, constants)?;

    Ok(Line::Assignment { var, value })
}

pub(crate) fn parse_array_assign(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<Line, ParseError> {
    let mut inner = pair.into_inner();
    let array = inner.next().unwrap().as_str().to_string();
    let index = parse_expression(inner.next().unwrap(), constants)?;
    let value = parse_expression(inner.next().unwrap(), constants)?;
    Ok(Line::ArrayAssign {
        array,
        index,
        value,
    })
}

pub(crate) fn parse_for_statement(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
    trash_var_count: &mut usize,
) -> Result<Line, ParseError> {
    let mut inner = pair.into_inner();
    let iterator = inner.next().unwrap().as_str().to_string();
    let start = parse_expression(inner.next().unwrap(), constants)?;
    let end = parse_expression(inner.next().unwrap(), constants)?;

    let mut unroll = false;
    let mut body = Vec::new();

    for item in inner {
        match item.as_rule() {
            Rule::unroll_clause => {
                unroll = true;
            }
            Rule::statement => {
                body.push(parse_statement(item, constants, trash_var_count)?);
            }
            _ => {}
        }
    }

    Ok(Line::ForLoop {
        iterator,
        start,
        end,
        body,
        unroll,
    })
}

pub(crate) fn parse_return_statement(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<Line, ParseError> {
    let mut return_data = Vec::new();
    for item in pair.into_inner() {
        if item.as_rule() == Rule::tuple_expression {
            return_data = parse_tuple_expression(item, constants)?;
        }
    }
    Ok(Line::FunctionRet { return_data })
}

pub(crate) fn parse_array_access(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<Expression, ParseError> {
    let mut inner = pair.into_inner();
    let array = inner.next().unwrap().as_str().to_string();
    let index = parse_expression(inner.next().unwrap(), constants)?;
    Ok(Expression::ArrayAccess {
        array,
        index: Box::new(index),
    })
}

pub(crate) fn parse_binary_expr(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
    operation: HighLevelOperation,
) -> Result<Expression, ParseError> {
    let mut inner = pair.into_inner();
    let mut expr = parse_expression(inner.next().unwrap(), constants)?;

    for right in inner {
        let right_expr = parse_expression(right, constants)?;
        expr = Expression::Binary {
            left: Box::new(expr),
            operation,
            right: Box::new(right_expr),
        };
    }

    Ok(expr)
}

pub(crate) fn parse_primary(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<Expression, ParseError> {
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::expression => parse_expression(inner, constants),
        Rule::var_or_constant => Ok(Expression::Value(parse_var_or_constant(inner, constants)?)),
        Rule::array_access_expr => parse_array_access(inner, constants),
        _ => Err(ParseError::SemanticError(
            "Invalid primary expression".to_string(),
        )),
    }
}

pub(crate) fn parse_var_or_constant(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<SimpleExpr, ParseError> {
    let text = pair.as_str();

    match pair.as_rule() {
        Rule::var_or_constant => {
            parse_var_or_constant(pair.into_inner().next().unwrap(), constants)
        }
        Rule::identifier | Rule::constant_value => match text {
            "public_input_start" => Ok(SimpleExpr::Constant(ConstExpression::Value(
                ConstantValue::PublicInputStart,
            ))),
            "pointer_to_zero_vector" => Ok(SimpleExpr::Constant(ConstExpression::Value(
                ConstantValue::PointerToZeroVector,
            ))),
            _ => constants.get(text).map_or_else(
                || {
                    text.parse::<usize>().map_or_else(
                        |_| Ok(SimpleExpr::Var(text.to_string())),
                        |value| {
                            Ok(SimpleExpr::Constant(ConstExpression::Value(
                                ConstantValue::Scalar(value),
                            )))
                        },
                    )
                },
                |value| {
                    Ok(SimpleExpr::Constant(ConstExpression::Value(
                        ConstantValue::Scalar(*value),
                    )))
                },
            ),
        },
        _ => Err(ParseError::SemanticError(
            "Expected identifier or constant".to_string(),
        )),
    }
}
