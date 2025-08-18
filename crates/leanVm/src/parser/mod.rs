use std::collections::BTreeMap;

use p3_field::{PrimeCharacteristicRing, PrimeField};
use pest::{Parser, iterators::Pair};
use pest_derive::Parser;

use crate::{
    bytecode::precompiles::PRECOMPILES,
    constant::F,
    intermediate_bytecode::HighLevelOperation,
    lang::{
        Boolean, ConstExpression, ConstantValue, Expression, Function, Line, Program, SimpleExpr,
    },
};

pub mod error;
pub use error::*;

#[derive(Parser, Debug)]
#[grammar = "grammar.pest"]
pub struct LangParser;

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

fn remove_comments(input: &str) -> String {
    input
        .lines()
        .map(|line| line.find("//").map_or(line, |pos| &line[..pos]))
        .collect::<Vec<_>>()
        .join("\n")
}

fn parse_constant_declaration(
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

fn parse_function(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
    trash_var_count: &mut usize,
) -> Result<Function, ParseError> {
    let mut inner = pair.into_inner();
    let name = inner.next().unwrap().as_str().to_string();

    let mut arguments = Vec::new();
    let mut n_returned_vars = 0;
    let mut body = Vec::new();

    for pair in inner {
        match pair.as_rule() {
            Rule::parameter_list => {
                for param in pair.into_inner() {
                    if param.as_rule() == Rule::parameter {
                        let parameter_name = parse_parameter(param)?;
                        arguments.push(parameter_name);
                    }
                }
            }
            Rule::return_count => {
                let count_str = pair.into_inner().next().unwrap().as_str();
                n_returned_vars = constants
                    .get(count_str)
                    .copied()
                    .or_else(|| count_str.parse().ok())
                    .ok_or_else(|| ParseError::SemanticError("Invalid return count".to_string()))?;
            }
            Rule::statement => {
                body.push(parse_statement(pair, constants, trash_var_count)?);
            }
            _ => {}
        }
    }

    Ok(Function {
        name,
        arguments,
        n_returned_vars,
        body,
    })
}

fn parse_parameter(pair: Pair<'_, Rule>) -> Result<(String, bool), ParseError> {
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

fn parse_statement(
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

fn parse_if_statement(
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

fn parse_assignment(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<Line, ParseError> {
    let mut inner = pair.into_inner();
    let var = inner.next().unwrap().as_str().to_string();
    let expr = inner.next().unwrap();
    let value = parse_expression(expr, constants)?;

    Ok(Line::Assignment { var, value })
}

fn parse_array_assign(
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

fn parse_for_statement(
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

fn parse_return_statement(
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

fn parse_expression(
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

fn parse_array_access(
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

fn parse_binary_expr(
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

fn parse_primary(
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

fn parse_tuple_expression(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<Vec<Expression>, ParseError> {
    pair.into_inner()
        .map(|item| parse_expression(item, constants))
        .collect()
}

#[allow(clippy::too_many_lines)]
fn parse_function_call(
    pair: &Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
    trash_var_count: &mut usize,
) -> Result<Line, ParseError> {
    let inner = pair.clone().into_inner();
    let mut return_data = Vec::new();
    let mut function_name = String::new();
    let mut args = Vec::new();

    for item in inner {
        match item.as_rule() {
            Rule::function_res => {
                for res_item in item.into_inner() {
                    if res_item.as_rule() == Rule::var_list {
                        return_data = parse_var_list(res_item, constants)?
                            .into_iter()
                            .filter_map(|v| {
                                if let SimpleExpr::Var(var) = v {
                                    Some(var)
                                } else {
                                    None
                                }
                            })
                            .collect();
                    }
                }
            }
            Rule::identifier => function_name = item.as_str().to_string(),
            Rule::tuple_expression => args = parse_tuple_expression(item, constants)?,
            _ => {}
        }
    }

    for var in &mut return_data {
        if var == "_" {
            *trash_var_count += 1;
            *var = format!("@trash_{trash_var_count}");
        }
    }

    match function_name.as_str() {
        "malloc" => {
            assert!(
                args.len() == 1 && return_data.len() == 1,
                "Invalid malloc call"
            );
            Ok(Line::MAlloc {
                var: return_data[0].clone(),
                size: args[0].clone(),
                vectorized: false,
            })
        }
        "malloc_vec" => {
            assert!(
                args.len() == 1 && return_data.len() == 1,
                "Invalid malloc_vec call"
            );
            Ok(Line::MAlloc {
                var: return_data[0].clone(),
                size: args[0].clone(),
                vectorized: true,
            })
        }
        "print" => {
            assert!(
                return_data.is_empty(),
                "Print function should not return values"
            );
            Ok(Line::Print {
                line_info: pair.as_str().to_string(),
                content: args,
            })
        }
        "decompose_bits" => {
            assert!(
                args.len() == 1 && return_data.len() == 1,
                "Invalid decompose_bits call"
            );
            Ok(Line::DecomposeBits {
                var: return_data[0].clone(),
                to_decompose: args[0].clone(),
            })
        }
        "panic" => {
            assert!(
                return_data.is_empty() && args.is_empty(),
                "Panic has no args and returns no values"
            );
            Ok(Line::Panic)
        }
        _ => {
            if let Some(precompile) = PRECOMPILES
                .iter()
                .find(|p| p.name.to_string() == function_name)
            {
                assert!(
                    args.len() == precompile.n_inputs && return_data.len() == precompile.n_outputs,
                    "Invalid precompile call"
                );
                Ok(Line::Precompile {
                    precompile: precompile.clone(),
                    args,
                    res: return_data,
                })
            } else {
                Ok(Line::FunctionCall {
                    function_name,
                    args,
                    return_data,
                })
            }
        }
    }
}

fn parse_condition(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<Boolean, ParseError> {
    let inner = pair.into_inner().next().unwrap();
    let mut parts = inner.clone().into_inner();
    let left = parse_expression(parts.next().unwrap(), constants)?;
    let right = parse_expression(parts.next().unwrap(), constants)?;

    match inner.as_rule() {
        Rule::condition_eq => Ok(Boolean::Equal { left, right }),
        Rule::condition_diff => Ok(Boolean::Different { left, right }),
        _ => unreachable!(),
    }
}

fn parse_assert_eq(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<Line, ParseError> {
    let mut inner = pair.into_inner();
    let left = parse_expression(inner.next().unwrap(), constants)?;
    let right = parse_expression(inner.next().unwrap(), constants)?;
    Ok(Line::Assert(Boolean::Equal { left, right }))
}

fn parse_assert_not_eq(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<Line, ParseError> {
    let mut inner = pair.into_inner();
    let left = parse_expression(inner.next().unwrap(), constants)?;
    let right = parse_expression(inner.next().unwrap(), constants)?;
    Ok(Line::Assert(Boolean::Different { left, right }))
}

fn parse_var_or_constant(
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

fn parse_var_list(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<Vec<SimpleExpr>, ParseError> {
    pair.into_inner()
        .map(|item| parse_var_or_constant(item, constants))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parser() {
        let program = r"

// This is a comment

const A = 10000;
const B = 20000;
// Another comment

fn main() {
// this a comment

    c = a + b;
    assert c == d;
    if c != b { // this a comment
        d = 1;
        e = 9;
        f = d * ((a - b) + ((h / 1) + d));
    } else {
        f = 8;
    }
    assert f != g;
    oo = memory[B];
    x = 8;
    y = 9;
    uuu = y[9];
    vvv = y[uuu];

    gh = memory[7];
    hh = memory[gh];

    print(hh);

    xx= poseidon16(x, y);
    xxx = poseidon24(7, b);

    k = public_input_start;

    for i in a..(b + 9) * ( 7 - 7 ) {
        assert i != d;
    }

    for i in a..(b + 9) * ( 7 - 7 ) unroll {
        assert i != d;
    }

    i, j, k = my_function1(b, b, a);
}

fn my_function1(a, const b, c) -> 2 {
    d = a + b;
    e = b + c;
    if e == e {
        return 0, 0;
    }
    if d != e {
        return d, e;
    } else {
        return e, d;
    }
}
    ";

        let parsed = parse_program(program).unwrap();
        println!("{parsed}");
    }

    #[test]
    fn test_const_parameters() {
        let program = r"
fn test_func(const a, b, const c) -> 1 {
    d = a + b + c;
    return d;
}
    ";

        let parsed = parse_program(program).unwrap();
        println!("{parsed}");
    }

    #[test]
    fn test_exponent_operation() {
        let program = r"
fn test_exp() -> 1 {
    a = 2 ** 3;
    b = x ** y ** z;  // Should parse as x ** (y ** z)
    c = (a + b) ** 2;
    d = a ** 2 * b;   // Should parse as (a ** 2) * b
    return a;
}
    ";

        let parsed = parse_program(program).unwrap();
        println!("{parsed}");
    }
}
