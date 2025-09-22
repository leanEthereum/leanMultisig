use crate::intermediate_bytecode::*;
use crate::lang::*;
use crate::precompiles::PRECOMPILES;
use lean_vm::*;
use p3_field::PrimeCharacteristicRing;
use pest::Parser;
use pest::iterators::Pair;
use pest_derive::Parser;
use std::collections::BTreeMap;
use utils::ToUsize;

#[derive(Parser)]
#[grammar = "grammar.pest"]
pub struct LangParser;

#[derive(Debug)]
pub enum ParseError {
    PestError(Box<pest::error::Error<Rule>>),
    SemanticError(String),
}

impl From<pest::error::Error<Rule>> for ParseError {
    fn from(error: pest::error::Error<Rule>) -> Self {
        Self::PestError(Box::new(error))
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PestError(e) => write!(f, "Parse error: {e}"),
            Self::SemanticError(e) => write!(f, "Semantic error: {e}"),
        }
    }
}

impl std::error::Error for ParseError {}

pub fn parse_program(input: &str) -> Result<(Program, BTreeMap<usize, String>), ParseError> {
    let input = remove_comments(input);
    let mut pairs = LangParser::parse(Rule::program, &input)?;
    let program_pair = pairs.next().unwrap();

    let mut constants = BTreeMap::new();
    let mut functions = BTreeMap::new();
    let mut trash_var_count = 0;

    let mut function_locations = BTreeMap::new();

    for pair in program_pair.into_inner() {
        match pair.as_rule() {
            Rule::constant_declaration => {
                let (name, value) = parse_constant_declaration(pair, &constants)?;
                if constants.insert(name.clone(), value).is_some() {
                    panic!("Multiply defined constant: {name}");
                }
            }
            Rule::function => {
                let location = pair.line_col().0;
                let function = parse_function(pair, &constants, &mut trash_var_count)?;
                let name = function.name.clone();
                function_locations.insert(location, name.clone());
                if functions.insert(name.clone(), function).is_some() {
                    panic!("Multiply defined function: {name}");
                }
            }
            Rule::EOI => break,
            _ => {}
        }
    }

    Ok((Program { functions }, function_locations))
}

fn remove_comments(input: &str) -> String {
    input
        .lines()
        .map(|line| {
            if let Some(pos) = line.find("//") {
                &line[..pos]
            } else {
                line
            }
        })
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
        .to_usize();
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
    let mut inlined = false;
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
            Rule::inlined_statement => {
                inlined = true;
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
                on_new_located_line(
                    &mut body,
                    parse_statement(pair, constants, trash_var_count)?,
                );
            }
            _ => {}
        }
    }

    Ok(Function {
        name,
        arguments,
        inlined,
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

fn on_new_located_line(lines: &mut Vec<Line>, line_and_location: (Line, SourceLineNumber)) {
    let (line, location) = line_and_location;
    lines.push(Line::LocationReport { location });
    lines.push(line);
}

fn parse_statement(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
    trash_var_count: &mut usize,
) -> Result<(Line, SourceLineNumber), ParseError> {
    let location = pair.line_col().0;
    let inner = pair.into_inner().next().unwrap();
    let line = match inner.as_rule() {
        Rule::single_assignment => parse_assignment(inner, constants),
        Rule::array_assign => parse_array_assign(inner, constants),
        Rule::if_statement => parse_if_statement(inner, constants, trash_var_count),
        Rule::for_statement => parse_for_statement(inner, constants, trash_var_count),
        Rule::match_statement => parse_match_statement(inner, constants, trash_var_count),
        Rule::return_statement => parse_return_statement(inner, constants),
        Rule::function_call => parse_function_call(inner, constants, trash_var_count),
        Rule::assert_eq_statement => parse_assert_eq(inner, constants),
        Rule::assert_not_eq_statement => parse_assert_not_eq(inner, constants),
        Rule::break_statement => Ok(Line::Break),
        Rule::continue_statement => todo!("Continue statement not implemented yet"),
        _ => Err(ParseError::SemanticError("Unknown statement".to_string())),
    }?;
    Ok((line, location))
}

fn parse_match_statement(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
    trash_var_count: &mut usize,
) -> Result<Line, ParseError> {
    let mut inner = pair.into_inner();
    let value = parse_expression(inner.next().unwrap(), constants)?;

    let mut arms = Vec::new();

    for arm_pair in inner {
        assert_eq!(arm_pair.as_rule(), Rule::match_arm);
        let mut arm_inner = arm_pair.into_inner();
        let const_expr = arm_inner.next().unwrap();
        let pattern = parse_const_expr(const_expr, constants)?;

        let mut statements = Vec::new();
        for stmt in arm_inner {
            if stmt.as_rule() == Rule::statement {
                on_new_located_line(
                    &mut statements,
                    parse_statement(stmt, constants, trash_var_count)?,
                );
            }
        }

        arms.push((pattern, statements));
    }

    Ok(Line::Match { value, arms })
}

fn parse_const_expr(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<usize, ParseError> {
    let inner = pair.into_inner().next().unwrap();

    match inner.as_rule() {
        Rule::constant_value => match inner.as_str() {
            "public_input_start" => Err(ParseError::SemanticError(
                "public_input_start cannot be used as match pattern".to_string(),
            )),
            text => {
                if let Some(value) = constants.get(text) {
                    Ok(*value)
                } else if let Ok(value) = text.parse::<usize>() {
                    Ok(value)
                } else {
                    Err(ParseError::SemanticError(format!(
                        "Invalid constant expression in match pattern: {text}"
                    )))
                }
            }
        },
        _ => Err(ParseError::SemanticError(format!(
            "Only constant values are allowed in match patterns: {}",
            inner.as_str()
        ))),
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
            Rule::statement => on_new_located_line(
                &mut then_branch,
                parse_statement(item, constants, trash_var_count)?,
            ),
            Rule::else_clause => {
                for else_item in item.into_inner() {
                    if else_item.as_rule() == Rule::statement {
                        on_new_located_line(
                            &mut else_branch,
                            parse_statement(else_item, constants, trash_var_count)?,
                        );
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
        array: array.into(),
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
    let next_peek = inner.peek().unwrap();
    let mut rev = false;
    if next_peek.as_rule() == Rule::rev_clause {
        rev = true;
        inner.next().unwrap(); // Consume the rev clause
    }
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
                on_new_located_line(
                    &mut body,
                    parse_statement(item, constants, trash_var_count)?,
                );
            }
            _ => {}
        }
    }

    Ok(Line::ForLoop {
        iterator,
        start,
        end,
        body,
        rev,
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
        Rule::mod_expr => parse_binary_expr(pair, constants, HighLevelOperation::Mod),
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
        array: array.into(),
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
        Rule::log2_ceil_expr => parse_log2_ceil(inner, constants),
        _ => Err(ParseError::SemanticError(
            "Invalid primary expression".to_string(),
        )),
    }
}

// Add this new function to handle log2_ceil parsing
fn parse_log2_ceil(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<Expression, ParseError> {
    let mut inner = pair.into_inner();
    let expr = parse_expression(inner.next().unwrap(), constants)?;
    Ok(Expression::Log2Ceil {
        value: Box::new(expr),
    })
}

fn parse_tuple_expression(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<Vec<Expression>, ParseError> {
    pair.into_inner()
        .map(|item| parse_expression(item, constants))
        .collect()
}

fn parse_function_call(
    pair: Pair<'_, Rule>,
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
                vectorized_len: Expression::zero(),
            })
        }
        "malloc_vec" => {
            let vectorized_len = if args.len() == 1 {
                Expression::scalar(LOG_VECTOR_LEN)
            } else {
                assert_eq!(args.len(), 2, "Invalid malloc_vec call");
                args[1].clone()
            };
            Ok(Line::MAlloc {
                var: return_data[0].clone(),
                size: args[0].clone(),
                vectorized: true,
                vectorized_len,
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
                !args.is_empty() && return_data.len() == 1,
                "Invalid decompose_bits call"
            );
            Ok(Line::DecomposeBits {
                var: return_data[0].clone(),
                to_decompose: args,
            })
        }
        "counter_hint" => {
            assert!(
                args.is_empty() && return_data.len() == 1,
                "Invalid counter_hint call"
            );
            Ok(Line::CounterHint {
                var: return_data[0].clone(),
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
                assert!(args.len() == precompile.n_inputs, "Invalid precompile call");
                Ok(Line::Precompile {
                    precompile: precompile.clone(),
                    args,
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
            "pointer_to_one_vector" => Ok(SimpleExpr::Constant(ConstExpression::Value(
                ConstantValue::PointerToOneVector,
            ))),
            _ => {
                if let Some(value) = constants.get(text) {
                    Ok(SimpleExpr::Constant(ConstExpression::Value(
                        ConstantValue::Scalar(*value),
                    )))
                } else if let Ok(value) = text.parse::<usize>() {
                    Ok(SimpleExpr::Constant(ConstExpression::Value(
                        ConstantValue::Scalar(value),
                    )))
                } else {
                    Ok(SimpleExpr::Var(text.to_string()))
                }
            }
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
