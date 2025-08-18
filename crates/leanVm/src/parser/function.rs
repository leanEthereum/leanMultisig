use std::collections::BTreeMap;

use pest::iterators::Pair;

use super::{ParseError, Rule, parse_parameter, parse_statement, parse_var_list};
use crate::{
    lang::{Function, Line, SimpleExpr},
    parser::{PRECOMPILES, parse_tuple_expression},
};

pub(crate) fn parse_function(
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

#[allow(clippy::too_many_lines)]
pub(crate) fn parse_function_call(
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
