use std::collections::BTreeMap;

use pest::iterators::Pair;

use super::{ParseError, Rule, parse_parameter, parse_statement};
use crate::lang::Function;

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
