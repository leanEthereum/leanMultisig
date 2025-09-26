use super::expression::ExpressionParser;
use super::literal::VarListParser;
use super::statement::StatementParser;
use super::{Parse, ParseContext, next_inner_pair};
use crate::{
    lang::{Expression, Function, Line, SimpleExpr},
    parser::{
        error::{ParseResult, SemanticError},
        grammar::{ParsePair, Rule},
    },
    precompiles::PRECOMPILES,
};
use lean_vm::LOG_VECTOR_LEN;

/// Parser for complete function definitions.
pub struct FunctionParser;

impl Parse<Function> for FunctionParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Function> {
        let mut inner = pair.into_inner();
        let name = next_inner_pair(&mut inner, "function name")?
            .as_str()
            .to_string();

        let mut arguments = Vec::new();
        let mut n_returned_vars = 0;
        let mut inlined = false;
        let mut body = Vec::new();

        for pair in inner {
            match pair.as_rule() {
                Rule::parameter_list => {
                    for param in pair.into_inner() {
                        if param.as_rule() == Rule::parameter {
                            arguments.push(ParameterParser::parse(param, ctx)?);
                        }
                    }
                }
                Rule::inlined_statement => {
                    inlined = true;
                }
                Rule::return_count => {
                    n_returned_vars = ReturnCountParser::parse(pair, ctx)?;
                }
                Rule::statement => {
                    Self::add_statement_with_location(&mut body, pair, ctx)?;
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
}

impl FunctionParser {
    fn add_statement_with_location(
        lines: &mut Vec<Line>,
        pair: ParsePair<'_>,
        ctx: &mut ParseContext,
    ) -> ParseResult<()> {
        let location = pair.line_col().0;
        let line = StatementParser::parse(pair, ctx)?;

        lines.push(Line::LocationReport { location });
        lines.push(line);

        Ok(())
    }
}

/// Parser for function parameters.
pub struct ParameterParser;

impl Parse<(String, bool)> for ParameterParser {
    fn parse(pair: ParsePair<'_>, _ctx: &mut ParseContext) -> ParseResult<(String, bool)> {
        let mut inner = pair.into_inner();
        let first = next_inner_pair(&mut inner, "parameter")?;

        if first.as_rule() == Rule::const_keyword {
            let identifier = next_inner_pair(&mut inner, "identifier after 'const'")?;
            Ok((identifier.as_str().to_string(), true))
        } else {
            Ok((first.as_str().to_string(), false))
        }
    }
}

/// Parser for function return count declarations.
pub struct ReturnCountParser;

impl Parse<usize> for ReturnCountParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<usize> {
        let count_str = next_inner_pair(&mut pair.into_inner(), "return count")?.as_str();

        ctx.get_constant(count_str)
            .or_else(|| count_str.parse().ok())
            .ok_or_else(|| SemanticError::new("Invalid return count").into())
    }
}

/// Parser for function calls with special handling for built-in functions.
pub struct FunctionCallParser;

impl Parse<Line> for FunctionCallParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let mut return_data = Vec::new();
        let mut function_name = String::new();
        let mut args = Vec::new();

        for item in pair.into_inner() {
            match item.as_rule() {
                Rule::function_res => {
                    for res_item in item.into_inner() {
                        if res_item.as_rule() == Rule::var_list {
                            return_data = VarListParser::parse(res_item, ctx)?
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
                Rule::tuple_expression => {
                    args = TupleExpressionParser::parse(item, ctx)?;
                }
                _ => {}
            }
        }

        // Replace trash variables with unique names
        for var in &mut return_data {
            if var == "_" {
                *var = ctx.next_trash_var();
            }
        }

        // Handle built-in functions
        Self::handle_builtin_function(function_name, args, return_data)
    }
}

impl FunctionCallParser {
    fn handle_builtin_function(
        function_name: String,
        args: Vec<Expression>,
        return_data: Vec<String>,
    ) -> ParseResult<Line> {
        match function_name.as_str() {
            "malloc" => {
                if args.len() != 1 || return_data.len() != 1 {
                    return Err(SemanticError::new("Invalid malloc call").into());
                }
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
                } else if args.len() == 2 {
                    args[1].clone()
                } else {
                    return Err(SemanticError::new("Invalid malloc_vec call").into());
                };

                Ok(Line::MAlloc {
                    var: return_data[0].clone(),
                    size: args[0].clone(),
                    vectorized: true,
                    vectorized_len,
                })
            }
            "print" => {
                if !return_data.is_empty() {
                    return Err(
                        SemanticError::new("Print function should not return values").into(),
                    );
                }
                Ok(Line::Print {
                    line_info: function_name.clone(),
                    content: args,
                })
            }
            "decompose_bits" => {
                if args.is_empty() || return_data.len() != 1 {
                    return Err(SemanticError::new("Invalid decompose_bits call").into());
                }
                Ok(Line::DecomposeBits {
                    var: return_data[0].clone(),
                    to_decompose: args,
                })
            }
            "counter_hint" => {
                if !args.is_empty() || return_data.len() != 1 {
                    return Err(SemanticError::new("Invalid counter_hint call").into());
                }
                Ok(Line::CounterHint {
                    var: return_data[0].clone(),
                })
            }
            "panic" => {
                if !return_data.is_empty() || !args.is_empty() {
                    return Err(
                        SemanticError::new("Panic has no args and returns no values").into(),
                    );
                }
                Ok(Line::Panic)
            }
            _ => {
                // Check for precompile functions
                if let Some(precompile) = PRECOMPILES
                    .iter()
                    .find(|p| p.name.to_string() == function_name)
                {
                    if args.len() != precompile.n_inputs {
                        return Err(SemanticError::new("Invalid precompile call").into());
                    }
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
}

/// Parser for tuple expressions used in function calls.
pub struct TupleExpressionParser;

impl Parse<Vec<Expression>> for TupleExpressionParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Vec<Expression>> {
        pair.into_inner()
            .map(|item| ExpressionParser::parse(item, ctx))
            .collect()
    }
}
