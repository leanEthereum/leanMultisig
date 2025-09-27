use super::expression::ExpressionParser;
use super::literal::VarListParser;
use super::statement::StatementParser;
use super::{Parse, ParseContext, next_inner_pair};
use crate::lang::{
    CounterHint, DecomposeBits, FunctionCall, LocationReport, MAlloc, Panic, PrecompileStmt, Print,
};
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

        lines.push(Line::LocationReport(LocationReport { location }));
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
                Ok(Line::MAlloc(MAlloc {
                    var: return_data[0].clone(),
                    size: args[0].clone(),
                    vectorized: false,
                    vectorized_len: Expression::zero(),
                }))
            }
            "malloc_vec" => {
                if return_data.len() != 1 {
                    return Err(
                        SemanticError::new("malloc_vec must return exactly one value").into(),
                    );
                }

                let vectorized_len = if args.len() == 1 {
                    Expression::scalar(LOG_VECTOR_LEN)
                } else if args.len() == 2 {
                    args[1].clone()
                } else {
                    return Err(SemanticError::new("malloc_vec takes 1 or 2 arguments").into());
                };

                Ok(Line::MAlloc(MAlloc {
                    var: return_data[0].clone(),
                    size: args[0].clone(),
                    vectorized: true,
                    vectorized_len,
                }))
            }
            "print" => {
                if !return_data.is_empty() {
                    return Err(
                        SemanticError::new("Print function should not return values").into(),
                    );
                }
                Ok(Line::Print(Print {
                    line_info: function_name.clone(),
                    content: args,
                }))
            }
            "decompose_bits" => {
                if args.is_empty() || return_data.len() != 1 {
                    return Err(SemanticError::new("Invalid decompose_bits call").into());
                }
                Ok(Line::DecomposeBits(DecomposeBits {
                    var: return_data[0].clone(),
                    to_decompose: args,
                }))
            }
            "counter_hint" => {
                if !args.is_empty() || return_data.len() != 1 {
                    return Err(SemanticError::new("Invalid counter_hint call").into());
                }
                Ok(Line::CounterHint(CounterHint {
                    var: return_data[0].clone(),
                }))
            }
            "panic" => {
                if !return_data.is_empty() || !args.is_empty() {
                    return Err(
                        SemanticError::new("Panic has no args and returns no values").into(),
                    );
                }
                Ok(Line::Panic(Panic))
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
                    Ok(Line::Precompile(PrecompileStmt {
                        precompile: precompile.clone(),
                        args,
                    }))
                } else {
                    Ok(Line::FunctionCall(FunctionCall {
                        function_name,
                        args,
                        return_data,
                    }))
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::{Expression, Line};
    use crate::parser::grammar::{LangParser, Rule};
    use pest::Parser;

    #[test]
    fn test_malloc_vec_no_return_data() {
        let args = vec![Expression::scalar(100)];
        let return_data = vec![];

        let result = FunctionCallParser::handle_builtin_function(
            "malloc_vec".to_string(),
            args,
            return_data,
        );

        assert!(result.is_err());
        if let Err(crate::parser::error::ParseError::SemanticError(error)) = result {
            assert!(
                error
                    .message
                    .contains("malloc_vec must return exactly one value")
            );
        } else {
            panic!("Expected SemanticError");
        }
    }

    #[test]
    fn test_malloc_vec_too_many_return_values() {
        let args = vec![Expression::scalar(100)];
        let return_data = vec!["ptr1".to_string(), "ptr2".to_string()];

        let result = FunctionCallParser::handle_builtin_function(
            "malloc_vec".to_string(),
            args,
            return_data,
        );

        assert!(result.is_err());
        if let Err(crate::parser::error::ParseError::SemanticError(error)) = result {
            assert!(
                error
                    .message
                    .contains("malloc_vec must return exactly one value")
            );
        } else {
            panic!("Expected SemanticError");
        }
    }

    #[test]
    fn test_malloc_vec_valid_one_arg() {
        let args = vec![Expression::scalar(100)];
        let return_data = vec!["ptr".to_string()];

        let result = FunctionCallParser::handle_builtin_function(
            "malloc_vec".to_string(),
            args,
            return_data,
        )
        .unwrap();

        if let Line::MAlloc(MAlloc {
            var,
            size: _,
            vectorized,
            vectorized_len: _,
        }) = result
        {
            assert_eq!(var, "ptr");
            assert!(vectorized);
        } else {
            panic!("Expected MAlloc line");
        }
    }

    #[test]
    fn test_malloc_vec_valid_two_args() {
        let args = vec![Expression::scalar(100), Expression::scalar(8)];
        let return_data = vec!["ptr".to_string()];

        let result = FunctionCallParser::handle_builtin_function(
            "malloc_vec".to_string(),
            args,
            return_data,
        )
        .unwrap();

        if let Line::MAlloc(MAlloc {
            var,
            size: _,
            vectorized,
            vectorized_len: _,
        }) = result
        {
            assert_eq!(var, "ptr");
            assert!(vectorized);
        } else {
            panic!("Expected MAlloc line");
        }
    }

    #[test]
    fn test_malloc_vec_too_many_args() {
        let args = vec![
            Expression::scalar(100),
            Expression::scalar(8),
            Expression::scalar(16),
        ];
        let return_data = vec!["ptr".to_string()];

        let result = FunctionCallParser::handle_builtin_function(
            "malloc_vec".to_string(),
            args,
            return_data,
        );

        assert!(result.is_err());
        if let Err(crate::parser::error::ParseError::SemanticError(error)) = result {
            assert!(error.message.contains("malloc_vec takes 1 or 2 arguments"));
        } else {
            panic!("Expected SemanticError");
        }
    }

    #[test]
    fn test_malloc_builtin() {
        let args = vec![Expression::scalar(200)];
        let return_data = vec!["mem".to_string()];

        let result =
            FunctionCallParser::handle_builtin_function("malloc".to_string(), args, return_data)
                .unwrap();

        if let Line::MAlloc(MAlloc {
            var,
            size,
            vectorized,
            vectorized_len,
        }) = result
        {
            assert_eq!(var, "mem");
            assert_eq!(size, Expression::scalar(200));
            assert!(!vectorized);
            assert_eq!(vectorized_len, Expression::zero());
        } else {
            panic!("Expected MAlloc");
        }
    }

    #[test]
    fn test_print_builtin() {
        let args = vec![
            Expression::scalar(42),
            Expression::Value(crate::lang::SimpleExpr::Var("x".to_string())),
        ];
        let return_data = vec![];

        let result = FunctionCallParser::handle_builtin_function(
            "print".to_string(),
            args.clone(),
            return_data,
        )
        .unwrap();

        if let Line::Print(Print { line_info, content }) = result {
            assert_eq!(line_info, "print");
            assert_eq!(content, args);
        } else {
            panic!("Expected Print");
        }
    }

    #[test]
    fn test_decompose_bits_builtin() {
        let args = vec![Expression::scalar(255)];
        let return_data = vec!["bits".to_string()];

        let result = FunctionCallParser::handle_builtin_function(
            "decompose_bits".to_string(),
            args.clone(),
            return_data,
        )
        .unwrap();

        if let Line::DecomposeBits(DecomposeBits { var, to_decompose }) = result {
            assert_eq!(var, "bits");
            assert_eq!(to_decompose, args);
        } else {
            panic!("Expected DecomposeBits");
        }
    }

    #[test]
    fn test_counter_hint_builtin() {
        let args = vec![];
        let return_data = vec!["counter".to_string()];

        let result = FunctionCallParser::handle_builtin_function(
            "counter_hint".to_string(),
            args,
            return_data,
        )
        .unwrap();

        if let Line::CounterHint(CounterHint { var }) = result {
            assert_eq!(var, "counter");
        } else {
            panic!("Expected CounterHint");
        }
    }

    #[test]
    fn test_panic_builtin() {
        let args = vec![];
        let return_data = vec![];

        let result =
            FunctionCallParser::handle_builtin_function("panic".to_string(), args, return_data)
                .unwrap();

        assert_eq!(result, Line::Panic(Panic));
    }

    #[test]
    fn test_regular_function_call() {
        let args = vec![Expression::scalar(1), Expression::scalar(2)];
        let return_data = vec!["result".to_string()];

        let result = FunctionCallParser::handle_builtin_function(
            "my_function".to_string(),
            args.clone(),
            return_data.clone(),
        )
        .unwrap();

        if let Line::FunctionCall(FunctionCall {
            function_name,
            args: call_args,
            return_data: call_return,
        }) = result
        {
            assert_eq!(function_name, "my_function");
            assert_eq!(call_args, args);
            assert_eq!(call_return, return_data);
        } else {
            panic!("Expected FunctionCall");
        }
    }

    #[test]
    fn test_tuple_expression_parser() {
        let mut ctx = ParseContext::new();
        let input = "42, x, 100";
        let mut pairs = LangParser::parse(Rule::tuple_expression, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = TupleExpressionParser::parse(pair, &mut ctx).unwrap();
        assert_eq!(result.len(), 3);
        assert_eq!(result[0], Expression::scalar(42));
        assert_eq!(
            result[1],
            Expression::Value(crate::lang::SimpleExpr::Var("x".to_string()))
        );
        assert_eq!(result[2], Expression::scalar(100));
    }

    #[test]
    fn test_parameter_parser_regular() {
        let mut ctx = ParseContext::new();
        let input = "param1";
        let mut pairs = LangParser::parse(Rule::parameter, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ParameterParser::parse(pair, &mut ctx).unwrap();
        assert_eq!(result, ("param1".to_string(), false));
    }

    #[test]
    fn test_parameter_parser_const() {
        let mut ctx = ParseContext::new();
        let input = "const param2";
        let mut pairs = LangParser::parse(Rule::parameter, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ParameterParser::parse(pair, &mut ctx).unwrap();
        assert_eq!(result, ("param2".to_string(), true));
    }

    #[test]
    fn test_return_count_parser() {
        let mut ctx = ParseContext::new();
        ctx.add_constant("RETURN_COUNT".to_string(), 3).unwrap();

        let input = "-> 3";
        let mut pairs = LangParser::parse(Rule::return_count, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ReturnCountParser::parse(pair, &mut ctx).unwrap();
        assert_eq!(result, 3);
    }
}
