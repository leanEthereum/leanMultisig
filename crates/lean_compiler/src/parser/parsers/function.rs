use super::expression::ExpressionParser;
use super::statement::StatementParser;
use super::{Parse, ParseContext, next_inner_pair};
use crate::{
    SourceLineNumber,
    lang::{AssignmentTarget, Expression, Function, Line, SimpleExpr},
    parser::{
        error::{ParseResult, SemanticError},
        grammar::{ParsePair, Rule},
    },
};
use lean_vm::{ALL_TABLES, CustomHint, LOG_VECTOR_LEN, Table, TableT};

/// Parser for complete function definitions.
pub struct FunctionParser;

impl Parse<Function> for FunctionParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Function> {
        let mut inner = pair.into_inner().peekable();
        let assume_always_returns = match inner.peek().map(|x| x.as_rule()) {
            Some(Rule::pragma) => {
                inner.next();
                true
            }
            _ => false,
        };
        let name = next_inner_pair(&mut inner, "function name")?.as_str().to_string();

        let mut arguments = Vec::new();
        let mut n_returned_vars = 0;
        let mut inlined = false;
        let mut body = Vec::new();

        for pair in inner {
            match pair.as_rule() {
                Rule::parameter_list => {
                    for param in pair.into_inner() {
                        if param.as_rule() == Rule::parameter {
                            arguments.push(ParameterParser.parse(param, ctx)?);
                        }
                    }
                }
                Rule::inlined_statement => {
                    inlined = true;
                }
                Rule::return_count => {
                    n_returned_vars = ReturnCountParser.parse(pair, ctx)?;
                }
                Rule::statement => {
                    Self::add_statement_with_location(&mut body, pair, ctx)?;
                }
                _ => {}
            }
        }

        Ok(Function {
            name,
            file_id: ctx.current_file_id,
            arguments,
            inlined,
            n_returned_vars,
            body,
            assume_always_returns,
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
        let line = StatementParser.parse(pair, ctx)?;

        lines.push(Line::LocationReport { location });
        lines.push(line);

        Ok(())
    }
}

/// Parser for function parameters.
pub struct ParameterParser;

impl Parse<(String, bool)> for ParameterParser {
    fn parse(&self, pair: ParsePair<'_>, _ctx: &mut ParseContext) -> ParseResult<(String, bool)> {
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
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<usize> {
        let count_str = next_inner_pair(&mut pair.into_inner(), "return count")?.as_str();

        ctx.get_constant(count_str)
            .or_else(|| count_str.parse().ok())
            .ok_or_else(|| SemanticError::new("Invalid return count").into())
    }
}

/// Parser for return target lists (used in function calls).
pub struct ReturnTargetListParser;

impl Parse<Vec<AssignmentTarget>> for ReturnTargetListParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Vec<AssignmentTarget>> {
        pair.into_inner()
            .map(|item| ReturnTargetParser.parse(item, ctx))
            .collect()
    }
}

/// Parser for individual return targets (variable or array access).
pub struct ReturnTargetParser;

impl Parse<AssignmentTarget> for ReturnTargetParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<AssignmentTarget> {
        let inner = next_inner_pair(&mut pair.into_inner(), "return target")?;

        match inner.as_rule() {
            Rule::array_access_expr => {
                let mut inner_pairs = inner.into_inner();
                let array = next_inner_pair(&mut inner_pairs, "array name")?.as_str().to_string();
                let index = ExpressionParser.parse(next_inner_pair(&mut inner_pairs, "array index")?, ctx)?;
                Ok(AssignmentTarget::ArrayAccess {
                    array: SimpleExpr::Var(array),
                    index: Box::new(index),
                })
            }
            Rule::identifier => Ok(AssignmentTarget::Var(inner.as_str().to_string())),
            _ => Err(SemanticError::new("Expected identifier or array access").into()),
        }
    }
}

/// Parser for function calls with special handling for built-in functions.
pub struct FunctionCallParser;

impl Parse<Line> for FunctionCallParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let mut return_data: Vec<AssignmentTarget> = Vec::new();
        let mut function_name = String::new();
        let mut args = Vec::new();
        let line_number = pair.line_col().0;

        for item in pair.into_inner() {
            match item.as_rule() {
                Rule::function_res => {
                    for res_item in item.into_inner() {
                        if res_item.as_rule() == Rule::return_target_list {
                            return_data = ReturnTargetListParser.parse(res_item, ctx)?;
                        }
                    }
                }
                Rule::identifier => function_name = item.as_str().to_string(),
                Rule::tuple_expression => {
                    args = TupleExpressionParser.parse(item, ctx)?;
                }
                _ => {}
            }
        }

        // Replace trash variables with unique names
        for target in &mut return_data {
            if let AssignmentTarget::Var(var) = target
                && var == "_"
            {
                *var = ctx.next_trash_var();
            }
        }

        // Handle built-in functions
        Self::handle_builtin_function(line_number, function_name, args, return_data)
    }
}

impl FunctionCallParser {
    fn handle_builtin_function(
        line_number: SourceLineNumber,
        function_name: String,
        args: Vec<Expression>,
        return_data: Vec<AssignmentTarget>,
    ) -> ParseResult<Line> {
        // Helper to extract a single variable from return_data for builtins
        let require_single_var = |return_data: &[AssignmentTarget], builtin_name: &str| -> ParseResult<String> {
            if return_data.len() != 1 {
                return Err(SemanticError::new(format!("Invalid {builtin_name} call: expected 1 return value")).into());
            }
            match &return_data[0] {
                AssignmentTarget::Var(v) => Ok(v.clone()),
                AssignmentTarget::ArrayAccess { .. } => Err(SemanticError::new(format!(
                    "{builtin_name} does not support array access as return target"
                ))
                .into()),
            }
        };

        match function_name.as_str() {
            "malloc" => {
                if args.len() != 1 {
                    return Err(SemanticError::new("Invalid malloc call").into());
                }
                let var = require_single_var(&return_data, "malloc")?;
                Ok(Line::MAlloc {
                    var,
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
                let var = require_single_var(&return_data, "malloc")?;
                Ok(Line::MAlloc {
                    var,
                    size: args[0].clone(),
                    vectorized: true,
                    vectorized_len,
                })
            }
            "print" => {
                if !return_data.is_empty() {
                    return Err(SemanticError::new("Print function should not return values").into());
                }
                Ok(Line::Print {
                    line_info: function_name.clone(),
                    content: args,
                })
            }
            "private_input_start" => {
                if !args.is_empty() {
                    return Err(SemanticError::new("Invalid private_input_start call").into());
                }
                let result = require_single_var(&return_data, "private_input_start")?;
                Ok(Line::PrivateInputStart { result })
            }
            "panic" => {
                if !return_data.is_empty() || !args.is_empty() {
                    return Err(SemanticError::new("Panic has no args and returns no values").into());
                }
                Ok(Line::Panic)
            }
            _ => {
                // Check for special precompile functions
                if let Some(table) = ALL_TABLES.into_iter().find(|p| p.name() == function_name)
                    && table != Table::execution()
                {
                    return Ok(Line::Precompile { table, args });
                }

                // Check for custom hint
                if let Some(hint) = CustomHint::find_by_name(&function_name) {
                    if !return_data.is_empty() {
                        return Err(SemanticError::new(format!(
                            "Custom hint: \"{}\" should not return values",
                            function_name
                        ))
                        .into());
                    }
                    if !hint.n_args_range().contains(&args.len()) {
                        return Err(SemanticError::new(format!(
                            "Custom hint: \"{}\" : invalid number of arguments",
                            function_name
                        ))
                        .into());
                    }
                    return Ok(Line::CustomHint(hint, args));
                }
                // Regular function call - allow array access targets
                Ok(Line::FunctionCall {
                    function_name,
                    args,
                    return_data,
                    line_number,
                })
            }
        }
    }
}

/// Parser for tuple expressions used in function calls.
pub struct TupleExpressionParser;

impl Parse<Vec<Expression>> for TupleExpressionParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Vec<Expression>> {
        pair.into_inner()
            .map(|item| ExpressionParser.parse(item, ctx))
            .collect()
    }
}
