use super::expression::ExpressionParser;
use super::statement::StatementParser;
use super::{Parse, ParseContext, next_inner_pair};
use crate::{
    SourceLineNumber,
    lang::{AssignmentTarget, Expression, Function, FunctionArg, Line, SourceLocation},
    parser::{
        error::{ParseResult, SemanticError},
        grammar::{ParsePair, Rule},
    },
};
use lean_vm::{ALL_TABLES, CustomHint, Table, TableT};

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
        let line_number = pair.line_col().0;
        let line = StatementParser.parse(pair, ctx)?;

        lines.push(Line::LocationReport {
            location: SourceLocation {
                file_id: ctx.current_file_id,
                line_number,
            },
        });
        lines.push(line);

        Ok(())
    }
}

/// Parser for function parameters.
pub struct ParameterParser;

impl Parse<FunctionArg> for ParameterParser {
    fn parse(&self, pair: ParsePair<'_>, _ctx: &mut ParseContext) -> ParseResult<FunctionArg> {
        let mut inner = pair.into_inner().peekable();
        let mut is_const = false;
        let mut is_mutable = false;

        // Check for const keyword
        if inner
            .peek()
            .map(|p| p.as_rule() == Rule::const_keyword)
            .unwrap_or(false)
        {
            is_const = true;
            inner.next();
        }

        // Check for mut keyword
        if inner.peek().map(|p| p.as_rule() == Rule::mut_keyword).unwrap_or(false) {
            is_mutable = true;
            inner.next();
        }

        // const and mut are mutually exclusive
        if is_const && is_mutable {
            return Err(SemanticError::new("Parameter cannot be both 'const' and 'mut'").into());
        }

        let name = next_inner_pair(&mut inner, "parameter name")?.as_str().to_string();
        Ok(FunctionArg {
            name,
            is_const,
            is_mutable,
        })
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

/// Parser for individual assignment targets (variable or array access).
pub struct AssignmentTargetParser;

impl Parse<AssignmentTarget> for AssignmentTargetParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<AssignmentTarget> {
        let mut inner = pair.into_inner().peekable();

        // Check for mut keyword
        let is_mutable = inner.peek().map(|p| p.as_rule() == Rule::mut_keyword).unwrap_or(false);
        if is_mutable {
            inner.next();
        }

        let target_pair = next_inner_pair(&mut inner, "assignment target")?;

        match target_pair.as_rule() {
            Rule::array_access_expr => {
                if is_mutable {
                    return Err(SemanticError::new("Cannot use 'mut' on array access targets").into());
                }
                let mut inner_pairs = target_pair.into_inner();
                let array = next_inner_pair(&mut inner_pairs, "array name")?.as_str().to_string();
                let index = ExpressionParser.parse(next_inner_pair(&mut inner_pairs, "array index")?, ctx)?;
                Ok(AssignmentTarget::ArrayAccess {
                    array,
                    index: Box::new(index),
                })
            }
            Rule::identifier => Ok(AssignmentTarget::Var {
                var: target_pair.as_str().to_string(),
                is_mutable,
            }),
            _ => Err(SemanticError::new("Expected identifier or array access").into()),
        }
    }
}

pub struct AssignmentParser;

impl Parse<Line> for AssignmentParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let line_number = pair.line_col().0;
        let mut inner = pair.into_inner().peekable();

        // Check if there's an assignment_target_list (LHS)
        let mut targets: Vec<AssignmentTarget> = Vec::new();
        if let Some(first) = inner.peek()
            && first.as_rule() == Rule::assignment_target_list
        {
            targets = inner
                .next()
                .unwrap()
                .into_inner()
                .map(|item| AssignmentTargetParser.parse(item, ctx))
                .collect::<ParseResult<Vec<AssignmentTarget>>>()?;
        }

        // Parse the expression (RHS)
        let expr_pair = next_inner_pair(&mut inner, "expression")?;
        let expr = ExpressionParser.parse(expr_pair, ctx)?;

        for target in &mut targets {
            if let AssignmentTarget::Var { var, .. } = target
                && var == "_"
            {
                *var = ctx.next_trash_var();
            }
        }

        match &expr {
            Expression::FunctionCall { function_name, args } => {
                Self::handle_function_call(line_number, function_name.clone(), args.clone(), targets)
            }
            _ => {
                // Non-function-call expression - must have exactly one target
                if targets.is_empty() {
                    return Err(SemanticError::new("Expression statement has no effect").into());
                }
                if targets.len() > 1 {
                    return Err(SemanticError::new(
                        "Multiple assignment targets require a function call on the right side",
                    )
                    .into());
                }

                Ok(Line::Statement {
                    targets,
                    value: expr,
                    line_number,
                })
            }
        }
    }
}

impl AssignmentParser {
    fn handle_function_call(
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
                AssignmentTarget::Var { var, .. } => Ok(var.clone()),
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
                if return_data.len() != 1 {
                    return Err(SemanticError::new("Invalid malloc call: expected 1 return value").into());
                }
                let (var, is_mutable) = match &return_data[0] {
                    AssignmentTarget::Var { var, is_mutable } => (var.clone(), *is_mutable),
                    AssignmentTarget::ArrayAccess { .. } => {
                        return Err(SemanticError::new("malloc does not support array access as return target").into())
                    }
                };
                Ok(Line::MAlloc {
                    var,
                    size: args[0].clone(),
                    is_mutable,
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
                            "Custom hint: \"{function_name}\" should not return values",
                        ))
                        .into());
                    }
                    if !hint.n_args_range().contains(&args.len()) {
                        return Err(SemanticError::new(format!(
                            "Custom hint: \"{function_name}\" : invalid number of arguments",
                        ))
                        .into());
                    }
                    return Ok(Line::CustomHint(hint, args));
                }
                // Regular function call - allow array access targets
                Ok(Line::Statement {
                    targets: return_data,
                    value: Expression::FunctionCall { function_name, args },
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
