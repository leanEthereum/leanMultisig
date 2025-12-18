use super::expression::ExpressionParser;
use super::{Parse, ParseContext, ParsedConstant, next_inner_pair};
use crate::{
    F,
    lang::{ConstExpression, ConstantValue, SimpleExpr},
    parser::{
        error::{ParseResult, SemanticError},
        grammar::{ParsePair, Rule},
    },
};
use multilinear_toolkit::prelude::*;
use utils::ToUsize;

/// Parser for constant declarations.
pub struct ConstantDeclarationParser;

impl Parse<(String, ParsedConstant)> for ConstantDeclarationParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<(String, ParsedConstant)> {
        let mut inner = pair.into_inner();
        let name = next_inner_pair(&mut inner, "constant name")?.as_str().to_string();
        let value_pair = next_inner_pair(&mut inner, "constant value")?;

        match value_pair.as_rule() {
            Rule::array_literal => {
                let values: Vec<usize> = value_pair
                    .into_inner()
                    .map(|expr_pair| {
                        let expr = ExpressionParser::parse(expr_pair, ctx).unwrap();
                        expr.eval_with(
                            &|simple_expr| match simple_expr {
                                SimpleExpr::Constant(cst) => cst.naive_eval(),
                                SimpleExpr::Var(var) => ctx.get_constant(var).map(F::from_usize),
                                SimpleExpr::ConstMallocAccess { .. } => None,
                            },
                            &|_, _| None,
                        )
                        .ok_or_else(|| {
                            SemanticError::with_context(
                                format!("Failed to evaluate array element in constant: {name}"),
                                "constant declaration",
                            )
                        })
                        .map(|f| f.to_usize())
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok((name, ParsedConstant::Array(values)))
            }
            _ => {
                // Parse the expression and evaluate it
                let expr = ExpressionParser::parse(value_pair, ctx)?;

                let value = expr
                    .eval_with(
                        &|simple_expr| match simple_expr {
                            SimpleExpr::Constant(cst) => cst.naive_eval(),
                            SimpleExpr::Var(var) => ctx.get_constant(var).map(F::from_usize),
                            SimpleExpr::ConstMallocAccess { .. } => None,
                        },
                        &|_, _| None,
                    )
                    .ok_or_else(|| {
                        SemanticError::with_context(
                            format!("Failed to evaluate constant: {name}"),
                            "constant declaration",
                        )
                    })?
                    .to_usize();

                Ok((name, ParsedConstant::Scalar(value)))
            }
        }
    }
}

/// Parser for variable or constant references.
pub struct VarOrConstantParser;

impl Parse<SimpleExpr> for VarOrConstantParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<SimpleExpr> {
        let text = pair.as_str();

        match pair.as_rule() {
            Rule::var_or_constant => {
                let inner = pair.into_inner().next().unwrap();
                Self::parse(inner, ctx)
            }
            Rule::identifier | Rule::constant_value => Self::parse_identifier_or_constant(text, ctx),
            _ => Err(SemanticError::new("Expected identifier or constant").into()),
        }
    }
}

impl VarOrConstantParser {
    fn parse_identifier_or_constant(text: &str, ctx: &ParseContext) -> ParseResult<SimpleExpr> {
        match text {
            // Special built-in constants
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
                // Check if it's a const array (error case - can't use array as value)
                if ctx.get_const_array(text).is_some() {
                    return Err(SemanticError::with_context(
                        format!("Cannot use const array '{text}' as a value directly (use indexing or len())"),
                        "variable reference",
                    )
                    .into());
                }

                // Try to resolve as defined constant
                if let Some(value) = ctx.get_constant(text) {
                    Ok(SimpleExpr::Constant(ConstExpression::Value(ConstantValue::Scalar(
                        value,
                    ))))
                }
                // Try to parse as numeric literal
                else if let Ok(value) = text.parse::<usize>() {
                    Ok(SimpleExpr::Constant(ConstExpression::Value(ConstantValue::Scalar(
                        value,
                    ))))
                }
                // Otherwise treat as variable reference
                else {
                    Ok(SimpleExpr::Var(text.to_string()))
                }
            }
        }
    }
}

/// Parser for constant expressions used in match patterns.
pub struct ConstExprParser;

impl Parse<usize> for ConstExprParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<usize> {
        let inner = pair.into_inner().next().unwrap();

        match inner.as_rule() {
            Rule::constant_value => {
                let text = inner.as_str();
                match text {
                    "public_input_start" => {
                        Err(SemanticError::new("public_input_start cannot be used as match pattern").into())
                    }
                    _ => {
                        if let Some(value) = ctx.get_constant(text) {
                            Ok(value)
                        } else if let Ok(value) = text.parse::<usize>() {
                            Ok(value)
                        } else {
                            Err(SemanticError::with_context(
                                format!("Invalid constant expression in match pattern: {text}"),
                                "match pattern",
                            )
                            .into())
                        }
                    }
                }
            }
            _ => Err(SemanticError::with_context(
                format!("Only constant values are allowed in match patterns: {}", inner.as_str()),
                "match pattern",
            )
            .into()),
        }
    }
}

/// Parser for variable lists (used in function calls).
pub struct VarListParser;

impl Parse<Vec<SimpleExpr>> for VarListParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Vec<SimpleExpr>> {
        pair.into_inner()
            .map(|item| VarOrConstantParser::parse(item, ctx))
            .collect()
    }
}
