use super::expression::ExpressionParser;
use super::{ConstArrayValue, Parse, ParseContext, ParsedConstant, next_inner_pair};
use crate::a_simplify_lang::VarOrConstMallocAccess;
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
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<(String, ParsedConstant)> {
        let mut inner = pair.into_inner();
        let name = next_inner_pair(&mut inner, "constant name")?.as_str().to_string();
        let value_pair = next_inner_pair(&mut inner, "constant value")?;

        match value_pair.as_rule() {
            Rule::array_literal => {
                let value = parse_array_literal(value_pair, ctx, &name)?;
                Ok((name, ParsedConstant::Array(value)))
            }
            _ => {
                // Parse the expression and evaluate it
                let expr = ExpressionParser.parse(value_pair, ctx)?;

                let value = evaluate_const_expr(&expr, ctx).ok_or_else(|| {
                    SemanticError::with_context(format!("Failed to evaluate constant: {name}"), "constant declaration")
                })?;

                Ok((name, ParsedConstant::Scalar(value)))
            }
        }
    }
}

/// Recursively parse a (potentially nested) array literal into a ConstArrayValue.
fn parse_array_literal(pair: ParsePair<'_>, ctx: &mut ParseContext, const_name: &str) -> ParseResult<ConstArrayValue> {
    let elements: Vec<ConstArrayValue> = pair
        .into_inner()
        .map(|element_pair| {
            match element_pair.as_rule() {
                Rule::array_element => {
                    // array_element = { array_literal | expression }
                    let inner = element_pair.into_inner().next().unwrap();
                    match inner.as_rule() {
                        Rule::array_literal => parse_array_literal(inner, ctx, const_name),
                        _ => {
                            // It's an expression - evaluate to scalar
                            let expr = ExpressionParser.parse(inner, ctx)?;
                            let value = evaluate_const_expr(&expr, ctx).ok_or_else(|| {
                                SemanticError::with_context(
                                    format!("Failed to evaluate array element in constant: {const_name}"),
                                    "constant declaration",
                                )
                            })?;
                            Ok(ConstArrayValue::Scalar(value))
                        }
                    }
                }
                Rule::array_literal => {
                    // Direct nested array
                    parse_array_literal(element_pair, ctx, const_name)
                }
                _ => {
                    // Direct expression (fallback for old grammar)
                    let expr = ExpressionParser.parse(element_pair, ctx)?;
                    let value = evaluate_const_expr(&expr, ctx).ok_or_else(|| {
                        SemanticError::with_context(
                            format!("Failed to evaluate array element in constant: {const_name}"),
                            "constant declaration",
                        )
                    })?;
                    Ok(ConstArrayValue::Scalar(value))
                }
            }
        })
        .collect::<Result<Vec<_>, _>>()?;

    Ok(ConstArrayValue::Array(elements))
}

/// Evaluate a const expression to a usize value at parse time.
pub fn evaluate_const_expr(expr: &crate::lang::Expression, ctx: &ParseContext) -> Option<usize> {
    expr.eval_with(
        &|simple_expr| match simple_expr {
            SimpleExpr::Constant(cst) => cst.naive_eval(),
            SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) => ctx.get_constant(var).map(F::from_usize),
            SimpleExpr::Memory(VarOrConstMallocAccess::ConstMallocAccess { .. }) => None,
        },
        &|arr, index| {
            // Support const array access in expressions
            let idx = index.iter().map(|e| e.to_usize()).collect::<Vec<_>>();
            let array = ctx.get_const_array(arr)?;
            array.navigate(&idx)?.as_scalar().map(F::from_usize)
        },
    )
    .map(|f| f.to_usize())
}

/// Parser for variable or constant references.
pub struct VarOrConstantParser;

impl Parse<SimpleExpr> for VarOrConstantParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<SimpleExpr> {
        let text = pair.as_str();

        match pair.as_rule() {
            Rule::var_or_constant => {
                let inner = pair.into_inner().next().unwrap();
                Self.parse(inner, ctx)
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
            "pointer_to_univariate_selectors" => Ok(SimpleExpr::Constant(ConstExpression::Value(
                ConstantValue::PointerToUnivariateSelectors,
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
                    Ok(VarOrConstMallocAccess::Var(text.to_string()).into())
                }
            }
        }
    }
}

/// Parser for constant expressions used in match patterns.
pub struct ConstExprParser;

impl Parse<usize> for ConstExprParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<usize> {
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
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Vec<SimpleExpr>> {
        pair.into_inner()
            .map(|item| VarOrConstantParser.parse(item, ctx))
            .collect()
    }
}
