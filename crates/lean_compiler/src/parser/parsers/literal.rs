use super::expression::ExpressionParser;
use super::{Parse, ParseContext, next_inner_pair};
use crate::{
    F,
    lang::{ConstExpression, ConstantValue, SimpleExpr},
    parser::{
        error::{ParseResult, SemanticError},
        grammar::{ParsePair, Rule},
    },
};
use p3_field::PrimeCharacteristicRing;
use utils::ToUsize;

/// Parser for constant declarations.
pub struct ConstantDeclarationParser;

impl Parse<(String, usize)> for ConstantDeclarationParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<(String, usize)> {
        let mut inner = pair.into_inner();
        let name = next_inner_pair(&mut inner, "constant name")?
            .as_str()
            .to_string();
        let value_pair = next_inner_pair(&mut inner, "constant value")?;

        // Parse the expression and evaluate it
        let expr = ExpressionParser::parse(value_pair, ctx)?;

        let value = expr
            .eval_with(
                &|simple_expr| match simple_expr {
                    SimpleExpr::Constant(cst) => cst.naive_eval(),
                    SimpleExpr::Var(var) => ctx.get_constant(var).map(F::from_usize),
                    SimpleExpr::ConstMallocAccess { .. } => None, // Not allowed in constants
                },
                &|_, _| None,
            )
            .ok_or_else(|| {
                SemanticError::with_context(
                    format!("Failed to evaluate constant: {}", name),
                    "constant declaration",
                )
            })?
            .to_usize();

        Ok((name, value))
    }
}

/// Parser for variable or constant references.
pub struct VarOrConstantParser;

impl Parse<SimpleExpr> for VarOrConstantParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<SimpleExpr> {
        let text = pair.as_str();

        match pair.as_rule() {
            Rule::var_or_constant => {
                let inner = pair.into_inner().next().ok_or_else(|| {
                    SemanticError::with_context(
                        "Expected var_or_constant inner content",
                        "variable or constant parsing",
                    )
                })?;
                Self::parse(inner, ctx)
            }
            Rule::identifier | Rule::constant_value => {
                Self::parse_identifier_or_constant(text, ctx)
            }
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
                // Try to resolve as defined constant
                if let Some(value) = ctx.get_constant(text) {
                    Ok(SimpleExpr::Constant(ConstExpression::Value(
                        ConstantValue::Scalar(value),
                    )))
                }
                // Try to parse as numeric literal
                else if let Ok(value) = text.parse::<usize>() {
                    Ok(SimpleExpr::Constant(ConstExpression::Value(
                        ConstantValue::Scalar(value),
                    )))
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
        let inner = pair.into_inner().next().ok_or_else(|| {
            SemanticError::with_context(
                "Expected const_expr inner content",
                "constant expression parsing",
            )
        })?;

        match inner.as_rule() {
            Rule::constant_value => {
                let text = inner.as_str();
                match text {
                    "public_input_start" => Err(SemanticError::new(
                        "public_input_start cannot be used as match pattern",
                    )
                    .into()),
                    _ => {
                        if let Some(value) = ctx.get_constant(text) {
                            Ok(value)
                        } else if let Ok(value) = text.parse::<usize>() {
                            Ok(value)
                        } else {
                            Err(SemanticError::with_context(
                                format!("Invalid constant expression in match pattern: {}", text),
                                "match pattern",
                            )
                            .into())
                        }
                    }
                }
            }
            _ => Err(SemanticError::with_context(
                format!(
                    "Only constant values are allowed in match patterns: {}",
                    inner.as_str()
                ),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::{ConstExpression, ConstantValue};
    use crate::parser::grammar::{LangParser, Rule};
    use pest::Parser;

    #[test]
    fn test_var_or_constant_parser_identifier() {
        let mut ctx = ParseContext::new();
        let input = "test_var";
        let mut pairs = LangParser::parse(Rule::identifier, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = VarOrConstantParser::parse(pair, &mut ctx).unwrap();
        if let SimpleExpr::Var(name) = result {
            assert_eq!(name, "test_var");
        } else {
            panic!("Expected variable");
        }
    }

    #[test]
    fn test_var_or_constant_parser_numeric_literal() {
        let mut ctx = ParseContext::new();
        let input = "42";
        let mut pairs = LangParser::parse(Rule::constant_value, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = VarOrConstantParser::parse(pair, &mut ctx).unwrap();
        if let SimpleExpr::Constant(ConstExpression::Value(ConstantValue::Scalar(value))) = result {
            assert_eq!(value, 42);
        } else {
            panic!("Expected scalar constant");
        }
    }

    #[test]
    fn test_var_or_constant_parser_defined_constant() {
        let mut ctx = ParseContext::new();
        ctx.add_constant("MY_CONST".to_string(), 100).unwrap();

        let input = "MY_CONST";
        let mut pairs = LangParser::parse(Rule::identifier, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = VarOrConstantParser::parse(pair, &mut ctx).unwrap();
        if let SimpleExpr::Constant(ConstExpression::Value(ConstantValue::Scalar(value))) = result {
            assert_eq!(value, 100);
        } else {
            panic!("Expected scalar constant");
        }
    }

    #[test]
    fn test_var_or_constant_parser_public_input_start() {
        let mut ctx = ParseContext::new();
        let input = "public_input_start";
        let mut pairs = LangParser::parse(Rule::constant_value, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = VarOrConstantParser::parse(pair, &mut ctx).unwrap();
        if let SimpleExpr::Constant(ConstExpression::Value(ConstantValue::PublicInputStart)) =
            result
        {
            // Success
        } else {
            panic!("Expected PublicInputStart constant");
        }
    }

    #[test]
    fn test_var_or_constant_parser_pointer_to_zero_vector() {
        let mut ctx = ParseContext::new();
        let input = "pointer_to_zero_vector";
        let mut pairs = LangParser::parse(Rule::identifier, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = VarOrConstantParser::parse(pair, &mut ctx).unwrap();
        if let SimpleExpr::Constant(ConstExpression::Value(ConstantValue::PointerToZeroVector)) =
            result
        {
            // Success
        } else {
            panic!("Expected PointerToZeroVector constant");
        }
    }

    #[test]
    fn test_var_or_constant_parser_pointer_to_one_vector() {
        let mut ctx = ParseContext::new();
        let input = "pointer_to_one_vector";
        let mut pairs = LangParser::parse(Rule::identifier, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = VarOrConstantParser::parse(pair, &mut ctx).unwrap();
        if let SimpleExpr::Constant(ConstExpression::Value(ConstantValue::PointerToOneVector)) =
            result
        {
            // Success
        } else {
            panic!("Expected PointerToOneVector constant");
        }
    }

    #[test]
    fn test_const_expr_parser_numeric() {
        let mut ctx = ParseContext::new();
        let input = "123";
        let mut pairs = LangParser::parse(Rule::pattern, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ConstExprParser::parse(pair, &mut ctx).unwrap();
        assert_eq!(result, 123);
    }

    #[test]
    fn test_const_expr_parser_public_input_start_error() {
        let mut ctx = ParseContext::new();
        let input = "public_input_start";
        let mut pairs = LangParser::parse(Rule::pattern, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ConstExprParser::parse(pair, &mut ctx);
        assert!(result.is_err());
    }

    #[test]
    fn test_var_or_constant_parser_invalid_rule() {
        let mut ctx = ParseContext::new();
        let input = "42";
        let mut pairs = LangParser::parse(Rule::number, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = VarOrConstantParser::parse(pair, &mut ctx);
        assert!(result.is_err());
        if let Err(crate::parser::error::ParseError::SemanticError(error)) = result {
            assert!(error.message.contains("Expected identifier or constant"));
        } else {
            panic!("Expected SemanticError");
        }
    }
}
