use super::literal::VarOrConstantParser;
use super::{Parse, ParseContext, next_inner_pair};
use crate::{
    ir::HighLevelOperation,
    lang::Expression,
    parser::{
        error::{ParseResult, SemanticError},
        grammar::{ParsePair, Rule},
    },
};

/// Parser for all expression types.
pub struct ExpressionParser;

impl Parse<Expression> for ExpressionParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Expression> {
        match pair.as_rule() {
            Rule::expression => {
                let inner = next_inner_pair(&mut pair.into_inner(), "expression body")?;
                Self::parse(inner, ctx)
            }
            Rule::add_expr => {
                BinaryExpressionParser::parse_with_op(pair, ctx, HighLevelOperation::Add)
            }
            Rule::sub_expr => {
                BinaryExpressionParser::parse_with_op(pair, ctx, HighLevelOperation::Sub)
            }
            Rule::mul_expr => {
                BinaryExpressionParser::parse_with_op(pair, ctx, HighLevelOperation::Mul)
            }
            Rule::mod_expr => {
                BinaryExpressionParser::parse_with_op(pair, ctx, HighLevelOperation::Mod)
            }
            Rule::div_expr => {
                BinaryExpressionParser::parse_with_op(pair, ctx, HighLevelOperation::Div)
            }
            Rule::exp_expr => {
                BinaryExpressionParser::parse_with_op(pair, ctx, HighLevelOperation::Exp)
            }
            Rule::primary => PrimaryExpressionParser::parse(pair, ctx),
            _ => Err(SemanticError::new("Invalid expression").into()),
        }
    }
}

/// Parser for binary arithmetic operations.
pub struct BinaryExpressionParser;

impl BinaryExpressionParser {
    pub fn parse_with_op(
        pair: ParsePair<'_>,
        ctx: &mut ParseContext,
        operation: HighLevelOperation,
    ) -> ParseResult<Expression> {
        let mut inner = pair.into_inner();
        let mut expr = ExpressionParser::parse(next_inner_pair(&mut inner, "binary left")?, ctx)?;

        for right in inner {
            let right_expr = ExpressionParser::parse(right, ctx)?;
            expr = Expression::Binary {
                left: Box::new(expr),
                operation,
                right: Box::new(right_expr),
            };
        }

        Ok(expr)
    }
}

/// Parser for primary expressions (variables, constants, parenthesized expressions).
pub struct PrimaryExpressionParser;

impl Parse<Expression> for PrimaryExpressionParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Expression> {
        let inner = next_inner_pair(&mut pair.into_inner(), "primary expression")?;

        match inner.as_rule() {
            Rule::expression => ExpressionParser::parse(inner, ctx),
            Rule::var_or_constant => {
                let simple_expr = VarOrConstantParser::parse(inner, ctx)?;
                Ok(Expression::Value(simple_expr))
            }
            Rule::array_access_expr => ArrayAccessParser::parse(inner, ctx),
            Rule::log2_ceil_expr => Log2CeilParser::parse(inner, ctx),
            _ => Err(SemanticError::new("Invalid primary expression").into()),
        }
    }
}

/// Parser for array access expressions.
pub struct ArrayAccessParser;

impl Parse<Expression> for ArrayAccessParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Expression> {
        let mut inner = pair.into_inner();
        let array = next_inner_pair(&mut inner, "array name")?
            .as_str()
            .to_string();
        let index = ExpressionParser::parse(next_inner_pair(&mut inner, "array index")?, ctx)?;

        Ok(Expression::ArrayAccess {
            array: array.into(),
            index: Box::new(index),
        })
    }
}

/// Parser for log2_ceil function calls.
pub struct Log2CeilParser;

impl Parse<Expression> for Log2CeilParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Expression> {
        let mut inner = pair.into_inner();
        let expr = ExpressionParser::parse(next_inner_pair(&mut inner, "log2_ceil value")?, ctx)?;

        Ok(Expression::Log2Ceil {
            value: Box::new(expr),
        })
    }
}
