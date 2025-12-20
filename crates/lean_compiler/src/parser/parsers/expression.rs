use super::literal::VarOrConstantParser;
use super::{Parse, ParseContext, next_inner_pair};
use crate::lang::MathExpr;
use crate::{
    ir::HighLevelOperation,
    lang::{ConstExpression, ConstantValue, Expression, SimpleExpr},
    parser::{
        error::{ParseError, ParseResult, SemanticError},
        grammar::{ParsePair, Rule},
    },
};

/// Parser for all expression types.
pub struct ExpressionParser;

impl Parse<Expression> for ExpressionParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Expression> {
        match pair.as_rule() {
            Rule::expression => {
                let inner = next_inner_pair(&mut pair.into_inner(), "expression body")?;
                Self.parse(inner, ctx)
            }
            Rule::neq_expr => BinaryExpressionParser::parse_with_op(pair, ctx, HighLevelOperation::NotEqual),
            Rule::eq_expr => BinaryExpressionParser::parse_with_op(pair, ctx, HighLevelOperation::Equal),
            Rule::add_expr => BinaryExpressionParser::parse_with_op(pair, ctx, HighLevelOperation::Add),
            Rule::sub_expr => BinaryExpressionParser::parse_with_op(pair, ctx, HighLevelOperation::Sub),
            Rule::mul_expr => BinaryExpressionParser::parse_with_op(pair, ctx, HighLevelOperation::Mul),
            Rule::mod_expr => BinaryExpressionParser::parse_with_op(pair, ctx, HighLevelOperation::Mod),
            Rule::div_expr => BinaryExpressionParser::parse_with_op(pair, ctx, HighLevelOperation::Div),
            Rule::exp_expr => BinaryExpressionParser::parse_with_op(pair, ctx, HighLevelOperation::Exp),
            Rule::primary => PrimaryExpressionParser.parse(pair, ctx),
            other_rule => Err(ParseError::SemanticError(SemanticError::new(format!(
                "ExpressionParser: Unexpected rule {other_rule:?}"
            )))),
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
        let mut expr = ExpressionParser.parse(next_inner_pair(&mut inner, "binary left")?, ctx)?;

        for right in inner {
            let right_expr = ExpressionParser.parse(right, ctx)?;
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
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Expression> {
        let inner = next_inner_pair(&mut pair.into_inner(), "primary expression")?;

        match inner.as_rule() {
            Rule::expression => ExpressionParser.parse(inner, ctx),
            Rule::var_or_constant => {
                let simple_expr = VarOrConstantParser.parse(inner, ctx)?;
                Ok(Expression::Value(simple_expr))
            }
            Rule::array_access_expr => ArrayAccessParser.parse(inner, ctx),
            Rule::log2_ceil_expr => MathExpr::Log2Ceil.parse(inner, ctx),
            Rule::next_multiple_of_expr => MathExpr::NextMultipleOf.parse(inner, ctx),
            Rule::len_expr => LenParser.parse(inner, ctx),
            _ => Err(SemanticError::new("Invalid primary expression").into()),
        }
    }
}

/// Parser for array access expressions.
pub struct ArrayAccessParser;

impl Parse<Expression> for ArrayAccessParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Expression> {
        let mut inner = pair.into_inner();
        let array = next_inner_pair(&mut inner, "array name")?.as_str().to_string();
        let index = ExpressionParser.parse(next_inner_pair(&mut inner, "array index")?, ctx)?;

        Ok(Expression::ArrayAccess {
            array: array.into(),
            index: Box::new(index),
        })
    }
}

impl Parse<Expression> for MathExpr {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Expression> {
        let mut inner = pair.into_inner();
        let mut args = Vec::new();
        for i in 0..self.num_args() {
            let expr =
                ExpressionParser.parse(next_inner_pair(&mut inner, &format!("math expr arg {}", i + 1))?, ctx)?;
            args.push(expr);
        }
        Ok(Expression::MathExpr(*self, args))
    }
}

/// Parser for len() expressions on const arrays.
pub struct LenParser;

impl Parse<Expression> for LenParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Expression> {
        let mut inner = pair.into_inner();
        let ident = next_inner_pair(&mut inner, "len argument")?.as_str();

        if let Some(arr) = ctx.get_const_array(ident) {
            Ok(Expression::Value(SimpleExpr::Constant(ConstExpression::Value(
                ConstantValue::Scalar(arr.len()),
            ))))
        } else {
            Err(SemanticError::with_context(
                format!("len() argument '{ident}' is not a const array"),
                "len expression",
            )
            .into())
        }
    }
}
