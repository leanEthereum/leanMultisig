use super::literal::{VarOrConstantParser, evaluate_const_expr};
use super::{ConstArrayValue, Parse, ParseContext, next_inner_pair};
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
            Rule::saturating_sub_expr => MathExpr::SaturatingSub.parse(inner, ctx),
            Rule::len_expr => LenParser.parse(inner, ctx),
            _ => Err(SemanticError::new("Invalid primary expression").into()),
        }
    }
}

/// Parser for array access expressions (supports chained indexing like arr[i][j]).
pub struct ArrayAccessParser;

impl Parse<Expression> for ArrayAccessParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Expression> {
        let mut inner = pair.into_inner();
        let array_name = next_inner_pair(&mut inner, "array name")?.as_str().to_string();

        let index: Vec<Expression> = inner
            .map(|idx_pair| ExpressionParser.parse(idx_pair, ctx))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Expression::ArrayAccess {
            array: SimpleExpr::Var(array_name),
            index,
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

/// Parser for len() expressions on const arrays (supports indexed access like len(ARR[i])).
pub struct LenParser;

impl Parse<Expression> for LenParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Expression> {
        let mut inner = pair.into_inner();
        let len_arg_pair = next_inner_pair(&mut inner, "len argument")?;

        // len_argument = { identifier ~ ("[" ~ expression ~ "]")* }
        let mut arg_inner = len_arg_pair.into_inner();
        let ident = next_inner_pair(&mut arg_inner, "array identifier")?
            .as_str()
            .to_string();

        // Check if the array exists
        if ctx.get_const_array(&ident).is_none() {
            return Err(SemanticError::with_context(
                format!("len() argument '{ident}' is not a const array"),
                "len expression",
            )
            .into());
        }

        let mut index_exprs = Vec::new();
        for index_pair in arg_inner {
            index_exprs.push(ExpressionParser.parse(index_pair, ctx)?);
        }

        // Now evaluate the indices
        let mut indices = Vec::new();
        for index_expr in &index_exprs {
            let index_val = evaluate_const_expr(index_expr, ctx).ok_or_else(|| {
                SemanticError::with_context("Index in len() must be a compile-time constant", "len expression")
            })?;
            indices.push(index_val);
        }

        // Now get the array again and navigate to the target sub-array
        let base_array = ctx.get_const_array(&ident).unwrap();
        let target = if indices.is_empty() {
            base_array
        } else {
            base_array.navigate(&indices).ok_or_else(|| {
                SemanticError::with_context(
                    format!(
                        "len() index out of bounds for '{ident}': [{}]",
                        indices.iter().map(|i| i.to_string()).collect::<Vec<_>>().join("][")
                    ),
                    "len expression",
                )
            })?
        };

        // Get its length
        let length = match target {
            ConstArrayValue::Scalar(_) => {
                return Err(
                    SemanticError::with_context("Cannot call len() on a scalar value", "len expression").into(),
                );
            }
            ConstArrayValue::Array(arr) => arr.len(),
        };

        Ok(Expression::Value(SimpleExpr::Constant(ConstExpression::Value(
            ConstantValue::Scalar(length),
        ))))
    }
}
