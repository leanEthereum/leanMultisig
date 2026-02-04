use lean_vm::{F, SourceLocation};
use multilinear_toolkit::prelude::*;

use super::literal::{VarOrConstantParser, evaluate_const_expr};
use super::{ConstArrayValue, Parse, ParseContext, next_inner_pair};
use crate::lang::MathOperation;
use crate::{
    lang::{ConstExpression, ConstantValue, Expression, SimpleExpr, VecLiteral},
    parser::{
        error::{ParseResult, SemanticError},
        grammar::{ParsePair, Rule},
    },
};

pub struct ExpressionParser;

impl Parse<Expression> for ExpressionParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Expression> {
        match pair.as_rule() {
            Rule::expression => {
                let inner = next_inner_pair(&mut pair.into_inner(), "expression body")?;
                Self.parse(inner, ctx)
            }
            Rule::add_expr => MathOperation::Add.parse(pair, ctx),
            Rule::sub_expr => MathOperation::Sub.parse(pair, ctx),
            Rule::mul_expr => MathOperation::Mul.parse(pair, ctx),
            Rule::mod_expr => MathOperation::Mod.parse(pair, ctx),
            Rule::div_expr => MathOperation::Div.parse(pair, ctx),
            Rule::exp_expr => MathOperation::Exp.parse(pair, ctx),
            Rule::log2_ceil_expr => MathOperation::Log2Ceil.parse(pair, ctx),
            Rule::next_multiple_of_expr => MathOperation::NextMultipleOf.parse(pair, ctx),
            Rule::div_ceil_expr => MathOperation::DivCeil.parse(pair, ctx),
            Rule::saturating_sub_expr => MathOperation::SaturatingSub.parse(pair, ctx),
            Rule::var_or_constant => Ok(Expression::Value(VarOrConstantParser.parse(pair, ctx)?)),
            Rule::array_access_expr => ArrayAccessParser.parse(pair, ctx),
            Rule::len_expr => LenParser.parse(pair, ctx),
            Rule::function_call_expr => FunctionCallExprParser.parse(pair, ctx),
            Rule::lambda_expr => LambdaParser.parse(pair, ctx),
            Rule::primary => {
                let inner = next_inner_pair(&mut pair.into_inner(), "primary expression")?;
                Self.parse(inner, ctx)
            }
            other_rule => Err(SemanticError::new(format!("ExpressionParser: Unexpected rule {other_rule:?}")).into()),
        }
    }
}

impl Parse<Expression> for MathOperation {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Expression> {
        let mut inner = pair.into_inner();
        let mut expr = ExpressionParser.parse(next_inner_pair(&mut inner, "math expr left")?, ctx)?;

        if self.is_unary() {
            return Ok(Expression::MathExpr(*self, vec![expr]));
        }

        for right in inner {
            let right_expr = ExpressionParser.parse(right, ctx)?;
            expr = Expression::MathExpr(*self, vec![expr, right_expr]);
        }

        Ok(expr)
    }
}

pub struct FunctionCallExprParser;

impl Parse<Expression> for FunctionCallExprParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Expression> {
        let line_number = pair.line_col().0;
        let mut inner = pair.into_inner();
        let function_name = next_inner_pair(&mut inner, "function name")?.as_str().to_string();

        let args = if let Some(tuple_pair) = inner.next() {
            tuple_pair
                .into_inner()
                .map(|item| ExpressionParser.parse(item, ctx))
                .collect::<Result<Vec<_>, _>>()?
        } else {
            Vec::new()
        };

        Ok(Expression::FunctionCall {
            function_name,
            args,
            location: SourceLocation {
                file_id: ctx.current_file_id,
                line_number,
            },
        })
    }
}

/// Parser for lambda expressions: `lambda param: body`
pub struct LambdaParser;

impl Parse<Expression> for LambdaParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Expression> {
        let mut inner = pair.into_inner();
        let param = next_inner_pair(&mut inner, "lambda parameter")?.as_str().to_string();
        let body = ExpressionParser.parse(next_inner_pair(&mut inner, "lambda body")?, ctx)?;

        Ok(Expression::Lambda {
            param,
            body: Box::new(body),
        })
    }
}

/// Parser for array access expressions (supports chained indexing like arr[i][j]).
pub struct ArrayAccessParser;

impl Parse<Expression> for ArrayAccessParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Expression> {
        let mut inner = pair.into_inner();
        let array = next_inner_pair(&mut inner, "array name")?.as_str().to_string();

        let index: Vec<Expression> = inner
            .map(|idx_pair| ExpressionParser.parse(idx_pair, ctx))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Expression::ArrayAccess { array, index })
    }
}

/// Parser for len() expressions on const arrays and vectors (supports indexed access like len(ARR[i])).
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

        let mut index_exprs = Vec::new();
        for index_pair in arg_inner {
            index_exprs.push(ExpressionParser.parse(index_pair, ctx)?);
        }

        // Check if this is a const array - if so, try to evaluate at parse time
        if let Some(base_array) = ctx.get_const_array(&ident) {
            // Try to evaluate indices at parse time
            let mut indices = Vec::new();
            let mut all_const = true;
            for index_expr in &index_exprs {
                if let Some(index_val) = evaluate_const_expr(index_expr, ctx) {
                    indices.push(index_val);
                } else {
                    all_const = false;
                    break;
                }
            }

            // If all indices are constants, evaluate len() now
            if all_const {
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

                let length = match target {
                    ConstArrayValue::Scalar(_) => {
                        return Err(SemanticError::with_context(
                            "Cannot call len() on a scalar value",
                            "len expression",
                        )
                        .into());
                    }
                    ConstArrayValue::Array(arr) => arr.len(),
                };

                return Ok(Expression::Value(SimpleExpr::Constant(ConstExpression::Value(
                    ConstantValue::Scalar(F::from_usize(length)),
                ))));
            }
        }

        // Defer evaluation for non-const arrays (could be vectors) or non-const indices
        Ok(Expression::Len {
            array: ident,
            indices: index_exprs,
        })
    }
}

/// Parser for vec![...] literals (compile-time vectors)
/// Parses into the VecLiteral enum (separate from Expression)
pub struct VecLiteralParser;

impl Parse<VecLiteral> for VecLiteralParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<VecLiteral> {
        // vec_literal = { "vec!" ~ "[" ~ (vec_element ~ ("," ~ vec_element)*)? ~ "]" }
        // vec_element = { vec_literal | expression }
        let elements: Vec<VecLiteral> = pair
            .into_inner()
            .map(|elem_pair| VecElementParser.parse(elem_pair, ctx))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(VecLiteral::Vec(elements))
    }
}

/// Parser for vec element (either a nested vec_literal or an expression)
pub struct VecElementParser;

impl Parse<VecLiteral> for VecElementParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<VecLiteral> {
        match pair.as_rule() {
            Rule::vec_element => {
                // vec_element contains either vec_literal or expression
                let inner = next_inner_pair(&mut pair.into_inner(), "vec element")?;
                match inner.as_rule() {
                    Rule::vec_literal => VecLiteralParser.parse(inner, ctx),
                    _ => Ok(VecLiteral::Expr(ExpressionParser.parse(inner, ctx)?)),
                }
            }
            Rule::vec_literal => VecLiteralParser.parse(pair, ctx),
            _ => Ok(VecLiteral::Expr(ExpressionParser.parse(pair, ctx)?)),
        }
    }
}
