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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::HighLevelOperation;
    use crate::lang::{Expression, SimpleExpr};
    use crate::parser::grammar::{LangParser, Rule};
    use pest::Parser;

    #[test]
    fn test_expression_parser_primary() {
        let mut ctx = ParseContext::new();
        let input = "42";
        let mut pairs = LangParser::parse(Rule::expression, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ExpressionParser::parse(pair, &mut ctx).unwrap();
        assert_eq!(result, Expression::scalar(42));
    }

    #[test]
    fn test_expression_parser_add() {
        let mut ctx = ParseContext::new();
        let input = "10 + 20";
        let mut pairs = LangParser::parse(Rule::expression, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ExpressionParser::parse(pair, &mut ctx).unwrap();
        if let Expression::Binary {
            left,
            operation,
            right,
        } = result
        {
            assert_eq!(*left, Expression::scalar(10));
            assert_eq!(operation, HighLevelOperation::Add);
            assert_eq!(*right, Expression::scalar(20));
        } else {
            panic!("Expected Binary expression");
        }
    }

    #[test]
    fn test_expression_parser_sub() {
        let mut ctx = ParseContext::new();
        let input = "30 - 5";
        let mut pairs = LangParser::parse(Rule::expression, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ExpressionParser::parse(pair, &mut ctx).unwrap();
        if let Expression::Binary {
            left,
            operation,
            right,
        } = result
        {
            assert_eq!(*left, Expression::scalar(30));
            assert_eq!(operation, HighLevelOperation::Sub);
            assert_eq!(*right, Expression::scalar(5));
        } else {
            panic!("Expected Binary expression");
        }
    }

    #[test]
    fn test_expression_parser_mul() {
        let mut ctx = ParseContext::new();
        let input = "6 * 7";
        let mut pairs = LangParser::parse(Rule::expression, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ExpressionParser::parse(pair, &mut ctx).unwrap();
        if let Expression::Binary {
            left,
            operation,
            right,
        } = result
        {
            assert_eq!(*left, Expression::scalar(6));
            assert_eq!(operation, HighLevelOperation::Mul);
            assert_eq!(*right, Expression::scalar(7));
        } else {
            panic!("Expected Binary expression");
        }
    }

    #[test]
    fn test_expression_parser_mod() {
        let mut ctx = ParseContext::new();
        let input = "15 % 4";
        let mut pairs = LangParser::parse(Rule::expression, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ExpressionParser::parse(pair, &mut ctx).unwrap();
        if let Expression::Binary {
            left,
            operation,
            right,
        } = result
        {
            assert_eq!(*left, Expression::scalar(15));
            assert_eq!(operation, HighLevelOperation::Mod);
            assert_eq!(*right, Expression::scalar(4));
        } else {
            panic!("Expected Binary expression");
        }
    }

    #[test]
    fn test_expression_parser_div() {
        let mut ctx = ParseContext::new();
        let input = "20 / 4";
        let mut pairs = LangParser::parse(Rule::expression, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ExpressionParser::parse(pair, &mut ctx).unwrap();
        if let Expression::Binary {
            left,
            operation,
            right,
        } = result
        {
            assert_eq!(*left, Expression::scalar(20));
            assert_eq!(operation, HighLevelOperation::Div);
            assert_eq!(*right, Expression::scalar(4));
        } else {
            panic!("Expected Binary expression");
        }
    }

    #[test]
    fn test_expression_parser_exp() {
        let mut ctx = ParseContext::new();
        let input = "2 ** 8";
        let mut pairs = LangParser::parse(Rule::expression, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ExpressionParser::parse(pair, &mut ctx).unwrap();
        if let Expression::Binary {
            left,
            operation,
            right,
        } = result
        {
            assert_eq!(*left, Expression::scalar(2));
            assert_eq!(operation, HighLevelOperation::Exp);
            assert_eq!(*right, Expression::scalar(8));
        } else {
            panic!("Expected Binary expression");
        }
    }

    #[test]
    fn test_primary_expression_parser_parentheses() {
        let mut ctx = ParseContext::new();
        let input = "(42)";
        let mut pairs = LangParser::parse(Rule::primary, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = PrimaryExpressionParser::parse(pair, &mut ctx).unwrap();
        assert_eq!(result, Expression::scalar(42));
    }

    #[test]
    fn test_primary_expression_parser_variable() {
        let mut ctx = ParseContext::new();
        let input = "x";
        let mut pairs = LangParser::parse(Rule::primary, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = PrimaryExpressionParser::parse(pair, &mut ctx).unwrap();
        assert_eq!(result, Expression::Value(SimpleExpr::Var("x".to_string())));
    }

    #[test]
    fn test_array_access_parser() {
        let mut ctx = ParseContext::new();
        let input = "arr[10]";
        let mut pairs = LangParser::parse(Rule::array_access_expr, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ArrayAccessParser::parse(pair, &mut ctx).unwrap();
        if let Expression::ArrayAccess { array, index } = result {
            assert_eq!(array, SimpleExpr::Var("arr".to_string()));
            assert_eq!(*index, Expression::scalar(10));
        } else {
            panic!("Expected ArrayAccess");
        }
    }

    #[test]
    fn test_log2_ceil_parser() {
        let mut ctx = ParseContext::new();
        let input = "log2_ceil(16)";
        let mut pairs = LangParser::parse(Rule::log2_ceil_expr, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = Log2CeilParser::parse(pair, &mut ctx).unwrap();
        if let Expression::Log2Ceil { value } = result {
            assert_eq!(*value, Expression::scalar(16));
        } else {
            panic!("Expected Log2Ceil");
        }
    }

    #[test]
    fn test_binary_expression_parser_chain() {
        let mut ctx = ParseContext::new();
        let input = "1 + 2 + 3";
        let mut pairs = LangParser::parse(Rule::expression, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ExpressionParser::parse(pair, &mut ctx).unwrap();
        if let Expression::Binary {
            left,
            operation,
            right,
        } = result
        {
            if let Expression::Binary {
                left: inner_left,
                operation: inner_op,
                right: inner_right,
            } = *left
            {
                assert_eq!(*inner_left, Expression::scalar(1));
                assert_eq!(inner_op, HighLevelOperation::Add);
                assert_eq!(*inner_right, Expression::scalar(2));
            } else {
                panic!("Expected nested Binary expression");
            }
            assert_eq!(operation, HighLevelOperation::Add);
            assert_eq!(*right, Expression::scalar(3));
        } else {
            panic!("Expected Binary expression");
        }
    }
}
