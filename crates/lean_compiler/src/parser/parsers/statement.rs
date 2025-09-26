use super::expression::ExpressionParser;
use super::function::{FunctionCallParser, TupleExpressionParser};
use super::literal::ConstExprParser;
use super::{Parse, ParseContext, next_inner_pair};
use crate::{
    lang::{Boolean, Line},
    parser::{
        error::{ParseResult, SemanticError},
        grammar::{ParsePair, Rule},
    },
};

/// Add a statement with location tracking.
fn add_statement_with_location(
    lines: &mut Vec<Line>,
    pair: ParsePair<'_>,
    ctx: &mut ParseContext,
) -> ParseResult<()> {
    let location = pair.line_col().0;
    let line = StatementParser::parse(pair, ctx)?;

    lines.push(Line::LocationReport { location });
    lines.push(line);

    Ok(())
}

/// Parser for all statement types.
pub struct StatementParser;

impl Parse<Line> for StatementParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let inner = next_inner_pair(&mut pair.into_inner(), "statement body")?;

        match inner.as_rule() {
            Rule::single_assignment => AssignmentParser::parse(inner, ctx),
            Rule::array_assign => ArrayAssignParser::parse(inner, ctx),
            Rule::if_statement => IfStatementParser::parse(inner, ctx),
            Rule::for_statement => ForStatementParser::parse(inner, ctx),
            Rule::match_statement => MatchStatementParser::parse(inner, ctx),
            Rule::return_statement => ReturnStatementParser::parse(inner, ctx),
            Rule::function_call => FunctionCallParser::parse(inner, ctx),
            Rule::assert_eq_statement => AssertEqParser::parse(inner, ctx),
            Rule::assert_not_eq_statement => AssertNotEqParser::parse(inner, ctx),
            Rule::break_statement => Ok(Line::Break),
            Rule::continue_statement => {
                Err(SemanticError::new("Continue statement not implemented yet").into())
            }
            _ => Err(SemanticError::new("Unknown statement").into()),
        }
    }
}

/// Parser for variable assignments.
pub struct AssignmentParser;

impl Parse<Line> for AssignmentParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let mut inner = pair.into_inner();
        let var = next_inner_pair(&mut inner, "variable name")?
            .as_str()
            .to_string();
        let expr = next_inner_pair(&mut inner, "assignment value")?;
        let value = ExpressionParser::parse(expr, ctx)?;

        Ok(Line::Assignment { var, value })
    }
}

/// Parser for array element assignments.
pub struct ArrayAssignParser;

impl Parse<Line> for ArrayAssignParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let mut inner = pair.into_inner();
        let array = next_inner_pair(&mut inner, "array name")?
            .as_str()
            .to_string();
        let index = ExpressionParser::parse(next_inner_pair(&mut inner, "array index")?, ctx)?;
        let value = ExpressionParser::parse(next_inner_pair(&mut inner, "array value")?, ctx)?;

        Ok(Line::ArrayAssign {
            array: array.into(),
            index,
            value,
        })
    }
}

/// Parser for if-else conditional statements.
pub struct IfStatementParser;

impl Parse<Line> for IfStatementParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let mut inner = pair.into_inner();
        let condition = ConditionParser::parse(next_inner_pair(&mut inner, "if condition")?, ctx)?;

        let mut then_branch = Vec::new();
        let mut else_branch = Vec::new();

        for item in inner {
            match item.as_rule() {
                Rule::statement => {
                    add_statement_with_location(&mut then_branch, item, ctx)?;
                }
                Rule::else_clause => {
                    for else_item in item.into_inner() {
                        if else_item.as_rule() == Rule::statement {
                            add_statement_with_location(&mut else_branch, else_item, ctx)?;
                        }
                    }
                }
                _ => {}
            }
        }

        Ok(Line::IfCondition {
            condition,
            then_branch,
            else_branch,
        })
    }
}

/// Parser for for-loop statements.
pub struct ForStatementParser;

impl Parse<Line> for ForStatementParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let mut inner = pair.into_inner();
        let iterator = next_inner_pair(&mut inner, "loop iterator")?
            .as_str()
            .to_string();

        // Check for optional reverse clause using efficient peek
        let mut rev = false;
        if let Some(peeked) = inner.peek()
            && peeked.as_rule() == Rule::rev_clause {
                rev = true;
                inner.next(); // Consume the rev clause
            }

        let start = ExpressionParser::parse(next_inner_pair(&mut inner, "loop start")?, ctx)?;
        let end = ExpressionParser::parse(next_inner_pair(&mut inner, "loop end")?, ctx)?;

        let mut unroll = false;
        let mut body = Vec::new();

        for item in inner {
            match item.as_rule() {
                Rule::unroll_clause => {
                    unroll = true;
                }
                Rule::statement => {
                    add_statement_with_location(&mut body, item, ctx)?;
                }
                _ => {}
            }
        }

        Ok(Line::ForLoop {
            iterator,
            start,
            end,
            body,
            rev,
            unroll,
        })
    }
}

/// Parser for match statements with pattern matching.
pub struct MatchStatementParser;

impl Parse<Line> for MatchStatementParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let mut inner = pair.into_inner();
        let value = ExpressionParser::parse(next_inner_pair(&mut inner, "match value")?, ctx)?;

        let mut arms = Vec::new();

        for arm_pair in inner {
            if arm_pair.as_rule() == Rule::match_arm {
                let mut arm_inner = arm_pair.into_inner();
                let const_expr = next_inner_pair(&mut arm_inner, "match pattern")?;
                let pattern = ConstExprParser::parse(const_expr, ctx)?;

                let mut statements = Vec::new();
                for stmt in arm_inner {
                    if stmt.as_rule() == Rule::statement {
                        add_statement_with_location(&mut statements, stmt, ctx)?;
                    }
                }

                arms.push((pattern, statements));
            }
        }

        Ok(Line::Match { value, arms })
    }
}

/// Parser for return statements.
pub struct ReturnStatementParser;

impl Parse<Line> for ReturnStatementParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let mut return_data = Vec::new();

        for item in pair.into_inner() {
            if item.as_rule() == Rule::tuple_expression {
                return_data = TupleExpressionParser::parse(item, ctx)?;
            }
        }

        Ok(Line::FunctionRet { return_data })
    }
}

/// Parser for boolean conditions used in if statements and assertions.
pub struct ConditionParser;

impl Parse<Boolean> for ConditionParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Boolean> {
        let inner = next_inner_pair(&mut pair.into_inner(), "condition")?;
        let mut parts = inner.clone().into_inner();

        let left = ExpressionParser::parse(next_inner_pair(&mut parts, "left side")?, ctx)?;
        let right = ExpressionParser::parse(next_inner_pair(&mut parts, "right side")?, ctx)?;

        match inner.as_rule() {
            Rule::condition_eq => Ok(Boolean::Equal { left, right }),
            Rule::condition_diff => Ok(Boolean::Different { left, right }),
            _ => Err(SemanticError::new("Invalid condition type").into()),
        }
    }
}

/// Parser for equality assertions.
pub struct AssertEqParser;

impl Parse<Line> for AssertEqParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let mut inner = pair.into_inner();
        let left = ExpressionParser::parse(next_inner_pair(&mut inner, "left assertion")?, ctx)?;
        let right = ExpressionParser::parse(next_inner_pair(&mut inner, "right assertion")?, ctx)?;

        Ok(Line::Assert(Boolean::Equal { left, right }))
    }
}

/// Parser for inequality assertions.
pub struct AssertNotEqParser;

impl Parse<Line> for AssertNotEqParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let mut inner = pair.into_inner();
        let left = ExpressionParser::parse(next_inner_pair(&mut inner, "left assertion")?, ctx)?;
        let right = ExpressionParser::parse(next_inner_pair(&mut inner, "right assertion")?, ctx)?;

        Ok(Line::Assert(Boolean::Different { left, right }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::Line;
    use crate::parser::grammar::{LangParser, Rule};
    use pest::Parser;

    #[test]
    fn test_for_loop_with_rev_clause() {
        let mut ctx = ParseContext::new();
        let input = r#"for i in rev 0..10 { break; }"#;
        let mut pairs = LangParser::parse(Rule::for_statement, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ForStatementParser::parse(pair, &mut ctx).unwrap();
        if let Line::ForLoop {
            iterator,
            start,
            end,
            body,
            rev,
            unroll,
        } = result
        {
            assert_eq!(iterator, "i");
            assert_eq!(start, crate::lang::Expression::scalar(0));
            assert_eq!(end, crate::lang::Expression::scalar(10));
            assert_eq!(body.len(), 2); // LocationReport + Break
            assert!(rev);
            assert!(!unroll);
        } else {
            panic!("Expected ForLoop");
        }
    }

    #[test]
    fn test_for_loop_without_rev_clause() {
        let mut ctx = ParseContext::new();
        let input = r#"for i in 0..10 { break; }"#;
        let mut pairs = LangParser::parse(Rule::for_statement, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ForStatementParser::parse(pair, &mut ctx).unwrap();
        if let Line::ForLoop {
            iterator,
            start,
            end,
            body,
            rev,
            unroll,
        } = result
        {
            assert_eq!(iterator, "i");
            assert_eq!(start, crate::lang::Expression::scalar(0));
            assert_eq!(end, crate::lang::Expression::scalar(10));
            assert_eq!(body.len(), 2); // LocationReport + Break
            assert!(!rev);
            assert!(!unroll);
        } else {
            panic!("Expected ForLoop");
        }
    }

    #[test]
    fn test_for_loop_with_unroll_clause() {
        let mut ctx = ParseContext::new();
        let input = r#"for i in 0..10 unroll { break; }"#;
        let mut pairs = LangParser::parse(Rule::for_statement, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ForStatementParser::parse(pair, &mut ctx).unwrap();
        if let Line::ForLoop {
            iterator,
            start,
            end,
            body,
            rev,
            unroll,
        } = result
        {
            assert_eq!(iterator, "i");
            assert_eq!(start, crate::lang::Expression::scalar(0));
            assert_eq!(end, crate::lang::Expression::scalar(10));
            assert_eq!(body.len(), 2); // LocationReport + Break
            assert!(!rev);
            assert!(unroll);
        } else {
            panic!("Expected ForLoop");
        }
    }

    #[test]
    fn test_for_loop_with_rev_and_unroll() {
        let mut ctx = ParseContext::new();
        let input = r#"for i in rev 0..10 unroll { break; }"#;
        let mut pairs = LangParser::parse(Rule::for_statement, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ForStatementParser::parse(pair, &mut ctx).unwrap();
        if let Line::ForLoop {
            iterator,
            start,
            end,
            body,
            rev,
            unroll,
        } = result
        {
            assert_eq!(iterator, "i");
            assert_eq!(start, crate::lang::Expression::scalar(0));
            assert_eq!(end, crate::lang::Expression::scalar(10));
            assert_eq!(body.len(), 2); // LocationReport + Break
            assert!(rev);
            assert!(unroll);
        } else {
            panic!("Expected ForLoop");
        }
    }

    #[test]
    fn test_statement_parser_break_statement() {
        let mut ctx = ParseContext::new();
        let input = "break;";
        let mut pairs = LangParser::parse(Rule::statement, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = StatementParser::parse(pair, &mut ctx).unwrap();
        assert_eq!(result, Line::Break);
    }

    #[test]
    fn test_statement_parser_continue_statement() {
        let mut ctx = ParseContext::new();
        let input = "continue;";
        let mut pairs = LangParser::parse(Rule::statement, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = StatementParser::parse(pair, &mut ctx);
        assert!(result.is_err());
        if let Err(crate::parser::error::ParseError::SemanticError(error)) = result {
            assert!(
                error
                    .message
                    .contains("Continue statement not implemented yet")
            );
        } else {
            panic!("Expected SemanticError");
        }
    }

    #[test]
    fn test_assignment_parser() {
        let mut ctx = ParseContext::new();
        let input = "x = 42;";
        let mut pairs = LangParser::parse(Rule::single_assignment, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = AssignmentParser::parse(pair, &mut ctx).unwrap();
        if let Line::Assignment { var, value } = result {
            assert_eq!(var, "x");
            assert_eq!(value, crate::lang::Expression::scalar(42));
        } else {
            panic!("Expected Assignment");
        }
    }

    #[test]
    fn test_array_assign_parser() {
        let mut ctx = ParseContext::new();
        let input = "arr[5] = 100;";
        let mut pairs = LangParser::parse(Rule::array_assign, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ArrayAssignParser::parse(pair, &mut ctx).unwrap();
        if let Line::ArrayAssign {
            array,
            index,
            value,
        } = result
        {
            assert_eq!(array, crate::lang::SimpleExpr::Var("arr".to_string()));
            assert_eq!(index, crate::lang::Expression::scalar(5));
            assert_eq!(value, crate::lang::Expression::scalar(100));
        } else {
            panic!("Expected ArrayAssign");
        }
    }

    #[test]
    fn test_assert_eq_parser() {
        let mut ctx = ParseContext::new();
        let input = "assert 10 == 20;";
        let mut pairs = LangParser::parse(Rule::assert_eq_statement, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = AssertEqParser::parse(pair, &mut ctx).unwrap();
        if let Line::Assert(crate::lang::Boolean::Equal { left, right }) = result {
            assert_eq!(left, crate::lang::Expression::scalar(10));
            assert_eq!(right, crate::lang::Expression::scalar(20));
        } else {
            panic!("Expected Assert with Equal condition");
        }
    }

    #[test]
    fn test_assert_not_eq_parser() {
        let mut ctx = ParseContext::new();
        let input = "assert 10 != 20;";
        let mut pairs = LangParser::parse(Rule::assert_not_eq_statement, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = AssertNotEqParser::parse(pair, &mut ctx).unwrap();
        if let Line::Assert(crate::lang::Boolean::Different { left, right }) = result {
            assert_eq!(left, crate::lang::Expression::scalar(10));
            assert_eq!(right, crate::lang::Expression::scalar(20));
        } else {
            panic!("Expected Assert with Different condition");
        }
    }

    #[test]
    fn test_condition_parser_equal() {
        let mut ctx = ParseContext::new();
        let input = "x == 5";
        let mut pairs = LangParser::parse(Rule::condition, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ConditionParser::parse(pair, &mut ctx).unwrap();
        if let crate::lang::Boolean::Equal { left, right } = result {
            assert_eq!(
                left,
                crate::lang::Expression::Value(crate::lang::SimpleExpr::Var("x".to_string()))
            );
            assert_eq!(right, crate::lang::Expression::scalar(5));
        } else {
            panic!("Expected Equal condition");
        }
    }

    #[test]
    fn test_condition_parser_different() {
        let mut ctx = ParseContext::new();
        let input = "y != 10";
        let mut pairs = LangParser::parse(Rule::condition, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ConditionParser::parse(pair, &mut ctx).unwrap();
        if let crate::lang::Boolean::Different { left, right } = result {
            assert_eq!(
                left,
                crate::lang::Expression::Value(crate::lang::SimpleExpr::Var("y".to_string()))
            );
            assert_eq!(right, crate::lang::Expression::scalar(10));
        } else {
            panic!("Expected Different condition");
        }
    }

    #[test]
    fn test_return_statement_parser_empty() {
        let mut ctx = ParseContext::new();
        let input = "return;";
        let mut pairs = LangParser::parse(Rule::return_statement, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ReturnStatementParser::parse(pair, &mut ctx).unwrap();
        if let Line::FunctionRet { return_data } = result {
            assert!(return_data.is_empty());
        } else {
            panic!("Expected FunctionRet");
        }
    }

    #[test]
    fn test_return_statement_parser_with_values() {
        let mut ctx = ParseContext::new();
        let input = "return 42, 100;";
        let mut pairs = LangParser::parse(Rule::return_statement, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = ReturnStatementParser::parse(pair, &mut ctx).unwrap();
        if let Line::FunctionRet { return_data } = result {
            assert_eq!(return_data.len(), 2);
            assert_eq!(return_data[0], crate::lang::Expression::scalar(42));
            assert_eq!(return_data[1], crate::lang::Expression::scalar(100));
        } else {
            panic!("Expected FunctionRet");
        }
    }

    #[test]
    fn test_match_statement_parser() {
        let mut ctx = ParseContext::new();
        let input = r#"match x { 0 => { break; } 1 => { break; } }"#;
        let mut pairs = LangParser::parse(Rule::match_statement, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = MatchStatementParser::parse(pair, &mut ctx).unwrap();
        if let Line::Match { value, arms } = result {
            assert_eq!(
                value,
                crate::lang::Expression::Value(crate::lang::SimpleExpr::Var("x".to_string()))
            );
            assert_eq!(arms.len(), 2);
            assert_eq!(arms[0].0, 0);
            assert_eq!(arms[1].0, 1);
            assert_eq!(arms[0].1.len(), 2); // LocationReport + Break
            assert_eq!(arms[1].1.len(), 2); // LocationReport + Break
        } else {
            panic!("Expected Match");
        }
    }

    #[test]
    fn test_if_statement_parser_no_else() {
        let mut ctx = ParseContext::new();
        let input = r#"if x == 0 { break; }"#;
        let mut pairs = LangParser::parse(Rule::if_statement, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = IfStatementParser::parse(pair, &mut ctx).unwrap();
        if let Line::IfCondition {
            condition,
            then_branch,
            else_branch,
        } = result
        {
            if let crate::lang::Boolean::Equal { left, right } = condition {
                assert_eq!(
                    left,
                    crate::lang::Expression::Value(crate::lang::SimpleExpr::Var("x".to_string()))
                );
                assert_eq!(right, crate::lang::Expression::scalar(0));
            } else {
                panic!("Expected Equal condition");
            }
            assert_eq!(then_branch.len(), 2); // LocationReport + Break
            assert!(else_branch.is_empty());
        } else {
            panic!("Expected IfCondition");
        }
    }

    #[test]
    fn test_if_statement_parser_with_else() {
        let mut ctx = ParseContext::new();
        let input = r#"if x == 0 { break; } else { break; }"#;
        let mut pairs = LangParser::parse(Rule::if_statement, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = IfStatementParser::parse(pair, &mut ctx).unwrap();
        if let Line::IfCondition {
            condition,
            then_branch,
            else_branch,
        } = result
        {
            if let crate::lang::Boolean::Equal { left, right } = condition {
                assert_eq!(
                    left,
                    crate::lang::Expression::Value(crate::lang::SimpleExpr::Var("x".to_string()))
                );
                assert_eq!(right, crate::lang::Expression::scalar(0));
            } else {
                panic!("Expected Equal condition");
            }
            assert_eq!(then_branch.len(), 2); // LocationReport + Break
            assert_eq!(else_branch.len(), 2); // LocationReport + Break
        } else {
            panic!("Expected IfCondition");
        }
    }
}
