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
                    Self::add_statement_with_location(&mut then_branch, item, ctx)?;
                }
                Rule::else_clause => {
                    for else_item in item.into_inner() {
                        if else_item.as_rule() == Rule::statement {
                            Self::add_statement_with_location(&mut else_branch, else_item, ctx)?;
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

impl IfStatementParser {
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
}

/// Parser for for-loop statements.
pub struct ForStatementParser;

impl Parse<Line> for ForStatementParser {
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let mut inner = pair.into_inner();
        let iterator = next_inner_pair(&mut inner, "loop iterator")?
            .as_str()
            .to_string();

        // Check for optional reverse clause
        let mut rev = false;
        if let Some(next_peek) = inner.clone().next()
            && next_peek.as_rule() == Rule::rev_clause
        {
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
                    Self::add_statement_with_location(&mut body, item, ctx)?;
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

impl ForStatementParser {
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
                        Self::add_statement_with_location(&mut statements, stmt, ctx)?;
                    }
                }

                arms.push((pattern, statements));
            }
        }

        Ok(Line::Match { value, arms })
    }
}

impl MatchStatementParser {
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
