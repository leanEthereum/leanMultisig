use lean_vm::{Boolean, BooleanExpr};

use super::expression::{ExpressionParser, VecElementParser, VecLiteralParser};
use super::function::{AssignmentParser, TupleExpressionParser};
use super::literal::ConstExprParser;
use super::{Parse, ParseContext, next_inner_pair};
use crate::{
    SourceLineNumber,
    lang::{Condition, Expression, Line, SourceLocation, VecLiteral},
    parser::{
        error::{ParseResult, SemanticError},
        grammar::{ParsePair, Rule},
    },
};

/// Parser for all statement types.
pub struct StatementParser;

impl Parse<Line> for StatementParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let inner = next_inner_pair(&mut pair.into_inner(), "statement body")?;

        match inner.as_rule() {
            Rule::forward_declaration => ForwardDeclarationParser.parse(inner, ctx),
            Rule::assignment => AssignmentParser.parse(inner, ctx),
            Rule::if_statement => IfStatementParser.parse(inner, ctx),
            Rule::for_statement => ForStatementParser.parse(inner, ctx),
            Rule::match_statement => MatchStatementParser.parse(inner, ctx),
            Rule::return_statement => ReturnStatementParser.parse(inner, ctx),
            Rule::assert_statement => AssertParser::<false>.parse(inner, ctx),
            Rule::debug_assert_statement => AssertParser::<true>.parse(inner, ctx),
            Rule::vec_declaration => VecDeclarationParser.parse(inner, ctx),
            Rule::push_statement => PushStatementParser.parse(inner, ctx),
            _ => Err(SemanticError::new("Unknown statement").into()),
        }
    }
}

/// Parser for forward declarations of variables.
pub struct ForwardDeclarationParser;

impl Parse<Line> for ForwardDeclarationParser {
    fn parse(&self, pair: ParsePair<'_>, _ctx: &mut ParseContext) -> ParseResult<Line> {
        let mut inner = pair.into_inner();
        let var = next_inner_pair(&mut inner, "variable name")?.as_str().to_string();
        Ok(Line::ForwardDeclaration { var })
    }
}

/// Parser for if-else conditional statements.
pub struct IfStatementParser;

impl Parse<Line> for IfStatementParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let line_number = pair.line_col().0;
        let mut inner = pair.into_inner();
        let condition = ConditionParser.parse(next_inner_pair(&mut inner, "if condition")?, ctx)?;

        let mut then_branch: Vec<Line> = Vec::new();
        let mut else_if_branches: Vec<(Condition, Vec<Line>, SourceLineNumber)> = Vec::new();
        let mut else_branch: Vec<Line> = Vec::new();

        for item in inner {
            match item.as_rule() {
                Rule::statement => {
                    Self::add_statement_with_location(&mut then_branch, item, ctx)?;
                }
                Rule::else_if_clause => {
                    let line_number = item.line_col().0;
                    let mut inner = item.into_inner();
                    let else_if_condition =
                        ConditionParser.parse(next_inner_pair(&mut inner, "else if condition")?, ctx)?;
                    let mut else_if_branch = Vec::new();
                    for else_if_item in inner {
                        Self::add_statement_with_location(&mut else_if_branch, else_if_item, ctx)?;
                    }
                    else_if_branches.push((else_if_condition, else_if_branch, line_number));
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

        let mut outer_else_branch = Vec::new();
        let mut inner_else_branch = &mut outer_else_branch;

        for (else_if_condition, else_if_branch, line_number) in else_if_branches.into_iter() {
            inner_else_branch.push(Line::IfCondition {
                condition: else_if_condition,
                then_branch: else_if_branch,
                else_branch: Vec::new(),
                location: SourceLocation {
                    file_id: ctx.current_file_id,
                    line_number,
                },
            });
            inner_else_branch = match &mut inner_else_branch[0] {
                Line::IfCondition { else_branch, .. } => else_branch,
                _ => unreachable!("Expected Line::IfCondition"),
            };
        }

        inner_else_branch.extend(else_branch);

        Ok(Line::IfCondition {
            condition,
            then_branch,
            else_branch: outer_else_branch,
            location: SourceLocation {
                file_id: ctx.current_file_id,
                line_number,
            },
        })
    }
}

impl IfStatementParser {
    fn add_statement_with_location(
        lines: &mut Vec<Line>,
        pair: ParsePair<'_>,
        ctx: &mut ParseContext,
    ) -> ParseResult<()> {
        let line_number = pair.line_col().0;
        let line = StatementParser.parse(pair, ctx)?;

        lines.push(Line::LocationReport {
            location: SourceLocation {
                file_id: ctx.current_file_id,
                line_number,
            },
        });
        lines.push(line);

        Ok(())
    }
}

/// Parser for conditions.
pub struct ConditionParser;

impl Parse<Condition> for ConditionParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Condition> {
        let inner_pair = next_inner_pair(&mut pair.into_inner(), "inner expression")?;
        match inner_pair.as_rule() {
            Rule::assumed_bool_expr => ExpressionParser
                .parse(next_inner_pair(&mut inner_pair.into_inner(), "inner expression")?, ctx)
                .map(Condition::AssumeBoolean),
            Rule::comparison => {
                let boolean = ComparisonParser::parse(inner_pair, ctx)?;
                Ok(Condition::Comparison(boolean))
            }
            _ => Err(SemanticError::new("Invalid condition").into()),
        }
    }
}

/// Parser for comparison expressions (shared between conditions and assertions).
pub struct ComparisonParser;

impl ComparisonParser {
    pub fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<BooleanExpr<Expression>> {
        let mut inner = pair.into_inner();
        let left = ExpressionParser.parse(next_inner_pair(&mut inner, "left side")?, ctx)?;
        let op = next_inner_pair(&mut inner, "comparison operator")?;
        let right = ExpressionParser.parse(next_inner_pair(&mut inner, "right side")?, ctx)?;

        let kind = match op.as_str() {
            "==" => Boolean::Equal,
            "!=" => Boolean::Different,
            "<" => Boolean::LessThan,
            _ => unreachable!(),
        };

        Ok(BooleanExpr { left, right, kind })
    }
}

/// Parser for for-loop statements.
pub struct ForStatementParser;

impl Parse<Line> for ForStatementParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let line_number = pair.line_col().0;
        let mut inner = pair.into_inner();
        let iterator = next_inner_pair(&mut inner, "loop iterator")?.as_str().to_string();

        let start = ExpressionParser.parse(next_inner_pair(&mut inner, "loop start")?, ctx)?;
        let end = ExpressionParser.parse(next_inner_pair(&mut inner, "loop end")?, ctx)?;

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
            unroll,
            location: SourceLocation {
                file_id: ctx.current_file_id,
                line_number,
            },
        })
    }
}

impl ForStatementParser {
    fn add_statement_with_location(
        lines: &mut Vec<Line>,
        pair: ParsePair<'_>,
        ctx: &mut ParseContext,
    ) -> ParseResult<()> {
        let line_number = pair.line_col().0;
        let line = StatementParser.parse(pair, ctx)?;

        lines.push(Line::LocationReport {
            location: SourceLocation {
                file_id: ctx.current_file_id,
                line_number,
            },
        });
        lines.push(line);

        Ok(())
    }
}

/// Parser for match statements with pattern matching.
pub struct MatchStatementParser;

impl Parse<Line> for MatchStatementParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let line_number = pair.line_col().0;
        let mut inner = pair.into_inner();
        let value = ExpressionParser.parse(next_inner_pair(&mut inner, "match value")?, ctx)?;

        let mut arms = Vec::new();

        for arm_pair in inner {
            if arm_pair.as_rule() == Rule::match_arm {
                let mut arm_inner = arm_pair.into_inner();
                let const_expr = next_inner_pair(&mut arm_inner, "match pattern")?;
                let pattern = ConstExprParser.parse(const_expr, ctx)?;

                let mut statements = Vec::new();
                for stmt in arm_inner {
                    if stmt.as_rule() == Rule::statement {
                        Self::add_statement_with_location(&mut statements, stmt, ctx)?;
                    }
                }

                arms.push((pattern, statements));
            }
        }
        let location = SourceLocation {
            file_id: ctx.current_file_id,
            line_number,
        };
        Ok(Line::Match { value, arms, location })
    }
}

impl MatchStatementParser {
    fn add_statement_with_location(
        lines: &mut Vec<Line>,
        pair: ParsePair<'_>,
        ctx: &mut ParseContext,
    ) -> ParseResult<()> {
        let line_number = pair.line_col().0;
        let line = StatementParser.parse(pair, ctx)?;

        lines.push(Line::LocationReport {
            location: SourceLocation {
                file_id: ctx.current_file_id,
                line_number,
            },
        });
        lines.push(line);

        Ok(())
    }
}

/// Parser for return statements.
pub struct ReturnStatementParser;

impl Parse<Line> for ReturnStatementParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let mut return_data = Vec::new();

        for item in pair.into_inner() {
            if item.as_rule() == Rule::tuple_expression {
                return_data = TupleExpressionParser.parse(item, ctx)?;
            }
        }

        Ok(Line::FunctionRet { return_data })
    }
}

/// Parser for assert statements.
pub struct AssertParser<const DEBUG: bool>;

impl<const DEBUG: bool> Parse<Line> for AssertParser<DEBUG> {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let line_number = pair.line_col().0;
        let comparison = next_inner_pair(&mut pair.into_inner(), "comparison")?;
        let boolean = ComparisonParser::parse(comparison, ctx)?;

        Ok(Line::Assert {
            debug: DEBUG,
            boolean,
            location: SourceLocation {
                file_id: ctx.current_file_id,
                line_number,
            },
        })
    }
}

/// Parser for vector declarations: `var = vec![...]` (vectors are implicitly mutable for push)
pub struct VecDeclarationParser;

impl Parse<Line> for VecDeclarationParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let line_number = pair.line_col().0;
        let mut inner = pair.into_inner();

        // Parse variable name
        let var = next_inner_pair(&mut inner, "variable name")?.as_str().to_string();

        // Parse the vec_literal
        let vec_literal_pair = next_inner_pair(&mut inner, "vec literal")?;
        let vec_literal = VecLiteralParser.parse(vec_literal_pair, ctx)?;

        // Extract elements from the VecLiteral::Vec
        let elements = match vec_literal {
            VecLiteral::Vec(elems) => elems,
            VecLiteral::Expr(_) => {
                return Err(SemanticError::new("Expected vec literal, got expression").into());
            }
        };

        Ok(Line::VecDeclaration {
            var,
            elements,
            location: SourceLocation {
                file_id: ctx.current_file_id,
                line_number,
            },
        })
    }
}

/// Parser for push statements: `push(vec_var, element);` or `push(vec_var[i][j], element);`
pub struct PushStatementParser;

impl Parse<Line> for PushStatementParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let line_number = pair.line_col().0;
        let mut inner = pair.into_inner();

        // Parse the push_target (identifier with optional indices)
        let push_target = next_inner_pair(&mut inner, "push target")?;
        let mut target_inner = push_target.into_inner();

        // First element is the vector variable name
        let vector = next_inner_pair(&mut target_inner, "vector variable")?
            .as_str()
            .to_string();

        // Remaining elements are index expressions
        let indices: Vec<Expression> = target_inner
            .map(|idx_pair| ExpressionParser.parse(idx_pair, ctx))
            .collect::<Result<Vec<_>, _>>()?;

        // Parse the element to push (vec_element can be vec_literal or expression)
        let element_pair = next_inner_pair(&mut inner, "push element")?;
        let element = VecElementParser.parse(element_pair, ctx)?;

        Ok(Line::Push {
            vector,
            indices,
            element,
            location: SourceLocation {
                file_id: ctx.current_file_id,
                line_number,
            },
        })
    }
}
