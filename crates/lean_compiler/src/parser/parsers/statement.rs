use lean_vm::{Boolean, BooleanExpr};
use utils::ToUsize;

use super::expression::{ExpressionParser, VecElementParser, VecLiteralParser};
use super::function::{AssignmentParser, TupleExpressionParser};
use super::literal::ConstExprParser;
use super::{Parse, ParseContext, next_inner_pair};
use crate::{
    SourceLineNumber,
    lang::{Condition, Expression, Line, LoopKind, SourceLocation, VecLiteral},
    parser::{
        error::{ParseResult, SemanticError},
        grammar::{ParsePair, Rule},
    },
};

/// Parser for all statement types.
pub struct StatementParser;

impl Parse<Line> for StatementParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let mut inner_iter = pair.into_inner();
        let inner = next_inner_pair(&mut inner_iter, "statement body")?;

        match inner.as_rule() {
            // Compound statements (have their own block structure)
            Rule::if_statement => IfStatementParser.parse(inner, ctx),
            Rule::for_statement => ForStatementParser.parse(inner, ctx),
            Rule::match_statement => MatchStatementParser.parse(inner, ctx),
            // Simple statements (wrapped in simple_statement rule)
            Rule::simple_statement => {
                let simple_inner = next_inner_pair(&mut inner.into_inner(), "simple statement body")?;
                match simple_inner.as_rule() {
                    Rule::forward_declaration => ForwardDeclarationParser.parse(simple_inner, ctx),
                    Rule::assignment => AssignmentParser.parse(simple_inner, ctx),
                    Rule::return_statement => ReturnStatementParser.parse(simple_inner, ctx),
                    Rule::assert_statement => AssertParser::<false>.parse(simple_inner, ctx),
                    Rule::debug_assert_statement => AssertParser::<true>.parse(simple_inner, ctx),
                    Rule::vec_declaration => VecDeclarationParser.parse(simple_inner, ctx),
                    Rule::push_statement => PushStatementParser.parse(simple_inner, ctx),
                    Rule::pop_statement => PopStatementParser.parse(simple_inner, ctx),
                    _ => Err(SemanticError::new("Unknown simple statement").into()),
                }
            }
            _ => Err(SemanticError::new("Unknown statement").into()),
        }
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
        let mut elif_branches: Vec<(Condition, Vec<Line>, SourceLineNumber)> = Vec::new();
        let mut else_branch: Vec<Line> = Vec::new();

        for item in inner {
            match item.as_rule() {
                Rule::statement => {
                    Self::add_statement_with_location(&mut then_branch, item, ctx)?;
                }
                Rule::elif_clause => {
                    let line_number = item.line_col().0;
                    let mut inner = item.into_inner();
                    let elif_condition = ConditionParser.parse(next_inner_pair(&mut inner, "elif condition")?, ctx)?;
                    let mut elif_branch = Vec::new();
                    for elif_item in inner {
                        if elif_item.as_rule() == Rule::statement {
                            Self::add_statement_with_location(&mut elif_branch, elif_item, ctx)?;
                        }
                    }
                    elif_branches.push((elif_condition, elif_branch, line_number));
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

        for (elif_condition, elif_branch, line_number) in elif_branches.into_iter() {
            inner_else_branch.push(Line::IfCondition {
                condition: elif_condition,
                then_branch: elif_branch,
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
            "<=" => Boolean::LessOrEqual,
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

        let range_pair = next_inner_pair(&mut inner, "range expression")?;
        let rule = range_pair.as_rule();
        let mut range_inner = range_pair.into_inner();
        let start = ExpressionParser.parse(next_inner_pair(&mut range_inner, "loop start")?, ctx)?;
        let end = ExpressionParser.parse(next_inner_pair(&mut range_inner, "loop end")?, ctx)?;
        let loop_kind = match rule {
            Rule::unroll_range => LoopKind::Unroll,
            Rule::dynamic_unroll_range => {
                let n_bits = ExpressionParser.parse(next_inner_pair(&mut range_inner, "n_bits")?, ctx)?;
                LoopKind::DynamicUnroll { n_bits }
            }
            _ => LoopKind::Range,
        };

        let mut body = Vec::new();
        for item in inner {
            if item.as_rule() == Rule::statement {
                Self::add_statement_with_location(&mut body, item, ctx)?;
            }
        }

        Ok(Line::ForLoop {
            iterator,
            start,
            end,
            body,
            loop_kind,
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
                let pattern = ConstExprParser.parse(const_expr, ctx)?.to_usize();

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
        let mut inner = pair.into_inner();
        // Skip the assert_keyword / debug_assert_keyword
        let _ = next_inner_pair(&mut inner, "assert keyword")?;
        let next = next_inner_pair(&mut inner, "comparison or assert_false")?;

        match next.as_rule() {
            Rule::assert_false => {
                // assert False or assert False, "message"
                let mut false_inner = next.into_inner();
                let message = false_inner.next().map(|s| {
                    let text = s.as_str();
                    // Strip the quotes from the string literal
                    text[1..text.len() - 1].to_string()
                });
                Ok(Line::Panic { message })
            }
            Rule::comparison => {
                let boolean = ComparisonParser::parse(next, ctx)?;
                Ok(Line::Assert {
                    debug: DEBUG,
                    boolean,
                    location: SourceLocation {
                        file_id: ctx.current_file_id,
                        line_number,
                    },
                })
            }
            _ => Err(SemanticError::new("Expected comparison or False in assert statement").into()),
        }
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

/// Parser for push statements: `vec_var.push(element);` or `vec_var[i][j].push(element);`
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

/// Parser for pop statements: `vec_var.pop();` or `vec_var[i][j].pop();`
pub struct PopStatementParser;

impl Parse<Line> for PopStatementParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let line_number = pair.line_col().0;
        let mut inner = pair.into_inner();

        // Parse the pop_target (identifier with optional indices)
        let pop_target = next_inner_pair(&mut inner, "pop target")?;
        let mut target_inner = pop_target.into_inner();

        // First element is the vector variable name
        let vector = next_inner_pair(&mut target_inner, "vector variable")?
            .as_str()
            .to_string();

        // Remaining elements are index expressions
        let indices: Vec<Expression> = target_inner
            .map(|idx_pair| ExpressionParser.parse(idx_pair, ctx))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Line::Pop {
            vector,
            indices,
            location: SourceLocation {
                file_id: ctx.current_file_id,
                line_number,
            },
        })
    }
}

/// Parser for forward declarations: `x: Imu` or `x: Mut`
pub struct ForwardDeclarationParser;

impl Parse<Line> for ForwardDeclarationParser {
    fn parse(&self, pair: ParsePair<'_>, _ctx: &mut ParseContext) -> ParseResult<Line> {
        let mut inner = pair.into_inner();

        // Parse variable name
        let var = next_inner_pair(&mut inner, "variable name")?.as_str().to_string();

        // Check for : Mut or : Imu annotation
        let annotation = next_inner_pair(&mut inner, "type annotation")?;
        let is_mutable = annotation.as_rule() == Rule::mut_annotation;

        Ok(Line::ForwardDeclaration { var, is_mutable })
    }
}
