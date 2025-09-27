//! Control flow analysis utilities.

use super::visitors::{Visitor, VisitorResult};
use crate::lang::Line;
use std::ops::ControlFlow;

/// Analyzes control flow patterns in a function body
pub struct ControlFlowAnalyzer {
    pub has_returns: bool,
    pub return_count: usize,
    pub has_nested_returns: bool,
    pub has_non_exhaustive_conditions: bool,
}

impl ControlFlowAnalyzer {
    pub fn new() -> Self {
        Self {
            has_returns: false,
            return_count: 0,
            has_nested_returns: false,
            has_non_exhaustive_conditions: false,
        }
    }

    pub fn analyze(lines: &[Line]) -> Self {
        let mut analyzer = Self::new();
        for line in lines {
            let _: VisitorResult<()> = analyzer.visit_line(line);
        }
        analyzer
    }

    /// Check if this pattern needs SSA violation repair
    pub fn needs_ssa_repair(&self) -> bool {
        self.has_non_exhaustive_conditions && self.return_count > 1
    }

    fn analyze_line_depth(&mut self, line: &Line, depth: usize) {
        match line {
            Line::FunctionRet(_) => {
                self.has_returns = true;
                self.return_count += 1;
                if depth > 0 {
                    self.has_nested_returns = true;
                }
            }
            Line::IfCondition(if_cond) => {
                let then_branch = &if_cond.then_branch;
                let else_branch = &if_cond.else_branch;
                // Non-exhaustive if else_branch is empty
                if else_branch.is_empty() && !then_branch.is_empty() {
                    self.has_non_exhaustive_conditions = true;
                }

                for line in then_branch {
                    self.analyze_line_depth(line, depth + 1);
                }
                for line in else_branch {
                    self.analyze_line_depth(line, depth + 1);
                }
            }
            Line::ForLoop(for_loop) => {
                for line in &for_loop.body {
                    self.analyze_line_depth(line, depth + 1);
                }
            }
            Line::Match(match_stmt) => {
                for (_, arm_lines) in &match_stmt.arms {
                    for line in arm_lines {
                        self.analyze_line_depth(line, depth + 1);
                    }
                }
            }
            _ => {}
        }
    }
}

impl Default for ControlFlowAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Visitor<T> for ControlFlowAnalyzer {
    fn visit_line(&mut self, line: &Line) -> VisitorResult<T> {
        self.analyze_line_depth(line, 0);
        ControlFlow::Continue(())
    }
}

/// Collects all return statements in a function
pub struct ReturnCollector {
    pub returns: Vec<Line>,
}

impl ReturnCollector {
    pub fn new() -> Self {
        Self {
            returns: Vec::new(),
        }
    }

    pub fn collect_from(lines: &[Line]) -> Vec<Line> {
        let mut collector = Self::new();
        for line in lines {
            let _: VisitorResult<()> = collector.visit_line(line);
        }
        collector.returns
    }
}

impl Default for ReturnCollector {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Visitor<T> for ReturnCollector {
    fn visit_line(&mut self, line: &Line) -> VisitorResult<T> {
        if let Line::FunctionRet(_) = line {
            self.returns.push(line.clone());
        }
        // Continue walking to find nested returns
        super::visitors::walk_line(self, line)
    }
}

/// Checks if a branch contains any return statements
pub fn has_return_in_branch(lines: &[Line]) -> bool {
    !ReturnCollector::collect_from(lines).is_empty()
}

/// Checks for specific SSA violation patterns
pub fn has_ssa_violation_pattern(lines: &[Line]) -> bool {
    let analysis = ControlFlowAnalyzer::analyze(lines);
    analysis.needs_ssa_repair()
}

/// Finds all non-exhaustive if conditions that contain returns
pub fn find_non_exhaustive_if_with_returns(lines: &[Line]) -> Vec<&Line> {
    let mut found = Vec::new();
    for line in lines {
        if let Line::IfCondition(if_cond) = line
            && if_cond.else_branch.is_empty()
            && has_return_in_branch(&if_cond.then_branch)
        {
            found.push(line);
        }
    }
    found
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::{Boolean, ConstExpression, Expression, SimpleExpr};

    #[test]
    fn test_control_flow_analyzer_simple() {
        let lines = vec![Line::FunctionRet(
            crate::lang::ast::statement::FunctionRet {
                return_data: vec![Expression::Value(SimpleExpr::Constant(
                    ConstExpression::scalar(42),
                ))],
            },
        )];

        let analysis = ControlFlowAnalyzer::analyze(&lines);
        assert!(analysis.has_returns);
        assert_eq!(analysis.return_count, 1);
        assert!(!analysis.has_nested_returns);
    }

    #[test]
    fn test_control_flow_analyzer_nested() {
        let lines = vec![Line::IfCondition(
            crate::lang::ast::statement::IfCondition {
                condition: Boolean::Equal {
                    left: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(1))),
                    right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(1))),
                },
                then_branch: vec![Line::FunctionRet(
                    crate::lang::ast::statement::FunctionRet {
                        return_data: vec![Expression::Value(SimpleExpr::Constant(
                            ConstExpression::scalar(100),
                        ))],
                    },
                )],
                else_branch: vec![],
            },
        )];

        let analysis = ControlFlowAnalyzer::analyze(&lines);
        assert!(analysis.has_returns);
        assert!(analysis.has_nested_returns);
        assert!(analysis.has_non_exhaustive_conditions);
    }

    #[test]
    fn test_ssa_violation_detection() {
        let lines = vec![
            Line::IfCondition(crate::lang::ast::statement::IfCondition {
                condition: Boolean::Equal {
                    left: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(1))),
                    right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(1))),
                },
                then_branch: vec![Line::FunctionRet(
                    crate::lang::ast::statement::FunctionRet {
                        return_data: vec![Expression::Value(SimpleExpr::Constant(
                            ConstExpression::scalar(100),
                        ))],
                    },
                )],
                else_branch: vec![],
            }),
            Line::FunctionRet(crate::lang::ast::statement::FunctionRet {
                return_data: vec![Expression::Value(SimpleExpr::Constant(
                    ConstExpression::scalar(200),
                ))],
            }),
        ];

        assert!(has_ssa_violation_pattern(&lines));
    }
}
