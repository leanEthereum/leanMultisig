//! SSA (Static Single Assignment) analysis utilities.

use crate::lang::{Line, Expression, Boolean, Var};
use super::visitors::{Visitor, VisitorResult};
use std::collections::{HashMap, HashSet};

/// Tracks variable assignments to detect SSA violations
pub struct SSAAnalyzer {
    /// Variables that have been assigned to
    pub assigned_vars: HashMap<Var, usize>,
    /// Variables with multiple assignments (SSA violations)
    pub violations: HashSet<Var>,
}

impl SSAAnalyzer {
    pub fn new() -> Self {
        Self {
            assigned_vars: HashMap::new(),
            violations: HashSet::new(),
        }
    }

    pub fn analyze(lines: &[Line]) -> Self {
        let mut analyzer = Self::new();
        for line in lines {
            let _: VisitorResult<()> = analyzer.visit_line(line);
        }
        analyzer
    }

    pub fn has_violations(&self) -> bool {
        !self.violations.is_empty()
    }

    fn record_assignment(&mut self, var: &Var) {
        let count = self.assigned_vars.entry(var.clone()).or_insert(0);
        *count += 1;

        if *count > 1 {
            self.violations.insert(var.clone());
        }
    }
}

impl Default for SSAAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Visitor<T> for SSAAnalyzer {
    fn visit_line(&mut self, line: &Line) -> VisitorResult<T> {
        match line {
            Line::Assignment { var, .. } => {
                self.record_assignment(var);
            }
            Line::ArrayAssign { .. } => {
                // Array assignments don't violate SSA for scalar variables
            }
            Line::MAlloc { var, .. } => {
                self.record_assignment(var);
            }
            Line::DecomposeBits { var, .. } => {
                self.record_assignment(var);
            }
            Line::CounterHint { var } => {
                self.record_assignment(var);
            }
            Line::FunctionCall { return_data, .. } => {
                for var in return_data {
                    self.record_assignment(var);
                }
            }
            _ => {}
        }

        // Continue walking to analyze nested structures
        super::visitors::walk_line(self, line)
    }
}

/// Context for tracking return assignments across different execution paths
#[derive(Debug, Clone)]
pub struct ReturnContext {
    /// Conditions that must be true for this return to execute
    pub conditions: Vec<Boolean>,
    /// Variable assignments in this return context
    pub assignments: Vec<(Var, Expression)>,
}

impl ReturnContext {
    pub fn new() -> Self {
        Self {
            conditions: Vec::new(),
            assignments: Vec::new(),
        }
    }

    pub fn with_condition(mut self, condition: Boolean) -> Self {
        self.conditions.push(condition);
        self
    }

    pub fn with_assignment(mut self, var: Var, expr: Expression) -> Self {
        self.assignments.push((var, expr));
        self
    }
}

impl Default for ReturnContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Collects all return contexts from a function body
pub struct ReturnContextCollector {
    pub contexts: Vec<ReturnContext>,
}

impl ReturnContextCollector {
    pub fn new() -> Self {
        Self {
            contexts: Vec::new(),
        }
    }

    pub fn collect_from(lines: &[Line], return_vars: &[Var]) -> Vec<ReturnContext> {
        let mut collector = Self::new();
        collector.collect_recursive(lines, return_vars, Vec::new());
        collector.contexts
    }

    fn collect_recursive(&mut self, lines: &[Line], return_vars: &[Var], current_conditions: Vec<Boolean>) {
        for line in lines {
            match line {
                Line::Assignment { var, value } if return_vars.contains(var) => {
                    let context = ReturnContext {
                        conditions: current_conditions.clone(),
                        assignments: vec![(var.clone(), value.clone())],
                    };
                    self.contexts.push(context);
                }
                Line::IfCondition { condition, then_branch, else_branch } => {
                    // Collect from then branch with added condition
                    let mut then_conditions = current_conditions.clone();
                    then_conditions.push(condition.clone());
                    self.collect_recursive(then_branch, return_vars, then_conditions);

                    // Collect from else branch with negated condition
                    if !else_branch.is_empty() {
                        let negated_condition = match condition {
                            Boolean::Equal { left, right } => Boolean::Different {
                                left: left.clone(),
                                right: right.clone(),
                            },
                            Boolean::Different { left, right } => Boolean::Equal {
                                left: left.clone(),
                                right: right.clone(),
                            },
                        };
                        let mut else_conditions = current_conditions.clone();
                        else_conditions.push(negated_condition);
                        self.collect_recursive(else_branch, return_vars, else_conditions);
                    }
                }
                Line::ForLoop { body, .. } => {
                    // For simplicity, treat loop body as unconditional context
                    self.collect_recursive(body, return_vars, current_conditions.clone());
                }
                Line::Match { arms, .. } => {
                    for (_, arm_lines) in arms {
                        self.collect_recursive(arm_lines, return_vars, current_conditions.clone());
                    }
                }
                _ => {}
            }
        }
    }
}

impl Default for ReturnContextCollector {
    fn default() -> Self {
        Self::new()
    }
}

/// Detects potential SSA violations in return patterns
pub fn detect_return_ssa_violations(lines: &[Line], return_vars: &[Var]) -> bool {
    let contexts = ReturnContextCollector::collect_from(lines, return_vars);

    // If we have multiple contexts that could assign to the same variable,
    // we have a potential SSA violation
    if contexts.len() <= 1 {
        return false;
    }

    // Check if any return variable is assigned in multiple contexts
    for return_var in return_vars {
        let contexts_with_var = contexts
            .iter()
            .filter(|ctx| ctx.assignments.iter().any(|(var, _)| var == return_var))
            .count();

        if contexts_with_var > 1 {
            return true;
        }
    }

    false
}

/// Creates a simple SSA repair strategy by restructuring control flow
pub fn create_ssa_repair_strategy(contexts: &[ReturnContext]) -> Vec<Line> {
    if contexts.is_empty() {
        return Vec::new();
    }

    // For now, implement a simple strategy: use the first context
    // In a complete implementation, we'd build proper if-else chains
    let first_context = &contexts[0];

    let mut result = Vec::new();
    for (var, expr) in &first_context.assignments {
        result.push(Line::Assignment {
            var: var.clone(),
            value: expr.clone(),
        });
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::{SimpleExpr, ConstExpression};

    #[test]
    fn test_ssa_analyzer_no_violations() {
        let lines = vec![
            Line::Assignment {
                var: "x".to_string(),
                value: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(1))),
            },
            Line::Assignment {
                var: "y".to_string(),
                value: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(2))),
            },
        ];

        let analyzer = SSAAnalyzer::analyze(&lines);
        assert!(!analyzer.has_violations());
    }

    #[test]
    fn test_ssa_analyzer_with_violations() {
        let lines = vec![
            Line::Assignment {
                var: "x".to_string(),
                value: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(1))),
            },
            Line::Assignment {
                var: "x".to_string(),
                value: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(2))),
            },
        ];

        let analyzer = SSAAnalyzer::analyze(&lines);
        assert!(analyzer.has_violations());
        assert!(analyzer.violations.contains("x"));
    }

    #[test]
    fn test_return_context_collection() {
        let lines = vec![
            Line::Assignment {
                var: "result".to_string(),
                value: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(42))),
            },
        ];

        let return_vars = vec!["result".to_string()];
        let contexts = ReturnContextCollector::collect_from(&lines, &return_vars);

        assert_eq!(contexts.len(), 1);
        assert_eq!(contexts[0].assignments.len(), 1);
        assert_eq!(contexts[0].assignments[0].0, "result");
    }

    #[test]
    fn test_detect_return_ssa_violations() {
        let lines = vec![
            Line::IfCondition {
                condition: Boolean::Equal {
                    left: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(1))),
                    right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(1))),
                },
                then_branch: vec![
                    Line::Assignment {
                        var: "result".to_string(),
                        value: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(100))),
                    }
                ],
                else_branch: vec![],
            },
            Line::Assignment {
                var: "result".to_string(),
                value: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(200))),
            },
        ];

        let return_vars = vec!["result".to_string()];
        assert!(detect_return_ssa_violations(&lines, &return_vars));
    }
}