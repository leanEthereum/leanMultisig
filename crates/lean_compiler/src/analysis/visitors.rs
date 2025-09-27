//! Visitor traits for AST traversal.

use crate::lang::{Boolean, Expression, Function, Line, Program, SimpleExpr};
use std::ops::ControlFlow;

/// Result type for visitor operations
pub type VisitorResult<T> = ControlFlow<T, ()>;

/// Immutable visitor trait for read-only AST traversal
pub trait Visitor<T = ()> {
    fn visit_program(&mut self, program: &Program) -> VisitorResult<T> {
        walk_program(self, program)
    }

    fn visit_function(&mut self, function: &Function) -> VisitorResult<T> {
        walk_function(self, function)
    }

    fn visit_line(&mut self, line: &Line) -> VisitorResult<T> {
        walk_line(self, line)
    }

    fn visit_expression(&mut self, expr: &Expression) -> VisitorResult<T> {
        walk_expression(self, expr)
    }

    fn visit_simple_expr(&mut self, simple_expr: &SimpleExpr) -> VisitorResult<T> {
        walk_simple_expr(self, simple_expr)
    }

    fn visit_boolean(&mut self, condition: &Boolean) -> VisitorResult<T> {
        walk_boolean(self, condition)
    }
}

/// Mutable visitor trait for AST transformations
pub trait MutVisitor<T = ()> {
    fn visit_program(&mut self, program: &mut Program) -> VisitorResult<T> {
        walk_program_mut(self, program)
    }

    fn visit_function(&mut self, function: &mut Function) -> VisitorResult<T> {
        walk_function_mut(self, function)
    }

    fn visit_line(&mut self, line: &mut Line) -> VisitorResult<T> {
        walk_line_mut(self, line)
    }

    fn visit_expression(&mut self, expr: &mut Expression) -> VisitorResult<T> {
        walk_expression_mut(self, expr)
    }

    fn visit_simple_expr(&mut self, simple_expr: &mut SimpleExpr) -> VisitorResult<T> {
        walk_simple_expr_mut(self, simple_expr)
    }

    fn visit_boolean(&mut self, condition: &mut Boolean) -> VisitorResult<T> {
        walk_boolean_mut(self, condition)
    }
}

// Immutable walking functions (now generic)
pub fn walk_program<V, T>(visitor: &mut V, program: &Program) -> VisitorResult<T>
where
    V: Visitor<T> + ?Sized,
{
    for function in program.functions.values() {
        visitor.visit_function(function)?;
    }
    ControlFlow::Continue(())
}

pub fn walk_function<V, T>(visitor: &mut V, function: &Function) -> VisitorResult<T>
where
    V: Visitor<T> + ?Sized,
{
    for line in &function.body {
        visitor.visit_line(line)?;
    }
    ControlFlow::Continue(())
}

pub fn walk_line<V, T>(visitor: &mut V, line: &Line) -> VisitorResult<T>
where
    V: Visitor<T> + ?Sized,
{
    match line {
        Line::Match { value, arms } => {
            visitor.visit_expression(value)?;
            for (_, arm_lines) in arms {
                for arm_line in arm_lines {
                    visitor.visit_line(arm_line)?;
                }
            }
        }
        Line::Assignment { value, .. } => {
            visitor.visit_expression(value)?;
        }
        Line::ArrayAssign {
            array,
            index,
            value,
        } => {
            visitor.visit_simple_expr(array)?;
            visitor.visit_expression(index)?;
            visitor.visit_expression(value)?;
        }
        Line::Assert(condition) => {
            visitor.visit_boolean(condition)?;
        }
        Line::IfCondition {
            condition,
            then_branch,
            else_branch,
        } => {
            visitor.visit_boolean(condition)?;
            for line in then_branch {
                visitor.visit_line(line)?;
            }
            for line in else_branch {
                visitor.visit_line(line)?;
            }
        }
        Line::ForLoop {
            start, end, body, ..
        } => {
            visitor.visit_expression(start)?;
            visitor.visit_expression(end)?;
            for line in body {
                visitor.visit_line(line)?;
            }
        }
        Line::FunctionCall { args, .. } => {
            for arg in args {
                visitor.visit_expression(arg)?;
            }
        }
        Line::FunctionRet { return_data } => {
            for expr in return_data {
                visitor.visit_expression(expr)?;
            }
        }
        Line::Precompile { args, .. } => {
            for arg in args {
                visitor.visit_expression(arg)?;
            }
        }
        Line::Print { content, .. } => {
            for expr in content {
                visitor.visit_expression(expr)?;
            }
        }
        Line::MAlloc {
            size,
            vectorized_len,
            ..
        } => {
            visitor.visit_expression(size)?;
            visitor.visit_expression(vectorized_len)?;
        }
        Line::DecomposeBits { to_decompose, .. } => {
            for expr in to_decompose {
                visitor.visit_expression(expr)?;
            }
        }
        Line::Break | Line::Panic | Line::CounterHint { .. } | Line::LocationReport { .. } => {}
    }
    ControlFlow::Continue(())
}

pub fn walk_expression<V, T>(visitor: &mut V, expr: &Expression) -> VisitorResult<T>
where
    V: Visitor<T> + ?Sized,
{
    match expr {
        Expression::Value(simple_expr) => visitor.visit_simple_expr(simple_expr)?,
        Expression::ArrayAccess { array, index } => {
            visitor.visit_simple_expr(array)?;
            visitor.visit_expression(index)?;
        }
        Expression::Binary { left, right, .. } => {
            visitor.visit_expression(left)?;
            visitor.visit_expression(right)?;
        }
        Expression::Log2Ceil { value } => {
            visitor.visit_expression(value)?;
        }
    }
    ControlFlow::Continue(())
}

pub fn walk_simple_expr<V, T>(_visitor: &mut V, _simple_expr: &SimpleExpr) -> VisitorResult<T>
where
    V: Visitor<T> + ?Sized,
{
    // SimpleExpr is leaf-level, no further traversal needed
    ControlFlow::Continue(())
}

pub fn walk_boolean<V, T>(visitor: &mut V, condition: &Boolean) -> VisitorResult<T>
where
    V: Visitor<T> + ?Sized,
{
    match condition {
        Boolean::Equal { left, right } | Boolean::Different { left, right } => {
            visitor.visit_expression(left)?;
            visitor.visit_expression(right)?;
        }
    }
    ControlFlow::Continue(())
}

// Mutable walking functions (now generic)
pub fn walk_program_mut<V, T>(visitor: &mut V, program: &mut Program) -> VisitorResult<T>
where
    V: MutVisitor<T> + ?Sized,
{
    for function in program.functions.values_mut() {
        visitor.visit_function(function)?;
    }
    ControlFlow::Continue(())
}

pub fn walk_function_mut<V, T>(visitor: &mut V, function: &mut Function) -> VisitorResult<T>
where
    V: MutVisitor<T> + ?Sized,
{
    for line in &mut function.body {
        visitor.visit_line(line)?;
    }
    ControlFlow::Continue(())
}

pub fn walk_line_mut<V, T>(visitor: &mut V, line: &mut Line) -> VisitorResult<T>
where
    V: MutVisitor<T> + ?Sized,
{
    match line {
        Line::Match { value, arms } => {
            visitor.visit_expression(value)?;
            for (_, arm_lines) in arms {
                for arm_line in arm_lines {
                    visitor.visit_line(arm_line)?;
                }
            }
        }
        Line::Assignment { value, .. } => {
            visitor.visit_expression(value)?;
        }
        Line::ArrayAssign {
            array,
            index,
            value,
        } => {
            visitor.visit_simple_expr(array)?;
            visitor.visit_expression(index)?;
            visitor.visit_expression(value)?;
        }
        Line::Assert(condition) => {
            visitor.visit_boolean(condition)?;
        }
        Line::IfCondition {
            condition,
            then_branch,
            else_branch,
        } => {
            visitor.visit_boolean(condition)?;
            for line in then_branch {
                visitor.visit_line(line)?;
            }
            for line in else_branch {
                visitor.visit_line(line)?;
            }
        }
        Line::ForLoop {
            start, end, body, ..
        } => {
            visitor.visit_expression(start)?;
            visitor.visit_expression(end)?;
            for line in body {
                visitor.visit_line(line)?;
            }
        }
        Line::FunctionCall { args, .. } => {
            for arg in args {
                visitor.visit_expression(arg)?;
            }
        }
        Line::FunctionRet { return_data } => {
            for expr in return_data {
                visitor.visit_expression(expr)?;
            }
        }
        Line::Precompile { args, .. } => {
            for arg in args {
                visitor.visit_expression(arg)?;
            }
        }
        Line::Print { content, .. } => {
            for expr in content {
                visitor.visit_expression(expr)?;
            }
        }
        Line::MAlloc {
            size,
            vectorized_len,
            ..
        } => {
            visitor.visit_expression(size)?;
            visitor.visit_expression(vectorized_len)?;
        }
        Line::DecomposeBits { to_decompose, .. } => {
            for expr in to_decompose {
                visitor.visit_expression(expr)?;
            }
        }
        Line::Break | Line::Panic | Line::CounterHint { .. } | Line::LocationReport { .. } => {}
    }
    ControlFlow::Continue(())
}

pub fn walk_expression_mut<V, T>(visitor: &mut V, expr: &mut Expression) -> VisitorResult<T>
where
    V: MutVisitor<T> + ?Sized,
{
    match expr {
        Expression::Value(simple_expr) => visitor.visit_simple_expr(simple_expr)?,
        Expression::ArrayAccess { array, index } => {
            visitor.visit_simple_expr(array)?;
            visitor.visit_expression(index)?;
        }
        Expression::Binary { left, right, .. } => {
            visitor.visit_expression(left)?;
            visitor.visit_expression(right)?;
        }
        Expression::Log2Ceil { value } => {
            visitor.visit_expression(value)?;
        }
    }
    ControlFlow::Continue(())
}

pub fn walk_simple_expr_mut<V, T>(
    _visitor: &mut V,
    _simple_expr: &mut SimpleExpr,
) -> VisitorResult<T>
where
    V: MutVisitor<T> + ?Sized,
{
    // SimpleExpr is leaf-level, no further traversal needed
    ControlFlow::Continue(())
}

pub fn walk_boolean_mut<V, T>(visitor: &mut V, condition: &mut Boolean) -> VisitorResult<T>
where
    V: MutVisitor<T> + ?Sized,
{
    match condition {
        Boolean::Equal { left, right } | Boolean::Different { left, right } => {
            visitor.visit_expression(left)?;
            visitor.visit_expression(right)?;
        }
    }
    ControlFlow::Continue(())
}

/// Utility for collecting items during traversal
pub struct Collector<T> {
    pub items: Vec<T>,
}

impl<T> Collector<T> {
    pub fn new() -> Self {
        Self { items: Vec::new() }
    }

    pub fn collect(mut self, item: T) -> Self {
        self.items.push(item);
        self
    }
}

impl<T> Default for Collector<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// Utility for finding specific patterns
pub struct PatternFinder<F, T> {
    pub predicate: F,
    pub found: Option<T>,
}

impl<F, T> PatternFinder<F, T>
where
    F: Fn(&T) -> bool,
{
    pub fn new(predicate: F) -> Self {
        Self {
            predicate,
            found: None,
        }
    }
}
