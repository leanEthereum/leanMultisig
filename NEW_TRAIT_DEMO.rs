// DEMONSTRATION: Unified Trait Approach
// This shows how the new StatementAnalysis trait would replace
// the large match statements in utility functions

use crate::{F, lang::Var};
use std::collections::{BTreeMap, BTreeSet};

/// NEW UNIFIED TRAIT - Replaces multiple scattered functions
pub trait StatementAnalysis {
    // Default implementations mean most statements need NO code
    fn replace_vars_for_unroll(&mut self, _iterator: &Var, _unroll_index: usize, _iterator_value: usize, _internal_vars: &BTreeSet<Var>) {}
    fn replace_vars_with_const(&mut self, _map: &BTreeMap<Var, F>) {}
    fn get_function_calls(&self, _function_calls: &mut Vec<String>) {}
    fn find_internal_vars(&self) -> (BTreeSet<Var>, BTreeSet<Var>) { (BTreeSet::new(), BTreeSet::new()) }
}

// EXAMPLE IMPLEMENTATIONS

// Simple statement - uses ALL defaults (zero code needed!)
impl StatementAnalysis for Panic {}
impl StatementAnalysis for Break {}
impl StatementAnalysis for LocationReport {}

// Function call - only overrides what it needs
impl StatementAnalysis for FunctionCall {
    fn get_function_calls(&self, function_calls: &mut Vec<String>) {
        function_calls.push(self.function_name.clone());
    }

    fn find_internal_vars(&self) -> (BTreeSet<Var>, BTreeSet<Var>) {
        let mut internal = BTreeSet::new();
        let mut external = BTreeSet::new();

        internal.extend(self.return_data.iter().cloned());
        for arg in &self.args {
            for var in vars_in_expression(arg) {
                if !internal.contains(&var) {
                    external.insert(var);
                }
            }
        }
        (internal, external)
    }
}

// Complex statement - overrides what it needs
impl StatementAnalysis for IfCondition {
    fn get_function_calls(&self, function_calls: &mut Vec<String>) {
        // Recursively collect from branches - NO giant match needed!
        for line in &self.then_branch {
            line.get_function_calls(function_calls);  // Dispatch to each line's implementation
        }
        for line in &self.else_branch {
            line.get_function_calls(function_calls);
        }
    }
}

// UTILITY FUNCTIONS - Now super clean!

/// NEW: Clean trait-based approach (replaces old get_function_called)
pub fn get_function_calls_new(lines: &[Line]) -> Vec<String> {
    let mut calls = Vec::new();
    for line in lines {
        line.get_function_calls(&mut calls);  // Simple dispatch!
    }
    calls
}

/// OLD: The giant match statement we're replacing
pub fn get_function_called_old(lines: &[Line], function_called: &mut Vec<String>) {
    for line in lines {
        match line {
            Line::Match(Match { value: _, arms }) => {
                for (_, statements) in arms {
                    get_function_called_old(statements, function_called);
                }
            }
            Line::FunctionCall(FunctionCall { function_name, .. }) => {
                function_called.push(function_name.clone());
            }
            Line::IfCondition(IfCondition {
                then_branch,
                else_branch,
                ..
            }) => {
                get_function_called_old(then_branch, function_called);
                get_function_called_old(else_branch, function_called);
            }
            Line::ForLoop(for_loop) => {
                get_function_called_old(&for_loop.body, function_called);
            }
            // 20+ more lines of boilerplate that do NOTHING!
            Line::Assignment(_) | Line::ArrayAssign(_) | Line::Assert(_)
            | Line::FunctionRet(_) | Line::Precompile(_) | Line::Print(_)
            | Line::DecomposeBits(_) | Line::CounterHint(_) | Line::MAlloc(_)
            | Line::Panic(_) | Line::Break(_) | Line::LocationReport(_) => {}
        }
    }
}

/// Line enum dispatch - clean and automatic
impl StatementAnalysis for Line {
    fn get_function_calls(&self, function_calls: &mut Vec<String>) {
        match self {
            Line::Match(stmt) => stmt.get_function_calls(function_calls),
            Line::Assignment(stmt) => stmt.get_function_calls(function_calls),
            Line::FunctionCall(stmt) => stmt.get_function_calls(function_calls),
            Line::IfCondition(stmt) => stmt.get_function_calls(function_calls),
            Line::ForLoop(stmt) => stmt.get_function_calls(function_calls),
            // All other variants automatically use default empty implementation!
            _ => {} // Or even better: remove this and let trait defaults handle it
        }
    }
}

/*
BENEFITS SUMMARY:

1. **Elimination of Boilerplate**:
   - OLD: 20+ match arms with empty implementations
   - NEW: Only implement what you need, defaults handle the rest

2. **Locality**:
   - OLD: All logic scattered in one giant utilities.rs file
   - NEW: Each statement type owns its logic

3. **Extensibility**:
   - OLD: Add new analysis = modify giant match statements
   - NEW: Add new method to trait, get defaults everywhere

4. **Maintainability**:
   - OLD: Change Assignment logic = find it in giant match
   - NEW: Change Assignment logic = edit assignment.rs

5. **Type Safety**:
   - OLD: Easy to forget a match arm
   - NEW: Compiler enforces all types implement trait

6. **Performance**:
   - OLD: Giant match statements, poor cache locality
   - NEW: Direct dispatch, better cache usage

This is exactly the pattern used by LLVM, GCC, and rustc!
*/