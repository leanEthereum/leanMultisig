use super::expression::ExpressionParser;
use super::statement::StatementParser;
use super::{Parse, ParseContext, next_inner_pair};
use crate::{
    a_simplify_lang::VarOrConstMallocAccess,
    lang::{AssignmentTarget, Expression, Function, FunctionArg, Line, MathOperation, SimpleExpr, SourceLocation},
    parser::{
        error::{ParseResult, SemanticError},
        grammar::{ParsePair, Rule},
    },
};
use lean_vm::{ALL_TABLES, TableT};

/// Reserved function names that users cannot define.
pub const RESERVED_FUNCTION_NAMES: &[&str] = &[
    // Built-in functions
    "print",
    "Array",
    "DynArray",
    "push", // Compile-time vector push
    // Compile-time only functions
    "len",
    "log2_ceil",
    "next_multiple_of",
    "saturating_sub",
    // Custom hints (manually listed since CustomHint doesn't re-export strum iterator)
    "hint_decompose_bits_xmss",
    "hint_decompose_bits",
    "range",
    "match_range",
];

/// Check if a function name is reserved.
fn is_reserved_function_name(name: &str) -> bool {
    // Check static reserved names
    if RESERVED_FUNCTION_NAMES.contains(&name) {
        return true;
    }
    // Check precompile names (poseidon16, dot_product, execution)
    for table in ALL_TABLES {
        if table.name() == name && !table.is_execution_table() {
            return true;
        }
    }
    false
}

/// Parser for complete function definitions.
pub struct FunctionParser;

impl Parse<Function> for FunctionParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Function> {
        let mut inner = pair.into_inner().peekable();

        // Parse optional @inline decorator
        let inlined = match inner.peek().map(|x| x.as_rule()) {
            Some(Rule::decorator) => {
                let decorator = inner.next().unwrap();
                let decorator_name = decorator.into_inner().next().unwrap().as_str();
                if decorator_name == "inline" {
                    true
                } else {
                    return Err(SemanticError::new(format!("Unknown decorator '@{decorator_name}'")).into());
                }
            }
            _ => false,
        };

        let name = next_inner_pair(&mut inner, "function name")?.as_str().to_string();

        // Check for reserved function names
        if is_reserved_function_name(&name) {
            return Err(SemanticError::new(format!("Cannot define function with reserved name '{name}'")).into());
        }

        let mut arguments = Vec::new();
        let mut body = Vec::new();

        for pair in inner {
            match pair.as_rule() {
                Rule::parameter_list => {
                    for param in pair.into_inner() {
                        if param.as_rule() == Rule::parameter {
                            arguments.push(ParameterParser.parse(param, ctx)?);
                        }
                    }
                }
                Rule::statement => {
                    Self::add_statement_with_location(&mut body, pair, ctx)?;
                }
                _ => {}
            }
        }

        let n_returned_vars = Self::infer_return_count(&name, &body)?;

        Ok(Function {
            name,
            arguments,
            inlined,
            n_returned_vars,
            body,
        })
    }
}

impl FunctionParser {
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

    /// Infer the number of return values from return statements in the function body.
    /// All return statements must return the same number of values.
    fn infer_return_count(func_name: &str, body: &[Line]) -> ParseResult<usize> {
        let mut return_counts: Vec<usize> = Vec::new();
        Self::collect_return_counts(body, &mut return_counts);

        match return_counts.as_slice() {
            [] => Err(SemanticError::new(format!("Function '{func_name}' has no return statements")).into()),
            [first, rest @ ..] => {
                if rest.iter().any(|&count| count != *first) {
                    return Err(
                        SemanticError::new(format!("Inconsistent return counts in function '{func_name}'")).into(),
                    );
                }
                Ok(*first)
            }
        }
    }

    fn collect_return_counts(body: &[Line], counts: &mut Vec<usize>) {
        for line in body {
            if let Line::FunctionRet { return_data } = line {
                counts.push(return_data.len());
            }
            for block in line.nested_blocks() {
                Self::collect_return_counts(block, counts);
            }
        }
    }
}

/// Parser for function parameters.
pub struct ParameterParser;

impl Parse<FunctionArg> for ParameterParser {
    fn parse(&self, pair: ParsePair<'_>, _ctx: &mut ParseContext) -> ParseResult<FunctionArg> {
        let mut inner = pair.into_inner();
        let name = next_inner_pair(&mut inner, "parameter name")?.as_str().to_string();

        // Check for optional type annotation (: Const or : Mut)
        let (is_const, is_mutable) = if let Some(annotation) = inner.next() {
            match annotation.as_str().trim() {
                ": Const" => (true, false),
                ": Mut" => (false, true),
                other => return Err(SemanticError::new(format!("Invalid parameter annotation: {other}")).into()),
            }
        } else {
            (false, false)
        };

        Ok(FunctionArg {
            name,
            is_const,
            is_mutable,
        })
    }
}

/// Parser for individual assignment targets (variable or array access).
pub struct AssignmentTargetParser;

impl Parse<AssignmentTarget> for AssignmentTargetParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<AssignmentTarget> {
        let mut inner = pair.into_inner().peekable();

        let first_pair = next_inner_pair(&mut inner, "assignment target")?;

        match first_pair.as_rule() {
            Rule::array_access_expr => {
                let mut inner_pairs = first_pair.into_inner();
                let array = next_inner_pair(&mut inner_pairs, "array name")?.as_str().to_string();
                let index = ExpressionParser.parse(next_inner_pair(&mut inner_pairs, "array index")?, ctx)?;
                Ok(AssignmentTarget::ArrayAccess {
                    array,
                    index: Box::new(index),
                })
            }
            Rule::identifier => {
                let var = first_pair.as_str().to_string();
                // Check for mut_annotation (: Mut) following the identifier
                let is_mutable = inner
                    .peek()
                    .map(|p| p.as_rule() == Rule::mut_annotation)
                    .unwrap_or(false);
                if is_mutable {
                    inner.next(); // consume the mut_annotation
                }
                Ok(AssignmentTarget::Var { var, is_mutable })
            }
            _ => Err(SemanticError::new("Expected identifier or array access").into()),
        }
    }
}

pub struct AssignmentParser;

impl Parse<Line> for AssignmentParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Line> {
        let line_number = pair.line_col().0;
        let mut inner = pair.into_inner().peekable();

        // Check if there's assignment_target_list and assign_op
        let lhs_info = if let Some(first) = inner.peek()
            && first.as_rule() == Rule::assignment_target_list
        {
            let target_list = inner.next().unwrap();
            let op_pair = next_inner_pair(&mut inner, "assignment operator")?;
            Some(Self::parse_lhs(target_list, op_pair, ctx)?)
        } else {
            None
        };

        // Parse the RHS expression
        let expr_pair = next_inner_pair(&mut inner, "expression")?;
        let rhs_expr = ExpressionParser.parse(expr_pair, ctx)?;
        let location = SourceLocation {
            file_id: ctx.current_file_id,
            line_number,
        };
        match lhs_info {
            Some(LhsInfo::Compound { target, lhs_expr, op }) => {
                // Desugar: target op= expr -> target = target op expr
                let desugared_expr = Expression::MathExpr(op, vec![lhs_expr, rhs_expr]);
                Ok(Line::Statement {
                    targets: vec![target],
                    value: desugared_expr,
                    location,
                })
            }
            Some(LhsInfo::Simple { mut targets }) => {
                for target in &mut targets {
                    if let AssignmentTarget::Var { var, .. } = target
                        && var == "_"
                    {
                        *var = ctx.next_trash_var();
                    }
                }
                Self::finalize_simple_assignment(location, targets, rhs_expr)
            }
            None => {
                // No LHS - expression statement (e.g., function call)
                Self::finalize_simple_assignment(location, Vec::new(), rhs_expr)
            }
        }
    }
}

/// Parsed LHS information
enum LhsInfo {
    Compound {
        target: AssignmentTarget,
        lhs_expr: Expression,
        op: MathOperation,
    },
    Simple {
        targets: Vec<AssignmentTarget>,
    },
}

impl AssignmentParser {
    /// Parse assignment LHS (target list + operator) and return structured info
    fn parse_lhs(
        target_list_pair: ParsePair<'_>,
        op_pair: ParsePair<'_>,
        ctx: &mut ParseContext,
    ) -> ParseResult<LhsInfo> {
        let op_str = op_pair.as_str();

        if op_str == "=" {
            // Simple assignment - parse target list
            let mut inner = target_list_pair.into_inner();
            let first = next_inner_pair(&mut inner, "assignment target")?;

            let targets = match first.as_rule() {
                Rule::simple_target_list => first
                    .into_inner()
                    .map(|item| AssignmentTargetParser.parse(item, ctx))
                    .collect::<ParseResult<Vec<AssignmentTarget>>>()?,
                _ => return Err(SemanticError::new("Expected assignment target").into()),
            };
            Ok(LhsInfo::Simple { targets })
        } else {
            // Compound assignment - validate constraints
            let mut outer = target_list_pair.into_inner();
            let inner_list = next_inner_pair(&mut outer, "assignment target")?;

            // Must be simple_target_list with exactly one target
            let targets: Vec<_> = inner_list.into_inner().collect();

            if targets.len() != 1 {
                return Err(SemanticError::new("Compound assignment operators only allow a single target").into());
            }

            let target_pair = targets.into_iter().next().unwrap();
            let (target, lhs_expr) = Self::parse_compound_target(target_pair, ctx)?;

            let op = match op_str {
                "+=" => MathOperation::Add,
                "-=" => MathOperation::Sub,
                "*=" => MathOperation::Mul,
                "/=" => MathOperation::Div,
                _ => return Err(SemanticError::new("Invalid compound operator").into()),
            };

            Ok(LhsInfo::Compound { target, lhs_expr, op })
        }
    }

    /// Parse a single target for compound assignment (no mut allowed)
    fn parse_compound_target(
        pair: ParsePair<'_>,
        ctx: &mut ParseContext,
    ) -> ParseResult<(AssignmentTarget, Expression)> {
        let mut inner = pair.into_inner().peekable();

        let target_inner = next_inner_pair(&mut inner, "assignment target")?;

        // Check for mut annotation (: Mut) - not allowed in compound assignment
        if inner
            .peek()
            .map(|p| p.as_rule() == Rule::mut_annotation)
            .unwrap_or(false)
        {
            return Err(SemanticError::new("Cannot use ': Mut' with compound assignment operators").into());
        }

        match target_inner.as_rule() {
            Rule::array_access_expr => {
                let mut arr_inner = target_inner.into_inner();
                let array = next_inner_pair(&mut arr_inner, "array name")?.as_str().to_string();
                let indices: Vec<Expression> = arr_inner
                    .map(|idx_pair| ExpressionParser.parse(idx_pair, ctx))
                    .collect::<ParseResult<Vec<_>>>()?;

                let target = AssignmentTarget::ArrayAccess {
                    array: array.clone(),
                    index: Box::new(indices[0].clone()),
                };
                let lhs_expr = Expression::ArrayAccess { array, index: indices };
                Ok((target, lhs_expr))
            }
            Rule::identifier => {
                let var = target_inner.as_str().to_string();
                let target = AssignmentTarget::Var {
                    var: var.clone(),
                    is_mutable: false,
                };
                let lhs_expr = Expression::Value(SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)));
                Ok((target, lhs_expr))
            }
            _ => Err(SemanticError::new("Expected identifier or array access").into()),
        }
    }

    /// Finalize a simple assignment (handles function calls vs regular expressions)
    fn finalize_simple_assignment(
        location: SourceLocation,
        targets: Vec<AssignmentTarget>,
        expr: Expression,
    ) -> ParseResult<Line> {
        match &expr {
            Expression::FunctionCall {
                function_name, args, ..
            } => Self::handle_function_call(location, function_name.clone(), args.clone(), targets),
            _ => {
                if targets.is_empty() {
                    return Err(SemanticError::new("Expression statement has no effect").into());
                }
                if targets.len() > 1 {
                    return Err(SemanticError::new(
                        "Multiple assignment targets require a function call on the right side",
                    )
                    .into());
                }
                Ok(Line::Statement {
                    targets,
                    value: expr,
                    location,
                })
            }
        }
    }
}

impl AssignmentParser {
    fn handle_function_call(
        location: SourceLocation,
        function_name: String,
        args: Vec<Expression>,
        return_data: Vec<AssignmentTarget>,
    ) -> ParseResult<Line> {
        // Function calls (print, precompiles, custom hints) are handled in a_simplify_lang.rs
        Ok(Line::Statement {
            targets: return_data,
            value: Expression::FunctionCall {
                function_name,
                args,
                location,
            },
            location,
        })
    }
}

/// Parser for tuple expressions used in function calls.
pub struct TupleExpressionParser;

impl Parse<Vec<Expression>> for TupleExpressionParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Vec<Expression>> {
        pair.into_inner()
            .map(|item| ExpressionParser.parse(item, ctx))
            .collect()
    }
}
