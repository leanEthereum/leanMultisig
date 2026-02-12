use super::function::FunctionParser;
use super::literal::ConstantDeclarationParser;
use crate::{
    CompilationFlags, ProgramSource,
    lang::{Program, SourceLocation},
    parser::{
        error::{ParseError, ParseResult, SemanticError},
        grammar::{ParsePair, Rule, parse_source},
        parsers::{Parse, ParseContext, ParsedConstant, next_inner_pair},
    },
};
use std::collections::BTreeMap;
use std::path::Path;

/// Parser for complete programs.
pub struct ProgramParser;

impl Parse<Program> for ProgramParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Program> {
        let mut functions = BTreeMap::new();
        let mut function_locations = BTreeMap::new();
        let mut source_code = BTreeMap::new();
        let mut filepaths = BTreeMap::new();
        let file_id = ctx.get_next_file_id();
        ctx.current_file_id = file_id;
        filepaths.insert(file_id, ctx.current_filepath.clone());
        source_code.insert(file_id, ctx.current_source_code.clone());

        for item in pair.into_inner() {
            match item.as_rule() {
                Rule::constant_declaration => {
                    let (name, value) = ConstantDeclarationParser.parse(item, ctx)?;
                    match value {
                        ParsedConstant::Scalar(v) => ctx.add_constant(name, v)?,
                        ParsedConstant::Array(arr) => ctx.add_const_array(name, arr)?,
                    }
                }
                Rule::import_statement => {
                    // Visit the imported file and parse it into the context
                    // and program; also keep track of which files have been
                    // imported and do not import the same file twice.
                    // Imports are resolved relative to the importing file's directory.
                    // Parent directory imports are supported: `from ..module import *`
                    let relative_path = ImportStatementParser.parse(item, ctx)?;
                    let is_parent_import = relative_path.starts_with("..");

                    // Parent imports (..module) resolve relative to the current file's directory.
                    // Normal imports resolve from the import root (entry file's directory).
                    let base_dir = if is_parent_import {
                        Path::new(&ctx.current_filepath)
                            .parent()
                            .filter(|p| !p.as_os_str().is_empty())
                            .map(|p| p.to_string_lossy().to_string())
                            .unwrap_or_else(|| ctx.import_root.clone())
                    } else {
                        ctx.import_root.clone()
                    };
                    let raw_path = Path::new(&base_dir).join(&relative_path);
                    let filepath = raw_path
                        .canonicalize()
                        .map_err(|e| {
                            SemanticError::new(format!(
                                "Cannot resolve import '{}' (resolved to '{}'): {}",
                                relative_path,
                                raw_path.display(),
                                e
                            ))
                        })?
                        .to_string_lossy()
                        .to_string();

                    // Check for circular imports
                    if ctx.import_stack.contains(&filepath) {
                        let cycle: Vec<_> = ctx
                            .import_stack
                            .iter()
                            .skip_while(|p| *p != &filepath)
                            .cloned()
                            .collect();
                        return Err(SemanticError::new(format!(
                            "Circular import detected: {} -> {}",
                            cycle.join(" -> "),
                            filepath
                        ))
                        .into());
                    }

                    if !ctx.imported_filepaths.contains(&filepath) {
                        let saved_filepath = ctx.current_filepath.clone();
                        let saved_file_id = ctx.current_file_id;
                        let saved_import_root = ctx.import_root.clone();
                        ctx.current_filepath = filepath.clone();
                        // For parent directory imports, update import_root to the imported
                        // file's directory so transitive non-relative imports resolve correctly.
                        if is_parent_import {
                            ctx.import_root = Path::new(&filepath)
                                .parent()
                                .map(|p| p.to_string_lossy().to_string())
                                .unwrap_or_default();
                        }
                        ctx.imported_filepaths.insert(filepath.clone());
                        ctx.import_stack.push(filepath.clone());
                        ctx.current_source_code = ProgramSource::Filepath(filepath).get_content(&ctx.flags)?;
                        let subprogram = parse_program_helper(ctx)?;
                        ctx.import_stack.pop();
                        functions.extend(subprogram.functions);
                        function_locations.extend(subprogram.function_locations);
                        source_code.extend(subprogram.source_code);
                        filepaths.extend(subprogram.filepaths);
                        ctx.import_root = saved_import_root;
                        ctx.current_filepath = saved_filepath;
                        ctx.current_file_id = saved_file_id;
                    }
                }
                Rule::function => {
                    let line_number = item.line_col().0;
                    let location = SourceLocation { file_id, line_number };
                    let function = FunctionParser.parse(item, ctx)?;
                    let name = function.name.clone();

                    function_locations.insert(location, name.clone());

                    if functions.insert(name.clone(), function).is_some() {
                        return Err(SemanticError::with_context(
                            format!("Multiply defined function: {name}"),
                            "function definition",
                        )
                        .into());
                    }
                }
                Rule::EOI => break,
                _ => {} // Skip other rules
            }
        }

        Ok(Program {
            functions,
            const_arrays: ctx.const_arrays.clone(),
            function_locations,
            filepaths,
            source_code,
        })
    }
}

/// Parser for import statements.
pub struct ImportStatementParser;

impl Parse<String> for ImportStatementParser {
    fn parse(&self, pair: ParsePair<'_>, _ctx: &mut ParseContext) -> ParseResult<String> {
        let mut inner = pair.into_inner();
        let item = next_inner_pair(&mut inner, "module_path")?;
        match item.as_rule() {
            Rule::module_path => {
                let mut has_parent_prefix = false;
                let mut parts: Vec<&str> = Vec::new();
                for p in item.into_inner() {
                    match p.as_rule() {
                        Rule::parent_prefix => has_parent_prefix = true,
                        Rule::identifier => parts.push(p.as_str()),
                        _ => {}
                    }
                }
                // Convert module.path to path/to/file.py, with ../ prefix for parent imports
                let filepath = if has_parent_prefix {
                    format!("../{}.py", parts.join("/"))
                } else {
                    format!("{}.py", parts.join("/"))
                };
                Ok(filepath)
            }
            _ => Err(SemanticError::with_context(
                format!("Expected a module path, got: {}", item.as_str()),
                "module_path",
            )
            .into()),
        }
    }
}

pub fn remove_comments(input: &str) -> String {
    let mut s = input;
    let mut result = String::with_capacity(input.len());
    while !s.is_empty() {
        // Handle # line comments (but not #![...] pragmas)
        if s.starts_with('#') && !s.starts_with("#![") {
            s = s.find('\n').map_or("", |i| &s[i..]);
        // Handle """ block comments
        } else if let Some(rest) = s.strip_prefix("\"\"\"") {
            s = rest.find("\"\"\"").map_or("", |i| &rest[i + 3..]);
        // Find next potential comment start
        } else if let Some(i) = s[1..].find(['#', '"']) {
            result.push_str(&s[..i + 1]);
            s = &s[i + 1..];
        } else {
            result.push_str(s);
            break;
        }
    }
    result
}

/// Removes the snark_lib import if it's on the first line.
/// This import is only used for Python execution compatibility and is not relevant to the zkDSL.
/// Preserves line numbers by keeping blank lines.
pub fn remove_snark_lib_import(input: &str) -> String {
    let mut lines: Vec<&str> = input.lines().collect();
    let mut modified = false;

    // Remove snark_lib imports from the beginning, preserving blank lines to maintain line numbers
    for line in lines.iter_mut() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue; // keep blank lines
        }
        let is_snark_lib_import =
            (trimmed.starts_with("import ") || trimmed.starts_with("from ")) && trimmed.contains("snark_lib");
        if is_snark_lib_import {
            *line = ""; // Replace with empty string to preserve line number
            modified = true;
        } else {
            break; // Stop at first non-import, non-blank line
        }
    }

    if modified { lines.join("\n") } else { input.to_string() }
}

/// Preprocesses Python-like indentation syntax into explicit block markers.
/// Handles line continuations (`\`) and implicit continuation inside parentheses/brackets/braces.
/// Converts indentation-based blocks to <END> markers.
pub fn preprocess_indentation(input: &str) -> Result<String, ParseError> {
    let mut result = String::with_capacity(input.len() * 2);
    let mut indent_stack: Vec<usize> = vec![0];

    // First, collect logical lines by joining continued lines
    // Continuation happens with `\` or when inside unclosed parentheses/brackets/braces
    let mut logical_lines: Vec<(usize, String)> = Vec::new(); // (starting line number, content)
    let mut current_logical_line = String::new();
    let mut logical_line_start = 1;
    let mut paren_depth = 0i32; // tracks (), [], {}

    for (i, line) in input.lines().enumerate() {
        let line_number = i + 1;
        let trimmed = line.trim_end();

        if current_logical_line.is_empty() {
            logical_line_start = line_number;
        }

        // Count parentheses/brackets/braces in this line
        for c in trimmed.chars() {
            match c {
                '(' | '[' | '{' => paren_depth += 1,
                ')' | ']' | '}' => paren_depth -= 1,
                _ => {}
            }
        }

        // Check for explicit line continuation with `\`
        if let Some(without_backslash) = trimmed.strip_suffix('\\') {
            current_logical_line.push_str(without_backslash.trim_end());
            current_logical_line.push(' ');
        } else if paren_depth > 0 {
            // Implicit continuation: inside unclosed parens/brackets/braces
            current_logical_line.push_str(trimmed);
            current_logical_line.push(' ');
        } else {
            current_logical_line.push_str(line);
            logical_lines.push((logical_line_start, std::mem::take(&mut current_logical_line)));
        }
    }
    // Handle any remaining content (file ending with `\` or unclosed parens)
    if !current_logical_line.is_empty() {
        logical_lines.push((logical_line_start, current_logical_line));
    }

    // Process each logical line, preserving original line numbers
    let mut current_output_line = 1;
    for (line_number, line) in logical_lines {
        let indent = line
            .chars()
            .take_while(|c| *c == ' ' || *c == '\t')
            .map(|c| if c == '\t' { 4 } else { 1 })
            .sum::<usize>();

        let trimmed = line.trim();

        if trimmed.is_empty() {
            continue;
        }

        let current_indent = *indent_stack.last().unwrap();

        if indent > current_indent {
            return Err(ParseError::from(format!(
                "Unexpected indentation at line {line_number}: expected {current_indent} spaces, got {indent}"
            )));
        }

        if indent < current_indent {
            while indent_stack.len() > 1 && indent < *indent_stack.last().unwrap() {
                indent_stack.pop();
                result.push_str("<END><NL>");
                // Don't increment current_output_line - <NL> is a token, not an actual newline
            }
            if indent != *indent_stack.last().unwrap() {
                return Err(ParseError::from(format!(
                    "Invalid indentation at line {line_number}: got {indent} spaces, which doesn't match any block level"
                )));
            }
        }

        // Pad with actual newlines to preserve original line number for pest
        while current_output_line < line_number {
            result.push('\n');
            current_output_line += 1;
        }

        result.push_str(trimmed);
        result.push_str("<NL>");
        // <NL> is a token, not an actual newline, so don't increment line counter

        // Handle indent (open block after colon)
        if trimmed.ends_with(':') && !trimmed.starts_with("import") {
            indent_stack.push(indent + 4); // expect indented block
        }
    }

    // Close any remaining open blocks
    while indent_stack.len() > 1 {
        indent_stack.pop();
        result.push_str("<END><NL>");
    }

    Ok(result)
}

fn parse_program_helper(ctx: &mut ParseContext) -> Result<Program, ParseError> {
    let without_snark_lib_import = remove_snark_lib_import(&ctx.current_source_code);
    let without_comments = remove_comments(&without_snark_lib_import);
    let processed_input = preprocess_indentation(&without_comments)?;

    // Parse grammar into AST nodes
    let program_pair = parse_source(&processed_input)?;

    // Parse into semantic structures
    ProgramParser.parse(program_pair, ctx)
}

pub fn parse_program(input: &ProgramSource, flags: CompilationFlags) -> Result<Program, ParseError> {
    parse_program_helper(&mut ParseContext::new(input, flags)?)
}
