use std::collections::BTreeMap;

use colored::Colorize;

use crate::isa::Bytecode;
use crate::{CodeAddress, FunctionName, SourceLocation};

pub(crate) fn pretty_stack_trace(
    bytecode: &Bytecode,
    error_pc: CodeAddress,
    location_history: &[SourceLocation],
) -> String {
    let mut out = String::new();
    let error_loc = bytecode.pc_to_location.get(error_pc).copied();

    out.push_str(&format!("{}\n\n", "ERROR".red().bold()));

    if let Some(loc) = error_loc {
        let path = filepath(bytecode, loc.file_id);
        let (_, func) = find_function_for_location(loc, &bytecode.function_locations);

        out.push_str(&format!(
            "  at {}:{} in {}\n\n",
            path,
            loc.line_number,
            func.blue().bold()
        ));

        // Source context
        if let Some(source) = bytecode.source_code.get(&loc.file_id) {
            let lines: Vec<&str> = source.lines().collect();
            let err_line = loc.line_number.saturating_sub(1);
            let start = err_line.saturating_sub(3);
            let end = (err_line + 2).min(lines.len());

            for i in start..end {
                let content = lines.get(i).unwrap_or(&"");
                if i == err_line {
                    out.push_str(&format!(
                        "  {:>4} {} {}\n",
                        (i + 1).to_string().red().bold(),
                        "│".red(),
                        content
                    ));
                    let indent = content.len() - content.trim_start().len();
                    out.push_str(&format!(
                        "       {} {}{}\n",
                        "│".red(),
                        " ".repeat(indent),
                        "^".repeat(content.trim().len().max(1)).red()
                    ));
                } else {
                    out.push_str(&format!(
                        "  {:>4} {} {}\n",
                        (i + 1).to_string().dimmed(),
                        "│".dimmed(),
                        content.dimmed()
                    ));
                }
            }
        }
    }

    // Call stack
    let stack = build_call_stack(location_history, &bytecode.function_locations);
    if stack.len() > 1 {
        out.push_str(&format!("\n{}\n\n", "CALL STACK".yellow().bold()));
        for (i, (func, call_loc)) in stack.iter().rev().enumerate() {
            let path = filepath(bytecode, call_loc.file_id);
            let marker = if i == 0 { "→".red().to_string() } else { " ".into() };
            out.push_str(&format!(
                "  {} {} at {}:{}\n",
                marker,
                format!("{func}()").bold(),
                path.dimmed(),
                call_loc.line_number.to_string().dimmed()
            ));
        }
    }

    out
}

fn build_call_stack(
    history: &[SourceLocation],
    func_locs: &BTreeMap<SourceLocation, String>,
) -> Vec<(String, SourceLocation)> {
    let mut stack: Vec<(String, SourceLocation)> = Vec::new();

    for (i, &loc) in history.iter().enumerate() {
        let (_, func) = find_function_for_location(loc, func_locs);

        if stack.last().map(|(f, _)| f) != Some(&func) {
            if let Some(pos) = stack.iter().position(|(f, _)| f == &func) {
                stack.truncate(pos + 1);
            } else {
                let call_loc = if i > 0 { history[i - 1] } else { loc };
                stack.push((func, call_loc));
            }
        }
    }
    stack
}

pub(crate) fn find_function_for_location(
    loc: SourceLocation,
    func_locs: &BTreeMap<SourceLocation, FunctionName>,
) -> (SourceLocation, String) {
    func_locs
        .range(..=loc)
        .next_back()
        .map(|(l, f)| (*l, f.clone()))
        .unwrap_or((
            SourceLocation {
                file_id: 0,
                line_number: 0,
            },
            "<unknown>".into(),
        ))
}

fn filepath(bytecode: &Bytecode, file_id: usize) -> &str {
    bytecode
        .filepaths
        .get(&file_id)
        .map(|s| s.as_str())
        .unwrap_or("<unknown>")
}
