use std::collections::BTreeMap;

use colored::Colorize;

use crate::LocationInSourceCode;

const STACK_TRACE_MAX_LINES_PER_FUNCTION: usize = 5;

pub(crate) fn pretty_stack_trace(
    source_code: &str,
    instructions: &[LocationInSourceCode], // LocationInSourceCode = usize
    function_locations: &BTreeMap<usize, String>,
) -> String {
    let source_lines: Vec<&str> = source_code.lines().collect();
    let mut result = String::new();
    let mut call_stack: Vec<(usize, String)> = Vec::new(); // (line_number, function_name)
    let mut prev_function_line = usize::MAX;
    let mut skipped_lines: usize = 0; // Track skipped lines for current function

    result
        .push_str("╔═════════════════════════════════════════════════════════════════════════╗\n");
    result
        .push_str("║                               STACK TRACE                               ║\n");
    result.push_str(
        "╚═════════════════════════════════════════════════════════════════════════╝\n\n",
    );

    for (idx, &line_num) in instructions.iter().enumerate() {
        let (current_function_line, current_function_name) =
            find_function_for_line(line_num, function_locations);

        if prev_function_line != current_function_line {
            assert_eq!(skipped_lines, 0);

            // Check if we're returning to a previous function or calling a new one
            if let Some(pos) = call_stack
                .iter()
                .position(|(_, f)| f == &current_function_name)
            {
                // Returning to a previous function - pop the stack
                while call_stack.len() > pos + 1 {
                    call_stack.pop();
                    let indent = "│ ".repeat(call_stack.len());
                    result.push_str(&format!("{indent}└─ [return]\n"));
                }
                skipped_lines = 0;
            } else {
                // Add the new function to the stack
                call_stack.push((line_num, current_function_name.clone()));
                let indent = "│ ".repeat(call_stack.len() - 1);
                result.push_str(&format!(
                    "{}├─ {} (line {})\n",
                    indent,
                    current_function_name.blue(),
                    current_function_line
                ));
                skipped_lines = 0;
            }
        }

        // Determine if we should show this line
        let should_show = if idx == instructions.len() - 1 {
            // Always show the last line (error location)
            true
        } else {
            // Count remaining lines in this function
            let remaining_in_function = count_remaining_lines_in_function(
                idx,
                instructions,
                function_locations,
                current_function_line,
            );

            remaining_in_function < STACK_TRACE_MAX_LINES_PER_FUNCTION
        };

        if should_show {
            // Show skipped lines message if transitioning from skipping to showing
            if skipped_lines > 0 {
                let indent = "│ ".repeat(call_stack.len());
                result.push_str(&format!(
                    "{indent}├─ ... ({skipped_lines} lines skipped) ...\n"
                ));
                skipped_lines = 0;
            }

            let indent = "│ ".repeat(call_stack.len());
            let code_line = source_lines.get(line_num.saturating_sub(1)).unwrap().trim();

            if idx == instructions.len() - 1 {
                result.push_str(&format!(
                    "{}├─ {} {}\n",
                    indent,
                    format!("line {line_num}:").red(),
                    code_line
                ));
            } else {
                result.push_str(&format!("{indent}├─ line {line_num}: {code_line}\n"));
            }
        } else {
            skipped_lines += 1;
        }

        prev_function_line = current_function_line;
    }

    // Add summary
    result.push('\n');
    result.push_str("──────────────────────────────────────────────────────────────────────────\n");

    if !call_stack.is_empty() {
        result.push_str("\nCall stack:\n");
        for (i, (line, func)) in call_stack.iter().enumerate() {
            result.push_str(&format!("  {}. {} (line {})\n", i + 1, func, line));
        }
    }

    result
}

pub(crate) fn find_function_for_line(
    line_num: usize,
    function_locations: &BTreeMap<usize, String>,
) -> (usize, String) {
    function_locations
        .range(..=line_num)
        .next_back()
        .map(|(line, func_name)| (*line, func_name.clone()))
        .unwrap()
}

fn count_remaining_lines_in_function(
    current_idx: usize,
    instructions: &[LocationInSourceCode],
    function_locations: &BTreeMap<usize, String>,
    current_function_line: usize,
) -> usize {
    let mut count = 0;

    for i in (current_idx + 1)..instructions.len() {
        let line_num = instructions[i];
        let func_line = find_function_for_line(line_num, function_locations).0;

        if func_line != current_function_line {
            break;
        }
        count += 1;
    }

    count
}
