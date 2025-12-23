use std::collections::BTreeMap;

use colored::Colorize;

use crate::{FileId, FunctionName, SourceLineNumber, SourceLocation};

const STACK_TRACE_MAX_LINES_PER_FUNCTION: usize = 5;

pub(crate) fn pretty_stack_trace(
    source_code: &BTreeMap<FileId, String>,
    instructions: &[SourceLocation],
    function_locations: &BTreeMap<SourceLocation, FunctionName>,
    filepaths: &BTreeMap<FileId, String>,
    last_pc: usize,
) -> String {
    let mut source_locations: BTreeMap<SourceLocation, &str> = BTreeMap::new();
    for (f_id, src) in source_code.iter() {
        for (i, line) in src.lines().enumerate() {
            source_locations.insert(
                SourceLocation {
                    file_id: *f_id,
                    line_number: i,
                },
                line,
            );
        }
    }
    let mut result = String::new();
    let mut call_stack: Vec<(SourceLocation, String)> = Vec::new();
    let mut prev_function_location: Option<SourceLocation> = None;
    let mut skipped_lines: usize = 0; // Track skipped lines for current function

    result.push_str("╔═════════════════════════════════════════════════════════════════════════╗\n");
    result.push_str("║                               STACK TRACE                               ║\n");
    result.push_str("╚═════════════════════════════════════════════════════════════════════════╝\n\n");

    for (idx, &location) in instructions.iter().enumerate() {
        let (current_function_location, current_function_name) =
            find_function_for_location(location, function_locations);
        let current_filepath = filepaths
            .get(&current_function_location.file_id)
            .expect("Undefined FileId");

        if prev_function_location != Some(current_function_location) {
            assert_eq!(skipped_lines, 0);

            // Check if we're returning to a previous function or calling a new one
            if let Some(pos) = call_stack.iter().position(|(_, f)| f == &current_function_name) {
                // Returning to a previous function - pop the stack
                while call_stack.len() > pos + 1 {
                    call_stack.pop();
                    let indent = "│ ".repeat(call_stack.len());
                    result.push_str(&format!("{indent}└─ [return]\n"));
                }
                skipped_lines = 0;
            } else {
                // Add the new function to the stack
                call_stack.push((location, current_function_name.clone()));
                let indent = "│ ".repeat(call_stack.len() - 1);
                result.push_str(&format!(
                    "{}├─ {} ({current_filepath}:{})\n",
                    indent,
                    current_function_name.blue(),
                    current_function_location.line_number,
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
                current_function_location.line_number,
            );

            remaining_in_function < STACK_TRACE_MAX_LINES_PER_FUNCTION
        };

        if should_show {
            // Show skipped lines message if transitioning from skipping to showing
            if skipped_lines > 0 {
                let indent = "│ ".repeat(call_stack.len());
                result.push_str(&format!("{indent}├─ ... ({skipped_lines} lines skipped) ...\n"));
                skipped_lines = 0;
            }

            let indent = "│ ".repeat(call_stack.len());
            let location = SourceLocation {
                file_id: location.file_id,
                line_number: location.line_number.saturating_sub(1),
            };
            let code_line = source_locations.get(&location).unwrap().trim();

            if idx == instructions.len() - 1 {
                result.push_str(&format!(
                    "{}├─ {} {}\n",
                    indent,
                    format!("{current_filepath}:{}:", location.line_number).red(),
                    code_line
                ));
            } else {
                result.push_str(&format!(
                    "{indent}├─ {current_filepath}:{}: {code_line}\n",
                    location.line_number
                ));
            }
        } else {
            skipped_lines += 1;
        }

        prev_function_location = Some(current_function_location);
    }

    // Add summary
    result.push('\n');
    result.push_str("──────────────────────────────────────────────────────────────────────────\n");

    if !call_stack.is_empty() {
        result.push_str("\nCall stack:\n");
        for (i, (location, func)) in call_stack.iter().enumerate() {
            let filepath = filepaths.get(&location.file_id).expect("Undefined FileId");
            if i + 1 == call_stack.len() {
                result.push_str(&format!(
                    "  {}. {} ({}:{}, pc {})\n",
                    i + 1,
                    func,
                    filepath,
                    location.line_number,
                    last_pc
                ));
            } else {
                result.push_str(&format!(
                    "  {}. {} ({}:{})\n",
                    i + 1,
                    func,
                    filepath,
                    location.line_number
                ));
            }
        }
    }

    result
}

pub(crate) fn find_function_for_location(
    location: SourceLocation,
    function_locations: &BTreeMap<SourceLocation, String>,
) -> (SourceLocation, String) {
    function_locations
        .range(..=location)
        .next_back()
        .map(|(location, func_name)| (*location, func_name.clone()))
        .unwrap_or_else(|| panic!("Did not find function for location: {location}"))
}

fn count_remaining_lines_in_function(
    current_idx: usize,
    instructions: &[SourceLocation],
    function_locations: &BTreeMap<SourceLocation, String>,
    current_function_line: usize,
) -> usize {
    let mut count = 0;

    for &location in instructions.iter().skip(current_idx + 1) {
        let func_line = find_function_for_location(location, function_locations).0.line_number;

        if func_line != current_function_line {
            break;
        }
        count += 1;
    }

    count
}
