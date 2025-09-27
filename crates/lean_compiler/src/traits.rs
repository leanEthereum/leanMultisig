use std::fmt::Display;

/// Trait for displaying with proper indentation.
pub trait IndentedDisplay: Display {
    /// Returns a string representation with the specified indentation level.
    ///
    /// Default implementation just adds indentation to the Display output.
    fn to_string_with_indent(&self, indent: usize) -> String {
        format!("{}{}", "    ".repeat(indent), self)
    }
}
