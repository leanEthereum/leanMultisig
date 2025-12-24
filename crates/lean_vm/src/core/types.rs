use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use std::{
    cmp::Ordering,
    fmt::{Display, Formatter},
};

/// Base field type for VM operations
pub type F = KoalaBear;

/// Extension field type for VM operations
pub type EF = QuinticExtensionFieldKB;

/// Line number in source code for debugging
pub type SourceLineNumber = usize;

/// Bytecode address (i.e., a value of the program counter)
pub type CodeAddress = usize;

/// Memory address
pub type MemoryAddress = usize;

/// Source code function name
pub type FunctionName = String;

/// Unique identifier for a file in a compilation
pub type FileId = usize;

/// Location in source code
#[derive(Hash, PartialEq, Eq, Debug, Clone, Copy)]
pub struct SourceLocation {
    pub file_id: FileId,
    pub line_number: SourceLineNumber,
}

impl Display for SourceLocation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "file_id: {}, line: {}", self.file_id, self.line_number)
    }
}

fn cmp_source_location(a: &SourceLocation, b: &SourceLocation) -> Ordering {
    match a.file_id.cmp(&b.file_id) {
        Ordering::Less => Ordering::Less,
        Ordering::Greater => Ordering::Greater,
        Ordering::Equal => a.line_number.cmp(&b.line_number),
    }
}

impl PartialOrd for SourceLocation {
    fn partial_cmp(&self, other: &SourceLocation) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SourceLocation {
    fn cmp(&self, other: &SourceLocation) -> Ordering {
        cmp_source_location(self, other)
    }
}
