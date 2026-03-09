use crate::SourceLocation;

/// Structured label for bytecode locations
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Label {
    /// Function entry point: @function_{name}
    Function(String),
    /// Program termination: @end_program
    EndProgram,
    /// Conditional flow: @if_{id}_line_{line_number}, @else_{id}_line_{line_number},
    ///   @if_else_end_{id}_line_{line_number}
    If {
        id: usize,
        kind: IfKind,
        location: SourceLocation,
    },
    /// Match statement end: @match_end_{id}
    MatchEnd(usize),
    /// Return from function call: @return_from_call_{id}
    ReturnFromCall(usize, SourceLocation),
    /// Loop definition: @loop_{id}_line_{line_number}
    Loop(usize, SourceLocation),
    /// Auxiliary variables during compilation
    AuxVar { kind: AuxKind, id: usize },
    /// Custom/raw label for backwards compatibility or special cases
    Custom(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IfKind {
    /// @if_{id}
    If,
    /// @else_{id}
    Else,
    /// @if_else_end_{id}
    End,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum AuxKind {
    /// @aux_var_{id}
    AuxVar,
    /// @arr_aux_{id}
    ArrayAux,
    /// @diff_{id}
    Diff,
    /// @inlined_var_{count}_{var}
    InlinedVar { count: usize, var: String },
    /// @unrolled_{index}_{value}_{var}
    UnrolledVar { index: usize, value: usize, var: String },
    /// @incremented_{var}
    Incremented(String),
    /// @trash_{id}
    Trash,
}

impl std::fmt::Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Function(name) => write!(f, "@function_{name}"),
            Self::EndProgram => write!(f, "@end_program"),
            Self::If { id, kind, location } => match kind {
                IfKind::If => write!(f, "@if_{id}_line_{}", location.line_number),
                IfKind::Else => write!(f, "@else_{id}_line_{}", location.line_number),
                IfKind::End => write!(f, "@if_else_end_{id}_line_{}", location.line_number),
            },
            Self::MatchEnd(id) => write!(f, "@match_end_{id}"),
            Self::ReturnFromCall(id, line_number) => {
                write!(f, "@return_from_call_{id}_line_{line_number}")
            }
            Self::Loop(id, line_number) => write!(f, "@loop_{id}_line_{line_number}"),
            Self::AuxVar { kind, id } => match kind {
                AuxKind::AuxVar => write!(f, "@aux_var_{id}"),
                AuxKind::ArrayAux => write!(f, "@arr_aux_{id}"),
                AuxKind::Diff => write!(f, "@diff_{id}"),
                AuxKind::InlinedVar { count, var } => write!(f, "@inlined_var_{count}_{var}"),
                AuxKind::UnrolledVar { index, value, var } => {
                    write!(f, "@unrolled_{index}_{value}_{var}")
                }
                AuxKind::Incremented(var) => write!(f, "@incremented_{var}"),
                AuxKind::Trash => write!(f, "@trash_{id}"),
            },
            Self::Custom(s) => write!(f, "{s}"),
        }
    }
}

impl Label {
    pub fn function(name: impl Into<String>) -> Self {
        Self::Function(name.into())
    }

    pub fn if_label(id: usize, location: SourceLocation) -> Self {
        Self::If {
            id,
            kind: IfKind::If,
            location,
        }
    }

    pub fn else_label(id: usize, location: SourceLocation) -> Self {
        Self::If {
            id,
            kind: IfKind::Else,
            location,
        }
    }

    pub fn if_else_end(id: usize, location: SourceLocation) -> Self {
        Self::If {
            id,
            kind: IfKind::End,
            location,
        }
    }

    pub fn match_end(id: usize) -> Self {
        Self::MatchEnd(id)
    }

    pub fn return_from_call(id: usize, location: SourceLocation) -> Self {
        Self::ReturnFromCall(id, location)
    }

    pub fn custom(label: impl Into<String>) -> Self {
        Self::Custom(label.into())
    }
}
