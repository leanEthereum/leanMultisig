/// Structured label for bytecode locations
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Label {
    /// Function entry point: @function_{name}
    Function(String),
    /// Program termination: @end_program
    EndProgram,
    /// Conditional flow: @if_{id}, @else_{id}, @if_else_end_{id}
    If { id: usize, kind: IfKind },
    /// Match statement end: @match_end_{id}
    MatchEnd(usize),
    /// Return from function call: @return_from_call_{id}
    ReturnFromCall(usize),
    /// Loop definition: @loop_{id}
    Loop(usize),
    /// Built-in memory symbols
    BuiltinSymbol(BuiltinSymbol),
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
pub enum BuiltinSymbol {
    /// @public_input_start
    PublicInputStart,
    /// @pointer_to_zero_vector
    PointerToZeroVector,
    /// @pointer_to_one_vector
    PointerToOneVector,
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
    UnrolledVar {
        index: usize,
        value: usize,
        var: String,
    },
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
            Self::If { id, kind } => match kind {
                IfKind::If => write!(f, "@if_{id}"),
                IfKind::Else => write!(f, "@else_{id}"),
                IfKind::End => write!(f, "@if_else_end_{id}"),
            },
            Self::MatchEnd(id) => write!(f, "@match_end_{id}"),
            Self::ReturnFromCall(id) => write!(f, "@return_from_call_{id}"),
            Self::Loop(id) => write!(f, "@loop_{id}"),
            Self::BuiltinSymbol(symbol) => write!(f, "{symbol}"),
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

impl std::fmt::Display for BuiltinSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PublicInputStart => write!(f, "@public_input_start"),
            Self::PointerToZeroVector => write!(f, "@pointer_to_zero_vector"),
            Self::PointerToOneVector => write!(f, "@pointer_to_one_vector"),
        }
    }
}

impl Label {
    pub fn function(name: impl Into<String>) -> Self {
        Self::Function(name.into())
    }

    pub fn if_label(id: usize) -> Self {
        Self::If {
            id,
            kind: IfKind::If,
        }
    }

    pub fn else_label(id: usize) -> Self {
        Self::If {
            id,
            kind: IfKind::Else,
        }
    }

    pub fn if_else_end(id: usize) -> Self {
        Self::If {
            id,
            kind: IfKind::End,
        }
    }

    pub fn match_end(id: usize) -> Self {
        Self::MatchEnd(id)
    }

    pub fn return_from_call(id: usize) -> Self {
        Self::ReturnFromCall(id)
    }

    pub fn loop_label(id: usize) -> Self {
        Self::Loop(id)
    }

    pub fn aux_var(id: usize) -> Self {
        Self::AuxVar {
            kind: AuxKind::AuxVar,
            id,
        }
    }

    pub fn array_aux(id: usize) -> Self {
        Self::AuxVar {
            kind: AuxKind::ArrayAux,
            id,
        }
    }

    pub fn diff(id: usize) -> Self {
        Self::AuxVar {
            kind: AuxKind::Diff,
            id,
        }
    }

    pub fn inlined_var(count: usize, var: impl Into<String>) -> Self {
        Self::AuxVar {
            kind: AuxKind::InlinedVar {
                count,
                var: var.into(),
            },
            id: 0, // Not used for this variant
        }
    }

    pub fn unrolled_var(index: usize, value: usize, var: impl Into<String>) -> Self {
        Self::AuxVar {
            kind: AuxKind::UnrolledVar {
                index,
                value,
                var: var.into(),
            },
            id: 0, // Not used for this variant
        }
    }

    pub fn incremented(var: impl Into<String>) -> Self {
        Self::AuxVar {
            kind: AuxKind::Incremented(var.into()),
            id: 0, // Not used for this variant
        }
    }

    pub fn trash(id: usize) -> Self {
        Self::AuxVar {
            kind: AuxKind::Trash,
            id,
        }
    }

    pub fn custom(label: impl Into<String>) -> Self {
        Self::Custom(label.into())
    }
}
