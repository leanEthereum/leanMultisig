//! Core type definitions for the VM

use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};

/// Base field type for VM operations
pub type F = KoalaBear;

/// Extension field type for VM operations
pub type EF = QuinticExtensionFieldKB;

/// Location in source code for debugging
pub type LocationInSourceCode = usize;
