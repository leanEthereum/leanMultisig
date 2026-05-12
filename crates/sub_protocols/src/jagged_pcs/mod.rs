//! Fancy jagged polynomial commitment scheme.
//!
//! Given a list of "sub-tables" -- each with a power-of-two number of columns
//! and an arbitrary (non-padded) row count -- this module commits to the
//! single dense polynomial obtained by concatenating the actual data of all
//! columns (row-major within each sub-table) and lets the verifier open
//! per-column evaluation claims as if each column had been committed
//! separately.
//!
//! The arithmetization is the "fancy jagged" variant of
//! [Hemo--Jue--Rabinovich--Roh--Rothblum](../../jagged_info/jagged_pcs.tex):
//! the verifier work for a single jagged evaluation is dominated by one
//! width-6 read-once branching program evaluation per claim (since each
//! claim's `z_tab` is on the boolean cube, only the corresponding sub-table
//! contributes to the `f_hat` evaluation).
//!
//! The "jagged assist" sub-protocol from the paper is not yet implemented;
//! it would replace the per-claim BP evals with a single BP eval at the
//! cost of an extra sumcheck. This is left as a follow-up; see the module
//! re-export comment in `sub_protocols::lib`.

mod assist;
mod branching;
mod config;
mod prover;
mod verifier;
mod zkvm;

pub use branching::*;
pub use config::*;
pub use prover::*;
pub use verifier::*;
pub use zkvm::*;

#[cfg(test)]
mod tests;
