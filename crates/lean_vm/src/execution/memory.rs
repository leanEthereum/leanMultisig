//! Memory management for the VM
use crate::MAX_LOG_MEMORY_SIZE;
use crate::core::{DIMENSION, EF, F};
use crate::diagnostics::RunnerError;
use multilinear_toolkit::prelude::*;

/// VM memory implementation with sparse allocation
#[derive(Debug, Clone, Default)]
pub struct Memory(pub Vec<Option<F>>);

impl Memory {
    /// Creates a new memory instance, initializing it with public data
    pub fn new(public_memory: Vec<F>) -> Self {
        Self(public_memory.into_par_iter().map(Some).collect())
    }

    /// Creates an empty memory instance
    pub fn empty() -> Self {
        Self::default()
    }

    /// Reads a single value from a memory address
    ///
    /// Returns an error if the address is uninitialized
    pub fn get(&self, index: usize) -> Result<F, RunnerError> {
        self.0
            .get(index)
            .copied()
            .flatten()
            .ok_or(RunnerError::UndefinedMemory(index))
    }

    /// Reads a single value from a memory address, returning ZERO if undefined or out of bounds.
    /// Used for range check hint resolution where undefined memory is acceptable.
    pub fn get_or_zero(&self, index: usize) -> F {
        self.0.get(index).copied().flatten().unwrap_or(F::ZERO)
    }

    /// Returns true if a memory address is defined
    pub fn is_defined(&self, index: usize) -> bool {
        self.0.get(index).copied().flatten().is_some()
    }

    /// Sets a value at a memory address
    ///
    /// Returns an error if the address is already set to a different value
    /// or if we exceed memory limits
    pub fn set(&mut self, index: usize, value: F) -> Result<(), RunnerError> {
        if index >= self.0.len() {
            if index >= 1 << MAX_LOG_MEMORY_SIZE {
                return Err(RunnerError::OutOfMemory);
            }
            self.0.resize((index + 1).next_power_of_two(), None);
        }
        if let Some(existing) = &mut self.0[index] {
            if *existing != value {
                return Err(RunnerError::MemoryAlreadySet {
                    address: index,
                    prev_value: *existing,
                    new_value: value,
                });
            }
        } else {
            self.0[index] = Some(value);
        }
        Ok(())
    }

    /// Gets the current size of allocated memory
    pub const fn size(&self) -> usize {
        self.0.len()
    }

    /// Get an extension field element from memory
    pub fn get_ef_element(&self, index: usize) -> Result<EF, RunnerError> {
        // index: non vectorized pointer
        let mut coeffs = [F::ZERO; DIMENSION];
        for (offset, coeff) in coeffs.iter_mut().enumerate() {
            *coeff = self.get(index + offset)?;
        }
        Ok(EF::from_basis_coefficients_slice(&coeffs).unwrap())
    }

    /// Get a continuous slice of extension field elements
    pub fn get_continuous_slice_of_ef_elements(
        &self,
        index: usize, // normal pointer
        len: usize,
    ) -> Result<Vec<EF>, RunnerError> {
        (0..len).map(|i| self.get_ef_element(index + i * DIMENSION)).collect()
    }

    /// Set an extension field element in memory
    pub fn set_ef_element(&mut self, index: usize, value: EF) -> Result<(), RunnerError> {
        for (i, v) in value.as_basis_coefficients_slice().iter().enumerate() {
            self.set(index + i, *v)?;
        }
        Ok(())
    }

    pub fn get_slice(&self, start: usize, len: usize) -> Result<Vec<F>, RunnerError> {
        (0..len).map(|i| self.get(start + i)).collect()
    }

    pub fn set_slice(&mut self, start: usize, values: &[F]) -> Result<(), RunnerError> {
        for (i, v) in values.iter().enumerate() {
            self.set(start + i, *v)?;
        }
        Ok(())
    }
}
