//! Memory management for the VM

use crate::core::{DIMENSION, EF, F, MAX_RUNNER_MEMORY_SIZE, VECTOR_LEN};
use crate::diagnostics::RunnerError;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
use rayon::prelude::*;

pub const MIN_LOG_MEMORY_SIZE: usize = 16;
pub const MAX_LOG_MEMORY_SIZE: usize = 29;

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
            .ok_or(RunnerError::UndefinedMemory)
    }

    /// Sets a value at a memory address
    ///
    /// Returns an error if the address is already set to a different value
    /// or if we exceed memory limits
    pub fn set(&mut self, index: usize, value: F) -> Result<(), RunnerError> {
        if index >= self.0.len() {
            if index >= MAX_RUNNER_MEMORY_SIZE {
                return Err(RunnerError::OutOfMemory);
            }
            self.0.resize(index + 1, None);
        }
        if let Some(existing) = &mut self.0[index] {
            if *existing != value {
                return Err(RunnerError::MemoryAlreadySet);
            }
        } else {
            self.0[index] = Some(value);
        }
        Ok(())
    }

    /// Reads a slice of memory values
    pub fn get_slice(&self, start: usize, len: usize) -> Result<Vec<F>, RunnerError> {
        (start..start + len).map(|i| self.get(i)).collect()
    }

    /// Sets a slice of memory values
    pub fn set_slice(&mut self, start: usize, values: &[F]) -> Result<(), RunnerError> {
        for (i, &value) in values.iter().enumerate() {
            self.set(start + i, value)?;
        }
        Ok(())
    }

    /// Gets the current size of allocated memory
    pub fn size(&self) -> usize {
        self.0.len()
    }

    /// Checks if a memory address is initialized
    pub fn is_initialized(&self, index: usize) -> bool {
        self.0.get(index).and_then(|x| x.as_ref()).is_some()
    }

    /// Gets all initialized memory addresses and their values
    pub fn initialized_entries(&self) -> Vec<(usize, F)> {
        self.0
            .iter()
            .enumerate()
            .filter_map(|(i, opt)| opt.map(|v| (i, v)))
            .collect()
    }

    /// Clears all memory
    pub fn clear(&mut self) {
        self.0.clear();
    }

    /// Get a vector from vectorized memory
    pub fn get_vector(&self, index: usize) -> Result<[F; VECTOR_LEN], RunnerError> {
        Ok(self.get_vectorized_slice(index, 1)?.try_into().unwrap())
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

    /// Get a vectorized slice from memory
    pub fn get_vectorized_slice(&self, index: usize, len: usize) -> Result<Vec<F>, RunnerError> {
        let start = index * VECTOR_LEN;
        let total_len = len * VECTOR_LEN;
        (0..total_len).map(|i| self.get(start + i)).collect()
    }

    /// Get a continuous slice of extension field elements
    pub fn get_continuous_slice_of_ef_elements(
        &self,
        index: usize, // normal pointer
        len: usize,
    ) -> Result<Vec<EF>, RunnerError> {
        (0..len)
            .map(|i| self.get_ef_element(index + i * DIMENSION))
            .collect()
    }

    /// Set an extension field element in memory
    pub fn set_ef_element(&mut self, index: usize, value: EF) -> Result<(), RunnerError> {
        for (i, v) in value.as_basis_coefficients_slice().iter().enumerate() {
            self.set(index + i, *v)?;
        }
        Ok(())
    }

    /// Set a vector in vectorized memory
    pub fn set_vector(&mut self, index: usize, value: [F; VECTOR_LEN]) -> Result<(), RunnerError> {
        for (i, v) in value.iter().enumerate() {
            let idx = VECTOR_LEN * index + i;
            self.set(idx, *v)?;
        }
        Ok(())
    }

    /// Set a vectorized slice in memory
    pub fn set_vectorized_slice(&mut self, index: usize, value: &[F]) -> Result<(), RunnerError> {
        assert!(value.len().is_multiple_of(VECTOR_LEN));
        let start = index * VECTOR_LEN;
        value
            .iter()
            .enumerate()
            .try_for_each(|(i, &v)| self.set(start + i, v))
    }

    /// Get a slice from memory for multilinear evaluation
    pub fn slice(&self, start: usize, len: usize) -> Result<Vec<F>, RunnerError> {
        (0..len).map(|i| self.get(start + i)).collect()
    }
}
