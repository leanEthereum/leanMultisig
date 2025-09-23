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
    pub const fn size(&self) -> usize {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_memory_operations() {
        let mut memory = Memory::empty();

        // Test setting and getting values
        memory.set(0, F::ONE).unwrap();
        memory.set(5, F::from_usize(42)).unwrap();

        assert_eq!(memory.get(0).unwrap(), F::ONE);
        assert_eq!(memory.get(5).unwrap(), F::from_usize(42));

        // Test undefined memory access
        assert!(matches!(memory.get(1), Err(RunnerError::UndefinedMemory)));
    }

    #[test]
    fn test_memory_already_set_error() {
        let mut memory = Memory::empty();

        memory.set(0, F::ONE).unwrap();
        // Setting same value should work
        memory.set(0, F::ONE).unwrap();

        // Setting different value should fail
        assert!(matches!(
            memory.set(0, F::ZERO),
            Err(RunnerError::MemoryAlreadySet)
        ));
    }

    #[test]
    fn test_memory_slices() {
        let mut memory = Memory::empty();
        let values = vec![F::ONE, F::ZERO, F::from_usize(42), F::from_usize(100)];

        memory.set_slice(10, &values).unwrap();
        let retrieved = memory.get_slice(10, 4).unwrap();

        assert_eq!(retrieved, values);
    }

    #[test]
    fn test_memory_initialization_and_utilities() {
        let public_data = vec![F::ONE, F::ZERO, F::from_usize(123)];
        let memory = Memory::new(public_data.clone());

        // All public data should be initialized
        for (i, expected) in public_data.iter().enumerate() {
            assert!(memory.is_initialized(i));
            assert_eq!(memory.get(i).unwrap(), *expected);
        }

        assert_eq!(memory.size(), 3);

        let entries = memory.initialized_entries();
        assert_eq!(entries.len(), 3);
        assert_eq!(entries[0], (0, F::ONE));
        assert_eq!(entries[2], (2, F::from_usize(123)));
    }

    #[test]
    fn test_vectorized_operations() {
        let mut memory = Memory::empty();
        let vector = [F::ONE; VECTOR_LEN];

        memory.set_vector(0, vector).unwrap();
        let retrieved = memory.get_vector(0).unwrap();

        assert_eq!(retrieved, vector);

        // Test vectorized slice
        let slice_data = vec![F::from_usize(1); 2 * VECTOR_LEN];
        memory.set_vectorized_slice(1, &slice_data).unwrap();
        let retrieved_slice = memory.get_vectorized_slice(1, 2).unwrap();

        assert_eq!(retrieved_slice, slice_data);
    }

    #[test]
    fn test_extension_field_operations() {
        let mut memory = Memory::empty();

        // Create a simple extension field element with proper dimension
        let mut coeffs = [F::ZERO; DIMENSION];
        coeffs[0] = F::ONE;
        let ef_value = EF::from_basis_coefficients_slice(&coeffs).unwrap();

        memory.set_ef_element(0, ef_value).unwrap();
        let retrieved = memory.get_ef_element(0).unwrap();

        assert_eq!(retrieved, ef_value);

        // Test continuous slice of EF elements
        memory.set_ef_element(DIMENSION, ef_value).unwrap();
        let ef_slice = memory.get_continuous_slice_of_ef_elements(0, 2).unwrap();

        assert_eq!(ef_slice.len(), 2);
        assert_eq!(ef_slice[0], ef_value);
        assert_eq!(ef_slice[1], ef_value);
    }

    #[test]
    fn test_memory_clear() {
        let mut memory = Memory::new(vec![F::ONE, F::ZERO]);
        assert_eq!(memory.size(), 2);

        memory.clear();
        assert_eq!(memory.size(), 0);
    }
}
