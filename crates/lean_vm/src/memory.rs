use crate::F;
use p3_field::BasedVectorSpace;
use p3_field::PrimeCharacteristicRing;
use rayon::prelude::*;

use crate::*;

pub(crate) const MAX_MEMORY_SIZE: usize = 1 << 24;

#[derive(Debug, Clone, Default)]
pub struct Memory(pub Vec<Option<F>>);

impl Memory {
    /// Creates a new memory instance, initializing it with public data.
    pub fn new(public_memory: Vec<F>) -> Self {
        Self(public_memory.into_par_iter().map(Some).collect())
    }

    /// Reads a single value from a memory address.
    ///
    /// Returns an error if the address is uninitialized.
    pub fn get(&self, index: usize) -> Result<F, RunnerError> {
        self.0
            .get(index)
            .copied()
            .flatten()
            .ok_or(RunnerError::UndefinedMemory)
    }

    pub fn set(&mut self, index: usize, value: F) -> Result<(), RunnerError> {
        if index >= self.0.len() {
            if index >= MAX_MEMORY_SIZE {
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

    pub fn get_vector(&self, index: usize) -> Result<[F; VECTOR_LEN], RunnerError> {
        Ok(self.get_vectorized_slice(index, 1)?.try_into().unwrap())
    }

    pub fn get_ef_element(&self, index: usize) -> Result<EF, RunnerError> {
        // index: non vectorized pointer
        let mut coeffs = [F::ZERO; DIMENSION];
        for i in 0..DIMENSION {
            coeffs[i] = self.get(index + i)?;
        }
        Ok(EF::from_basis_coefficients_slice(&coeffs).unwrap())
    }

    pub fn get_vectorized_slice(&self, index: usize, len: usize) -> Result<Vec<F>, RunnerError> {
        let start = index * VECTOR_LEN;
        let total_len = len * VECTOR_LEN;
        (0..total_len).map(|i| self.get(start + i)).collect()
    }

    pub fn get_continuous_slice_of_ef_elements(
        &self,
        index: usize, // normal pointer
        len: usize,
    ) -> Result<Vec<EF>, RunnerError> {
        (0..len)
            .map(|i| self.get_ef_element(index + i * DIMENSION))
            .collect()
    }

    pub fn slice(&self, index: usize, len: usize) -> Result<Vec<F>, RunnerError> {
        (0..len).map(|i| self.get(index + i)).collect()
    }

    pub fn set_ef_element(&mut self, index: usize, value: EF) -> Result<(), RunnerError> {
        for (i, v) in value.as_basis_coefficients_slice().iter().enumerate() {
            self.set(index + i, *v)?;
        }
        Ok(())
    }

    pub fn set_vector(&mut self, index: usize, value: [F; VECTOR_LEN]) -> Result<(), RunnerError> {
        for (i, v) in value.iter().enumerate() {
            let idx = VECTOR_LEN * index + i;
            self.set(idx, *v)?;
        }
        Ok(())
    }

    pub fn set_vectorized_slice(&mut self, index: usize, value: &[F]) -> Result<(), RunnerError> {
        assert!(value.len().is_multiple_of(VECTOR_LEN));
        let start = index * VECTOR_LEN;
        value
            .iter()
            .enumerate()
            .try_for_each(|(i, &v)| self.set(start + i, v))
    }
}
