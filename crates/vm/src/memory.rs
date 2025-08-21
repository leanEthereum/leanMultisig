use p3_field::{BasedVectorSpace, ExtensionField};
use rayon::prelude::*;

use crate::{DIMENSION, EF, F, RunnerError};

pub(crate) const MAX_MEMORY_SIZE: usize = 1 << 23;

#[derive(Debug, Clone, Default)]
pub struct Memory(pub Vec<Option<F>>);

impl Memory {
    pub fn new(public_memory: Vec<F>) -> Self {
        Self(public_memory.into_par_iter().map(Some).collect())
    }

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

    pub fn get_vector(&self, index: usize) -> Result<[F; DIMENSION], RunnerError> {
        Ok(self.get_vectorized_slice(index, 1)?.try_into().unwrap())
    }

    pub fn get_extension(&self, index: usize) -> Result<EF, RunnerError> {
        Ok(EF::from_basis_coefficients_slice(&self.get_vector(index)?).unwrap())
    }

    pub fn get_vectorized_slice(&self, index: usize, len: usize) -> Result<Vec<F>, RunnerError> {
        let mut vector = Vec::with_capacity(len * DIMENSION);
        for i in 0..len * DIMENSION {
            vector.push(self.get(index * DIMENSION + i)?);
        }
        Ok(vector)
    }

    pub fn get_vectorized_slice_extension<EF: ExtensionField<F>>(
        &self,
        index: usize,
        len: usize,
    ) -> Result<Vec<EF>, RunnerError> {
        let mut vector = Vec::with_capacity(len);
        for i in 0..len {
            let v = self.get_vector(index + i)?;
            vector.push(EF::from_basis_coefficients_slice(&v).unwrap());
        }
        Ok(vector)
    }

    pub fn slice(&self, index: usize, len: usize) -> Result<Vec<F>, RunnerError> {
        (0..len).map(|i| self.get(index + i)).collect()
    }

    pub fn set_vector(&mut self, index: usize, value: [F; DIMENSION]) -> Result<(), RunnerError> {
        value
            .iter()
            .enumerate()
            .try_for_each(|(i, &v)| self.set(index * DIMENSION + i, v))
    }

    pub fn set_vectorized_slice(&mut self, index: usize, value: &[F]) -> Result<(), RunnerError> {
        assert!(value.len().is_multiple_of(DIMENSION));
        value
            .iter()
            .enumerate()
            .try_for_each(|(i, &v)| self.set(index * DIMENSION + i, v))
    }
}
