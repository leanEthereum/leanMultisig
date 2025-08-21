use p3_field::{BasedVectorSpace, ExtensionField, PrimeCharacteristicRing};
use p3_symmetric::Permutation;
use rayon::prelude::*;
use utils::{build_poseidon16, build_poseidon24};

use crate::{
    DIMENSION, EF, F, POSEIDON_16_NULL_HASH_PTR, POSEIDON_24_NULL_HASH_PTR, PUBLIC_INPUT_START,
    RunnerError, ZERO_VEC_PTR,
};

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

#[must_use]
pub fn build_public_memory(public_input: &[F]) -> Vec<F> {
    // padded to a power of two
    let public_memory_len = (PUBLIC_INPUT_START + public_input.len()).next_power_of_two();
    let mut public_memory = F::zero_vec(public_memory_len);
    public_memory[PUBLIC_INPUT_START..][..public_input.len()].copy_from_slice(public_input);
    for pm in public_memory.iter_mut().take((ZERO_VEC_PTR + 2) * 8) {
        *pm = F::ZERO; // zero vector
    }
    public_memory[POSEIDON_16_NULL_HASH_PTR * 8..(POSEIDON_16_NULL_HASH_PTR + 2) * 8]
        .copy_from_slice(&build_poseidon16().permute([F::ZERO; 16]));
    public_memory[POSEIDON_24_NULL_HASH_PTR * 8..(POSEIDON_24_NULL_HASH_PTR + 1) * 8]
        .copy_from_slice(&build_poseidon24().permute([F::ZERO; 24])[16..]);
    public_memory
}
