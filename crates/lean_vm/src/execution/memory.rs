use crate::MAX_LOG_MEMORY_SIZE;
use crate::core::{DIMENSION, EF, F};
use crate::diagnostics::RunnerError;
use backend::*;

pub trait MemoryAccess {
    fn get(&self, index: usize) -> Result<F, RunnerError>;
    fn set(&mut self, index: usize, value: F) -> Result<(), RunnerError>;

    fn get_slice(&self, start: usize, len: usize) -> Result<Vec<F>, RunnerError> {
        (0..len).map(|i| self.get(start + i)).collect()
    }

    fn set_slice(&mut self, start: usize, values: &[F]) -> Result<(), RunnerError> {
        for (i, v) in values.iter().enumerate() {
            self.set(start + i, *v)?;
        }
        Ok(())
    }

    fn get_ef_element(&self, index: usize) -> Result<EF, RunnerError> {
        let mut coeffs = [F::ZERO; DIMENSION];
        for (offset, coeff) in coeffs.iter_mut().enumerate() {
            *coeff = self.get(index + offset)?;
        }
        Ok(EF::from_basis_coefficients_slice(&coeffs).unwrap())
    }

    fn set_ef_element(&mut self, index: usize, value: EF) -> Result<(), RunnerError> {
        for (i, v) in value.as_basis_coefficients_slice().iter().enumerate() {
            self.set(index + i, *v)?;
        }
        Ok(())
    }

    fn get_continuous_slice_of_ef_elements(&self, index: usize, len: usize) -> Result<Vec<EF>, RunnerError> {
        (0..len).map(|i| self.get_ef_element(index + i * DIMENSION)).collect()
    }

    fn make_slices_equal_and_defined(&mut self, ptr_0: usize, ptr_1: usize, len: usize) -> Result<(), RunnerError> {
        for i in 0..len {
            match (self.get(ptr_0 + i), self.get(ptr_1 + i)) {
                (Ok(v0), Ok(v1)) => {
                    if v0 != v1 {
                        return Err(RunnerError::NotEqual(v0, v1));
                    }
                }
                (Ok(v), Err(_)) => {
                    self.set(ptr_1 + i, v)?;
                }
                (Err(_), Ok(v)) => {
                    self.set(ptr_0 + i, v)?;
                }
                (Err(_), Err(_)) => {
                    // Both are unknown, we set to zeros (arbitrary, maybe we need to revisit this later)
                    self.set(ptr_0 + i, F::ZERO)?;
                    self.set(ptr_1 + i, F::ZERO)?;
                }
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Default)]
pub struct Memory(pub Vec<Option<F>>);

impl MemoryAccess for Memory {
    fn get(&self, index: usize) -> Result<F, RunnerError> {
        self.get(index)
    }

    fn set(&mut self, index: usize, value: F) -> Result<(), RunnerError> {
        self.set(index, value)
    }
}

impl Memory {
    pub fn new(public_memory: Vec<F>) -> Self {
        Self(public_memory.into_par_iter().map(Some).collect())
    }

    pub fn get(&self, index: usize) -> Result<F, RunnerError> {
        self.0
            .get(index)
            .copied()
            .flatten()
            .ok_or(RunnerError::UndefinedMemory(index))
    }

    pub fn set(&mut self, index: usize, value: F) -> Result<(), RunnerError> {
        if index >= self.0.len() {
            if index >= 1 << MAX_LOG_MEMORY_SIZE {
                return Err(RunnerError::OutOfMemory);
            }
            self.0.resize(index + 1, None);
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
}

/// A segmented view into VM memory for parallel execution.
///
/// |--------- shared (read-only) ---------|-- seg 1 --|-- seg 2 --|-- ... --|-- seg N --|
///                                        ^                       ^
/// 0                                  split_at              this segment's
///                                                       exclusive &mut slice
///
/// - `shared`: `[0, split_at)` — pre-batch data + iteration 0's completed frame.
///   Fully written before segments are created. Immutable borrow, safe for all to read.
/// - `segment`: `[segment_start, segment_start + len)` — this segment's exclusive frame.
/// - Reads outside both → `UndefinedMemory` (speculative Deref into another segment's
///   frame gracefully fails; resolved by `resolve_deref_hints`).
/// - Writes outside `segment` → deferred, applied sequentially after the parallel phase.
#[derive(Debug)]
pub struct SegmentMemory<'a> {
    shared: &'a [Option<F>],
    segment: &'a mut [Option<F>],
    segment_start: usize,
    deferred_writes: Vec<(usize, F)>,
}

impl<'a> SegmentMemory<'a> {
    pub fn new(shared: &'a [Option<F>], segment: &'a mut [Option<F>], segment_start: usize) -> Self {
        Self {
            shared,
            segment,
            segment_start,
            deferred_writes: Vec::new(),
        }
    }

    pub fn into_deferred_writes(self) -> Vec<(usize, F)> {
        self.deferred_writes
    }
}

impl MemoryAccess for SegmentMemory<'_> {
    fn get(&self, index: usize) -> Result<F, RunnerError> {
        if index < self.segment_start {
            self.shared
                .get(index)
                .copied()
                .flatten()
                .ok_or(RunnerError::UndefinedMemory(index))
        } else {
            let offset = index - self.segment_start;
            if offset < self.segment.len() {
                self.segment[offset].ok_or(RunnerError::UndefinedMemory(index))
            } else {
                Err(RunnerError::UndefinedMemory(index))
            }
        }
    }

    fn set(&mut self, index: usize, value: F) -> Result<(), RunnerError> {
        let in_segment = index >= self.segment_start && (index - self.segment_start) < self.segment.len();
        if !in_segment {
            self.deferred_writes.push((index, value));
            return Ok(());
        }
        {
            let offset = index - self.segment_start;
            if let Some(existing) = self.segment[offset] {
                if existing != value {
                    return Err(RunnerError::MemoryAlreadySet {
                        address: index,
                        prev_value: existing,
                        new_value: value,
                    });
                }
            } else {
                self.segment[offset] = Some(value);
            }
            Ok(())
        }
    }
}
