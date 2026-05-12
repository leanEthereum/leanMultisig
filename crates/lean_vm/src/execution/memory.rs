use crate::MAX_LOG_MEMORY_SIZE;
use crate::core::{DIMENSION, EF, F};
use crate::diagnostics::RunnerError;
use crate::tables::SlotColumn;
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

/// Write-once VM memory.
///
/// `values` is a `SlotColumn` so it can be either:
/// - `Owned`: a regular `Vec<F>` that grows on demand (the default, used by the runner CLI, tests,
///   etc.). Internally indistinguishable from the previous `Vec<F>` representation.
/// - `Slot`: a borrowed slice into the prover's pre-allocated stacked WHIR polynomial. In that
///   mode the cap is fixed to the predicted padded memory size; every `set` lands directly in
///   the final committed buffer with no later memcpy.
#[derive(Debug, Default)]
pub struct Memory {
    pub values: SlotColumn,
    pub written: Vec<bool>,
}

impl Clone for Memory {
    fn clone(&self) -> Self {
        Self {
            values: self.values.clone(),
            written: self.written.clone(),
        }
    }
}

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
        let written = vec![true; public_memory.len()];
        Self {
            values: SlotColumn::Owned(public_memory),
            written,
        }
    }

    /// Construct a slot-backed memory: `values` is borrowed from `slot` (capacity = `slot.len()`),
    /// initialized with `public_memory` copied into `[0, public_memory.len())`. `written` is owned
    /// and grows / shrinks alongside `values`'s logical length.
    ///
    /// # Safety
    /// `slot` must outlive every operation on the returned `Memory`.
    pub unsafe fn new_in_slot(slot: &mut [F], public_memory: &[F]) -> Self {
        assert!(slot.len() >= public_memory.len());
        slot[..public_memory.len()].copy_from_slice(public_memory);
        // SAFETY: positions `0..public_memory.len()` were just initialized by `copy_from_slice`.
        let values = unsafe { SlotColumn::from_slot_with_len(slot, public_memory.len()) };
        let written = vec![true; public_memory.len()];
        Self { values, written }
    }

    pub fn len(&self) -> usize {
        self.values.len()
    }

    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    pub fn resize(&mut self, new_len: usize) {
        self.values.resize(new_len, F::ZERO);
        self.written.resize(new_len, false);
    }

    pub fn is_set(&self, index: usize) -> bool {
        index < self.written.len() && self.written[index]
    }

    pub fn get(&self, index: usize) -> Result<F, RunnerError> {
        if index < self.written.len() && self.written[index] {
            Ok(self.values[index])
        } else {
            Err(RunnerError::UndefinedMemory(index))
        }
    }

    pub fn set(&mut self, index: usize, value: F) -> Result<(), RunnerError> {
        if index >= self.values.len() {
            if index >= 1 << MAX_LOG_MEMORY_SIZE {
                return Err(RunnerError::OutOfMemory);
            }
            self.resize(index + 1);
        }
        if self.written[index] {
            let existing = self.values[index];
            if existing != value {
                return Err(RunnerError::MemoryAlreadySet {
                    address: index,
                    prev_value: existing,
                    new_value: value,
                });
            }
        } else {
            self.values[index] = value;
            self.written[index] = true;
        }
        Ok(())
    }

    pub fn num_cells_used(&self) -> usize {
        self.written.par_iter().filter(|&&w| w).count()
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
    shared_values: &'a [F],
    shared_written: &'a [bool],
    segment_values: &'a mut [F],
    segment_written: &'a mut [bool],
    segment_start: usize,
    deferred_writes: Vec<(usize, F)>,
}

impl<'a> SegmentMemory<'a> {
    pub fn new(
        shared_values: &'a [F],
        shared_written: &'a [bool],
        segment_values: &'a mut [F],
        segment_written: &'a mut [bool],
        segment_start: usize,
    ) -> Self {
        debug_assert_eq!(shared_values.len(), shared_written.len());
        debug_assert_eq!(segment_values.len(), segment_written.len());
        Self {
            shared_values,
            shared_written,
            segment_values,
            segment_written,
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
            if index < self.shared_written.len() && self.shared_written[index] {
                Ok(self.shared_values[index])
            } else {
                Err(RunnerError::UndefinedMemory(index))
            }
        } else {
            let offset = index - self.segment_start;
            if offset < self.segment_written.len() && self.segment_written[offset] {
                Ok(self.segment_values[offset])
            } else {
                Err(RunnerError::UndefinedMemory(index))
            }
        }
    }

    fn set(&mut self, index: usize, value: F) -> Result<(), RunnerError> {
        let Some(offset) = index
            .checked_sub(self.segment_start)
            .filter(|&o| o < self.segment_values.len())
        else {
            self.deferred_writes.push((index, value));
            return Ok(());
        };
        if self.segment_written[offset] {
            let existing = self.segment_values[offset];
            if existing != value {
                return Err(RunnerError::MemoryAlreadySet {
                    address: index,
                    prev_value: existing,
                    new_value: value,
                });
            }
        } else {
            self.segment_values[offset] = value;
            self.segment_written[offset] = true;
        }
        Ok(())
    }
}
