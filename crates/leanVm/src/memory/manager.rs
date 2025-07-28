use p3_field::PrimeField64;

use super::{address::MemoryAddress, mem::Memory, val::MemoryValue};
use crate::errors::memory::MemoryError;

/// A high level manager for the memory.
#[derive(Debug, Default)]
pub struct MemoryManager {
    pub memory: Memory,
}

impl MemoryManager {
    /// Returns the number of currently allocated segments in memory.
    ///
    /// This reflects the actual physical segment count, starting from segment index 0.
    ///
    /// # Returns
    /// * `usize` — the number of segments allocated in `self.memory`.
    #[must_use]
    pub fn num_segments(&self) -> usize {
        self.memory.data.len()
    }

    /// Adds a new, empty segment to memory and returns its starting address.
    ///
    /// This operation appends an empty segment to the memory, which starts at offset 0.
    /// The returned `MemoryAddress` corresponds to the beginning of that segment.
    ///
    /// # Returns
    /// * `MemoryAddress` — the starting address (segment_index, offset=0) of the new segment.
    pub fn add(&mut self) -> MemoryAddress {
        // Allocate a new, empty segment at the end of the list.
        self.memory.data.push(Vec::new());

        // Compute the index of the newly created segment.
        let new_segment_index = self.memory.data.len() - 1;

        // Return the starting address of the new segment (offset always 0).
        MemoryAddress {
            segment_index: new_segment_index,
            offset: 0,
        }
    }

    /// Loads a slice of data into memory starting from a given address.
    ///
    /// The function writes each value in `data` to consecutive addresses starting
    /// from `ptr`. The write is done in reverse order to ensure that any required
    /// memory extension happens once at the end rather than multiple times.
    ///
    /// If all values are written successfully, the function returns the first
    /// address **after** the last inserted value.
    ///
    /// # Type Parameters
    /// * `F`: A finite field, used as the scalar type.
    ///
    /// # Arguments
    /// * `ptr`: Starting address where the data should be written.
    /// * `data`: A slice of memory values representing the values to be stored.
    ///
    /// # Returns
    /// * `Ok(MemoryAddress)` — the address immediately following the last written value.
    /// * `Err(MemoryError<F>)` — if writing fails due to:
    ///     - Memory cell already initialized with a different value.
    ///     - Overflow when computing addresses.
    ///     - Exceeding vector capacity.
    pub fn load_data<F>(
        &mut self,
        ptr: MemoryAddress,
        data: &[MemoryValue<F>],
    ) -> Result<MemoryAddress, MemoryError<F>>
    where
        F: PrimeField64,
    {
        // Iterate over the data values in reverse order, with indices.
        //
        // This reverse order allows any required memory segment resizing
        // (e.g., length extension or capacity reservation) to occur *once*
        // at the highest offset instead of repeatedly during writes.
        for (num, value) in data.iter().enumerate().rev() {
            // Compute the target address: ptr + num.
            //
            // This operation may fail if it causes overflow.
            let addr = ptr.add_usize(num).map_err(MemoryError::Math)?;

            // Attempt to write the value into memory at the computed address.
            //
            // This enforces the write-once rule — it will fail if the cell is already
            // initialized with a different value.
            self.memory.insert(addr, value.clone())?;
        }

        // After writing all values, compute and return the address after the last item.
        //
        // This is simply ptr + data.len(), and it may also fail on overflow.
        ptr.add_usize(data.len()).map_err(MemoryError::Math)
    }

    /// Retrieves the value stored at a given memory address.
    #[must_use]
    pub fn get<F>(&self, address: MemoryAddress) -> Option<MemoryValue<F>>
    where
        F: PrimeField64,
    {
        self.memory.get(address)
    }
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;
    use p3_field::PrimeCharacteristicRing;

    use super::*;
    use crate::{errors::math::MathError, memory::cell::MemoryCell};

    type F = BabyBear;

    #[test]
    fn test_add_segment_returns_correct_address() {
        // Create a new empty memory manager.
        let mut manager = MemoryManager::default();

        // Initially, there should be no segments.
        assert_eq!(manager.num_segments(), 0);

        // Add the first memory segment.
        let addr1 = manager.add();

        // The first segment should have index 0, starting at offset 0.
        assert_eq!(addr1.segment_index, 0);
        assert_eq!(addr1.offset, 0);

        // After adding, the total number of segments should be 1.
        assert_eq!(manager.num_segments(), 1);

        // Add another segment.
        let addr2 = manager.add();

        // The second segment should have index 1, also starting at offset 0.
        assert_eq!(addr2.segment_index, 1);
        assert_eq!(addr2.offset, 0);

        // Now there should be exactly 2 segments.
        assert_eq!(manager.num_segments(), 2);
    }

    #[test]
    fn test_load_data_successful() {
        // Create a new memory manager.
        let mut manager = MemoryManager::default();

        // Add a memory segment and get its starting address.
        let base_addr = manager.add(); // segment_index = 0, offset = 0

        // Prepare a list of memory values to load.
        let values = vec![
            MemoryValue::Int(F::from_u64(10)),
            MemoryValue::Int(F::from_u64(20)),
            MemoryValue::Int(F::from_u64(30)),
        ];

        // Load the data into memory starting at base_addr.
        let end_addr = manager.load_data(base_addr, &values).unwrap();

        // The returned end address should be immediately after the last inserted value.
        assert_eq!(end_addr.segment_index, base_addr.segment_index);
        assert_eq!(end_addr.offset, base_addr.offset + values.len());

        // Verify that each value was inserted correctly at its expected offset.
        for (i, expected) in values.iter().enumerate() {
            let addr = MemoryAddress {
                segment_index: base_addr.segment_index,
                offset: base_addr.offset + i,
            };
            assert_eq!(manager.memory.get(addr), Some(expected.clone()));
        }
    }

    #[test]
    fn test_load_data_returns_math_error_on_address_overflow() {
        // Create a new memory manager.
        let mut manager = MemoryManager::default();

        // Define a starting address where the offset is at the maximum `usize` value.
        let base_addr = MemoryAddress {
            segment_index: 0,
            offset: usize::MAX,
        };

        // Manually push an empty segment to allow writing into segment 0.
        manager.memory.data.push(Vec::new());

        // Create two values to write: this will cause an overflow.
        let values = vec![
            MemoryValue::Int(F::from_u64(1)),
            MemoryValue::Int(F::from_u64(2)),
        ];

        // Try to load data starting at MAX offset.
        //
        // This should fail with an overflow error.
        let err = manager.load_data(base_addr, &values).unwrap_err();

        // Confirm that the error is a MathError due to offset overflow.
        match err {
            MemoryError::Math(MathError::MemoryAddressAddUsizeOffsetExceeded(boxed)) => {
                let (addr, delta) = *boxed;
                // original address
                assert_eq!(addr, base_addr);
                // the amount that caused overflow
                assert_eq!(delta, 1);
            }
            other => panic!("Unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_load_data_partial_write_does_not_corrupt_memory() {
        // Create a new memory manager.
        let mut manager = MemoryManager::default();

        // Add a segment (segment_index = 0).
        let _ = manager.add();

        // Construct values to insert. The second will cause a failure.
        let values = vec![
            MemoryValue::Int(F::from_u64(1)),
            MemoryValue::Int(F::from_u64(2)),
        ];

        // Set the starting address such that adding even one to it will cause overflow.
        let failing_addr = MemoryAddress {
            segment_index: 0,
            offset: usize::MAX - 1,
        };

        // Simulate a memory segment with a small preallocated length.
        manager.memory.data[0] = vec![MemoryCell::NONE; 4];

        // Attempt to load the data starting at the failing address.
        // This should fail due to memory limitations.
        let err = manager.load_data(failing_addr, &values).unwrap_err();

        // Confirm the error is due to exceeding vector capacity.
        assert!(matches!(err, MemoryError::VecCapacityExceeded));
    }
}
