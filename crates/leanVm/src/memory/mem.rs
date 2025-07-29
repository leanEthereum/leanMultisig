use p3_field::PrimeField64;

use super::{address::MemoryAddress, cell::MemoryCell, val::MemoryValue};
use crate::errors::memory::MemoryError;

#[derive(Debug, Default)]
pub struct Memory {
    pub(crate) data: Vec<Vec<MemoryCell>>,
}

impl Memory {
    /// Inserts a value into a specific memory address, handling segment allocation and write-once logic.
    ///
    /// This function acts as the primary way to write data to the VM's memory. It ensures that memory
    /// segments are correctly sized to accommodate new values and enforces the rule that a memory cell,
    /// once written, cannot be altered.
    ///
    /// # Type Parameters
    /// * `V`: A generic type that can be converted into a `MemoryValue<F>`. This allows for flexible
    ///   insertion of different kinds of values (e.g., raw field elements, addresses).
    /// * `F`: The `PrimeField64` type used for integer values in memory.
    ///
    /// # Arguments
    /// * `address`: The `MemoryAddress` where the value should be stored.
    /// * `value`: The value to insert, which will be converted into a `MemoryValue<F>`.
    ///
    /// # Returns
    /// * `Ok(())` on successful insertion.
    /// * `Err(MemoryError)` if:
    ///   - The `address.segment_index` points to a segment that has not been allocated.
    ///   - The cell at the `address` already contains a different value.
    ///   - The operation would cause the memory segment to exceed its maximum capacity.
    pub fn insert<V, F>(&mut self, address: MemoryAddress, value: V) -> Result<(), MemoryError<F>>
    where
        F: PrimeField64,
        MemoryValue<F>: From<V>,
    {
        // Convert the input `value` into the canonical `MemoryValue` enum.
        let value = MemoryValue::from(value);
        // Destructure the address into its constituent parts for easier access.
        let MemoryAddress {
            segment_index,
            offset,
        } = address;

        // Attempt to get a mutable reference to the target segment.
        //
        // If the segment index is out of bounds, return an `UnallocatedSegment` error.
        let segment = self
            .data
            .get_mut(segment_index)
            .ok_or_else(|| MemoryError::UnallocatedSegment(Box::new((segment_index, offset))))?;

        // Check if the target offset is outside the current bounds of the segment.
        if segment.len() <= offset {
            // If so, the segment needs to be extended. Calculate the required new length.
            //
            // `checked_add` prevents an integer overflow if the offset is `usize::MAX`.
            let new_len = offset
                .checked_add(1)
                .ok_or(MemoryError::VecCapacityExceeded)?;

            // Efficiently reserve additional capacity if needed before resizing.
            segment
                .try_reserve(new_len.saturating_sub(segment.capacity()))
                .map_err(|_| MemoryError::VecCapacityExceeded)?;

            // Resize the segment, filling any new, intermediate cells with `MemoryCell::NONE`.
            segment.resize(new_len, MemoryCell::NONE);
        }

        // Now that the segment is guaranteed to be long enough, access the target cell.
        // The `value()` method checks the cell's `NONE` flag.
        match segment[offset].value() {
            // If the cell is empty (`None`), we can write the new value.
            None => segment[offset] = MemoryCell::from(value),
            // If the cell already has a value (`Some`), we must check if it's the same.
            Some(current_cell) => {
                // If the existing value is different from the new one, it's an error.
                if current_cell != value {
                    // Return an error to enforce the write-once, immutable memory rule.
                    return Err(MemoryError::InconsistentMemory(Box::new((
                        address,
                        current_cell,
                        value,
                    ))));
                }
                // If the values are the same, do nothing. The operation is idempotent.
            }
        }

        // If all checks pass and the value is written (or was already present), return Ok.
        Ok(())
    }

    /// Retrieves the value stored at a given memory address.
    ///
    /// This is a read-only operation that safely checks for the existence of a value
    /// without causing any side effects or panics. It's the primary way to read
    /// from memory in a fallible manner.
    ///
    /// # Arguments
    /// * `address`: The `MemoryAddress` specifying the location to read from.
    ///
    /// # Returns
    /// An `Option<MemoryValue<F>>` containing the value if found. This will be:
    /// - `Some(MemoryValue<F>)` if the address is valid and the cell is initialized.
    /// - `None` if the segment index is out of bounds, the offset is out of bounds
    ///   for the given segment, or the memory cell at the address is uninitialized (`NONE`).
    pub(crate) fn get<F>(&self, address: MemoryAddress) -> Option<MemoryValue<F>>
    where
        F: PrimeField64,
        MemoryValue<F>: From<MemoryCell>,
    {
        let MemoryAddress {
            segment_index,
            offset,
        } = address;

        // The following chain of operations safely retrieves the value. It will short-circuit
        // and return `None` at the first step that fails:
        // 1. `None` if the segment does not exist.
        // 2. `None` if the offset is out of bounds for the segment.
        // 3. `None` if the memory cell is present but uninitialized (is `NONE`).
        self.data
            .get(segment_index)
            .and_then(|segment| segment.get(offset))
            .and_then(|mem_cell| mem_cell.value())
    }

    /// Retrieves a fixed-size array of field elements starting from a given address.
    ///
    /// This function reads `DIM` consecutive memory cells starting from `start_address`,
    /// expecting each cell to contain an integer (`MemoryValue::Int`). It's a generic
    /// way to perform the "vectorized memory access". We need to check further if it is better
    /// to use vectorized memory cells directly.
    ///
    /// # Arguments
    /// * `start_address`: The `MemoryAddress` of the first element of the vector.
    pub(crate) fn get_array<F, const DIM: usize>(
        &self,
        start_address: MemoryAddress,
    ) -> Result<[MemoryValue<F>; DIM], MemoryError<F>>
    where
        F: PrimeField64,
    {
        // Initialize an array to store the result.
        let mut result = [MemoryValue::default(); DIM];

        // Iterate from 0 to DIM-1 to read each element of the vector.
        for (i, res) in result.iter_mut().enumerate().take(DIM) {
            // Calculate the address of the current element by adding the index `i` to the start offset.
            let current_addr = start_address.add_usize(i).map_err(MemoryError::Math)?;

            // Retrieve the value from the calculated address.
            let mem_val = self
                .get(current_addr)
                .ok_or(MemoryError::UninitializedMemory(current_addr))?;

            // Assign the validated field element to the result array.
            *res = mem_val;
        }

        // Return the completed array.
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;
    use p3_field::PrimeCharacteristicRing;

    use super::*;

    type F = BabyBear;

    /// Helper function to create a Memory instance with a specified number of empty segments.
    fn create_memory_with_segments(num_segments: usize) -> Memory {
        let mut memory = Memory::default();
        for _ in 0..num_segments {
            memory.data.push(Vec::new());
        }
        memory
    }

    #[test]
    fn test_insert_successful_at_start_of_segment() {
        let mut memory = create_memory_with_segments(1);
        let addr = MemoryAddress {
            segment_index: 0,
            offset: 0,
        };
        let val = MemoryValue::<F>::Int(F::from_u64(100));

        assert!(memory.insert(addr, val).is_ok());
        assert_eq!(memory.get(addr), Some(val));
    }

    #[test]
    fn test_insert_successful_at_offset_creates_gap() {
        let mut memory = create_memory_with_segments(1);
        let addr = MemoryAddress {
            segment_index: 0,
            offset: 5,
        };
        let val = MemoryValue::<F>::Int(F::from_u64(200));

        assert!(memory.insert(addr, val).is_ok());

        // Verify the segment was resized and padded with NONE.
        assert_eq!(memory.data[0].len(), 6);
        assert!(memory.data[0][4].is_none());
        assert!(memory.data[0][5].is_some());

        // Verify the inserted value and a value in the gap.
        assert_eq!(memory.get(addr), Some(val));
        assert_eq!(
            memory.get::<F>(MemoryAddress {
                segment_index: 0,
                offset: 3
            }),
            None
        );
    }

    #[test]
    fn test_insert_same_value_is_ok() {
        let mut memory = create_memory_with_segments(1);
        let addr = MemoryAddress {
            segment_index: 0,
            offset: 2,
        };
        let val = MemoryValue::<F>::Int(F::from_u64(300));

        // First insert should succeed.
        assert!(memory.insert(addr, val).is_ok());
        // Inserting the exact same value again should also succeed.
        assert!(memory.insert(addr, val).is_ok());

        assert_eq!(memory.get(addr), Some(val));
    }

    #[test]
    fn test_insert_fails_on_unallocated_segment() {
        let mut memory = create_memory_with_segments(1); // Only segment 0 exists.
        let addr = MemoryAddress {
            segment_index: 1,
            offset: 0,
        };
        let val = MemoryValue::<F>::Int(F::from_u64(400));

        let err = memory.insert(addr, val).unwrap_err();
        assert_eq!(err, MemoryError::UnallocatedSegment(Box::new((1, 0))));
    }

    #[test]
    fn test_insert_fails_on_inconsistent_write() {
        let mut memory = create_memory_with_segments(1);
        let addr = MemoryAddress {
            segment_index: 0,
            offset: 0,
        };
        let val1 = MemoryValue::<F>::Int(F::from_u64(500));
        let val2 = MemoryValue::<F>::Int(F::from_u64(600));

        // First write is OK.
        memory.insert(addr, val1).unwrap();

        // Second write with a different value should fail.
        let err = memory.insert(addr, val2).unwrap_err();
        assert_eq!(
            err,
            MemoryError::InconsistentMemory(Box::new((addr, val1, val2)))
        );
    }

    #[test]
    fn test_insert_address_value() {
        let mut memory = create_memory_with_segments(2);
        let addr_to_insert_at = MemoryAddress {
            segment_index: 0,
            offset: 1,
        };
        let address_value = MemoryAddress {
            segment_index: 1,
            offset: 10,
        };
        let val = MemoryValue::<F>::Address(address_value);

        assert!(memory.insert(addr_to_insert_at, val).is_ok());
        assert_eq!(memory.get(addr_to_insert_at), Some(val));
    }

    #[test]
    fn test_get_successful() {
        let mut memory = create_memory_with_segments(1);
        let addr = MemoryAddress {
            segment_index: 0,
            offset: 0,
        };
        let val = MemoryValue::<F>::Int(F::from_u64(123));
        memory.insert(addr, val).unwrap();

        assert_eq!(memory.get(addr), Some(val));
    }

    #[test]
    fn test_get_returns_none_for_unallocated_segment() {
        let memory = create_memory_with_segments(1);
        let addr = MemoryAddress {
            segment_index: 1,
            offset: 0,
        }; // Segment 1 does not exist.

        assert_eq!(memory.get::<F>(addr), None);
    }

    #[test]
    fn test_get_returns_none_for_out_of_bounds_offset() {
        let memory = create_memory_with_segments(1);
        let addr = MemoryAddress {
            segment_index: 0,
            offset: 100,
        }; // Offset 100 is out of bounds.

        assert_eq!(memory.get::<F>(addr), None);
    }

    #[test]
    fn test_get_returns_none_for_gap_in_memory() {
        let mut memory = create_memory_with_segments(1);
        // Insert at offset 5, creating a gap from 0 to 4.
        memory
            .insert(
                MemoryAddress {
                    segment_index: 0,
                    offset: 5,
                },
                MemoryValue::<F>::Int(F::ONE),
            )
            .unwrap();

        let gap_addr = MemoryAddress {
            segment_index: 0,
            offset: 2,
        };
        assert_eq!(memory.get::<F>(gap_addr), None);
    }

    #[test]
    fn test_get_array_successful() {
        // Setup: Create a memory instance with one segment.
        let mut memory = create_memory_with_segments(1);
        // Define the starting address for the array read.
        let start_addr = MemoryAddress {
            segment_index: 0,
            offset: 2,
        };
        // Define the array of mixed `MemoryValue` types to insert.
        let values_to_insert = [
            MemoryValue::Int(F::from_u64(100)),
            MemoryValue::Address(MemoryAddress::new(0, 99)),
            MemoryValue::Int(F::from_u64(300)),
        ];

        // Loop through the data and insert each value at a consecutive address.
        for (i, &val) in values_to_insert.iter().enumerate() {
            memory
                // Calculate the address for the current item: `start_addr + i`.
                .insert(start_addr.add_usize::<F>(i).unwrap(), val)
                .unwrap();
        }

        // Execute: Call `get_array` to retrieve the data.
        let result: Result<[MemoryValue<F>; 3], _> = memory.get_array(start_addr);
        // Verify: The retrieved array should be identical to the one we inserted.
        assert_eq!(result.unwrap(), values_to_insert);
    }

    #[test]
    fn test_get_array_fails_on_uninitialized() {
        // Setup: Create a memory instance with one segment.
        let mut memory = create_memory_with_segments(1);
        // Define the starting address.
        let start_addr = MemoryAddress {
            segment_index: 0,
            offset: 0,
        };
        // Insert only the *first* value of the array we intend to read.
        memory
            .insert(start_addr, MemoryValue::Int(F::from_u64(100)))
            .unwrap();

        // Execute: Attempt to read a 2-element array. This should fail on the second element.
        let result: Result<[MemoryValue<F>; 2], _> = memory.get_array(start_addr);
        // Verify: The operation should fail.
        assert!(result.is_err());
        // Verify: The error must be `UninitializedMemory` at the exact address of the missing element.
        assert_eq!(
            result.unwrap_err(),
            MemoryError::UninitializedMemory(MemoryAddress {
                segment_index: 0,
                offset: 1
            })
        );
    }
}
