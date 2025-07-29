use std::ops::{Deref, DerefMut};

use p3_field::PrimeField64;

use super::{address::MemoryAddress, val::MemoryValue};

/// A memory cell used by the VM for storing 64-bit field elements with metadata.
///
/// Internally, the cell holds a single `u64` value.
/// The two most significant bits are reserved as flags:
/// - `BIT63` (NONE_MASK): indicates the cell is empty.
/// - `BIT62` (ACCESS_MASK): marks whether the cell has been accessed.
///
/// The remaining 62 bits store the canonical representation of a field element.
///
/// This design favors simplicity and cache efficiency over expressive power.
#[derive(Copy, Clone, Eq, Ord, PartialEq, PartialOrd, Debug)]
pub(crate) struct MemoryCell(u64);

impl Deref for MemoryCell {
    type Target = u64;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for MemoryCell {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl MemoryCell {
    /// Flag bit indicating the cell is empty (bit 63 set).
    pub(crate) const NONE_MASK: u64 = 1 << 63;
    /// Flag bit indicating the cell was accessed (bit 62 set).
    pub(crate) const ACCESS_MASK: u64 = 1 << 62;
    /// Flag bit indicating the cell contains a MemoryAddress (bit 61 set).
    pub(crate) const ADDRESS_MASK: u64 = 1 << 61;
    /// A mask to extract only the value bits, ignoring all flags.
    pub(crate) const VALUE_MASK: u64 = 0x1FFF_FFFF_FFFF_FFFF;
    /// Constant representing an empty cell.
    pub(crate) const NONE: Self = Self(Self::NONE_MASK);

    /// Returns true if the cell is marked as empty (`NONE`).
    pub(crate) const fn is_none(self) -> bool {
        self.0 & Self::NONE_MASK == Self::NONE_MASK
    }

    /// Returns true if the cell is not marked as empty.
    pub(crate) const fn is_some(self) -> bool {
        !self.is_none()
    }

    /// Marks the cell as accessed by setting the access flag.
    pub(crate) const fn mark_accessed(&mut self) {
        self.0 |= Self::ACCESS_MASK;
    }

    /// Returns true if the cell is marked as accessed.
    pub(crate) const fn is_accessed(self) -> bool {
        self.0 & Self::ACCESS_MASK == Self::ACCESS_MASK
    }

    pub(crate) fn value<F>(self) -> Option<MemoryValue<F>>
    where
        MemoryValue<F>: From<Self>,
    {
        self.is_some().then(|| self.into())
    }
}

impl<F> From<MemoryValue<F>> for MemoryCell
where
    F: PrimeField64,
{
    fn from(value: MemoryValue<F>) -> Self {
        match value {
            // If it's an integer, store its u64 representation.
            // The ADDRESS_MASK bit will be 0 by default.
            MemoryValue::Int(f) => Self(f.as_canonical_u64()),

            // If it's an address, pack it into the u64.
            MemoryValue::Address(addr) => {
                // Ensure the address components fit within their allocated bit-space.
                // 29 bits for segment allows for 536+ million segments.
                // 32 bits for offset allows for 4+ billion items per segment.
                debug_assert!(
                    addr.segment_index < (1 << 29),
                    "Segment index out of bounds"
                );
                debug_assert!(addr.offset < (1 << 32), "Offset out of bounds");

                // Pack segment and offset into a single u64, and set the address flag.
                let segment = (addr.segment_index as u64) << 32;
                let offset = addr.offset as u64;
                Self(segment | offset | Self::ADDRESS_MASK)
            }
        }
    }
}

impl<F> From<MemoryCell> for MemoryValue<F>
where
    F: PrimeField64,
{
    fn from(cell: MemoryCell) -> Self {
        // Check the address flag to determine the type of value.
        if (cell.0 & MemoryCell::ADDRESS_MASK) == MemoryCell::ADDRESS_MASK {
            // It's an address, so we unpack it.
            let segment_index = ((cell.0 & MemoryCell::VALUE_MASK) >> 32) as usize;
            // Mask for lower 32 bits
            let offset = (cell.0 & 0xFFFF_FFFF) as usize;

            Self::Address(MemoryAddress {
                segment_index,
                offset,
            })
        } else {
            // It's an integer. We extract the value bits and convert to a field element.
            let value_bits = cell.0 & MemoryCell::VALUE_MASK;
            Self::Int(F::from_u64(value_bits))
        }
    }
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;
    use p3_field::PrimeCharacteristicRing;
    use proptest::prelude::*;

    use super::*;

    type F = BabyBear;

    #[test]
    fn test_is_none_and_is_some() {
        // A cell explicitly created as NONE should be none.
        let none_cell = MemoryCell::NONE;
        assert!(none_cell.is_none());
        assert!(!none_cell.is_some());

        // A cell with a value (even zero) should be some.
        let some_cell = MemoryCell::from(MemoryValue::<F>::Int(F::from_u64(42)));
        assert!(!some_cell.is_none());
        assert!(some_cell.is_some());

        let zero_cell = MemoryCell::from(MemoryValue::<F>::Int(F::ZERO));
        assert!(!zero_cell.is_none());
        assert!(zero_cell.is_some());
    }

    #[test]
    fn test_mark_and_check_accessed() {
        let mut cell = MemoryCell::from(MemoryValue::<F>::Int(F::from_u64(99)));

        // Initially not accessed.
        assert!(!cell.is_accessed());

        // Mark it as accessed.
        cell.mark_accessed();

        // Now it should be accessed.
        assert!(cell.is_accessed());
        // Should not affect the NONE flag.
        assert!(cell.is_some());

        // The original value should be preserved alongside the flag.
        let value_without_flags = cell.0 & MemoryCell::VALUE_MASK;
        assert_eq!(value_without_flags, 99);
    }

    #[test]
    fn test_flag_interactions() {
        // Mark a NONE cell as accessed
        let mut none_cell = MemoryCell::NONE;
        none_cell.mark_accessed();
        assert!(none_cell.is_none(), "is_none should be true after access");
        assert!(none_cell.is_accessed(), "is_accessed should be true");
        assert_eq!(none_cell.0, MemoryCell::NONE_MASK | MemoryCell::ACCESS_MASK);

        // Mark an ADDRESS cell as accessed
        let mut addr_cell = MemoryCell::from(MemoryValue::<F>::Address(MemoryAddress {
            segment_index: 1,
            offset: 2,
        }));
        addr_cell.mark_accessed();
        assert!(addr_cell.is_some(), "Address cell should be 'some'");
        assert!(
            (addr_cell.0 & MemoryCell::ADDRESS_MASK) != 0,
            "Address flag should be set"
        );
        assert!(
            addr_cell.is_accessed(),
            "Address cell should be marked accessed"
        );
    }

    #[test]
    fn test_value_method() {
        // Test on a NONE cell.
        let none_cell = MemoryCell::NONE;
        assert_eq!(none_cell.value::<F>(), None);

        // Test on a valid integer cell.
        let int_val = MemoryValue::Int(F::from_u64(123));
        let int_cell = MemoryCell::from(int_val);
        assert_eq!(int_cell.value(), Some(int_val));

        // Test on a valid address cell.
        let addr_val = MemoryValue::<F>::Address(MemoryAddress {
            segment_index: 5,
            offset: 10,
        });
        let addr_cell = MemoryCell::from(addr_val);
        assert_eq!(addr_cell.value(), Some(addr_val));
    }

    #[test]
    fn test_conversion_from_int_value() {
        let val = MemoryValue::Int(F::from_u64(500));
        let cell = MemoryCell::from(val);
        // Should just be the raw value, no flags set.
        assert_eq!(cell.0, 500);
    }

    #[test]
    fn test_conversion_from_address_value() {
        let val = MemoryValue::<F>::Address(MemoryAddress {
            segment_index: 10,
            offset: 20,
        });
        let cell = MemoryCell::from(val);

        // Expected packed value: 0x2000000A00000014
        // Bit 61 (ADDRESS_MASK) + segment 10 shifted by 32 + offset 20
        let expected = (10u64 << 32) | 20u64 | MemoryCell::ADDRESS_MASK;
        assert_eq!(cell.0, expected);
    }

    #[test]
    fn test_conversion_to_int_value() {
        // Raw u64 for an integer.
        let int_cell = MemoryCell(42);
        let val = MemoryValue::<F>::from(int_cell);
        assert_eq!(val, MemoryValue::Int(F::from_u64(42)));

        // An integer cell can also be marked accessed; the flag should be ignored.
        let accessed_int_cell = MemoryCell(42 | MemoryCell::ACCESS_MASK);
        let accessed_val = MemoryValue::<F>::from(accessed_int_cell);
        assert_eq!(accessed_val, MemoryValue::Int(F::from_u64(42)));
    }

    #[test]
    fn test_conversion_to_address_value() {
        let raw_addr = (50u64 << 32) | 100u64 | MemoryCell::ADDRESS_MASK;
        let addr_cell = MemoryCell(raw_addr);
        let val = MemoryValue::<F>::from(addr_cell);

        let expected = MemoryValue::Address(MemoryAddress {
            segment_index: 50,
            offset: 100,
        });
        assert_eq!(val, expected);
    }

    proptest! {
        #[test]
        fn proptest_roundtrip_conversion(
            val in any::<MemoryValue<F>>()
        ) {
            // Convert the generated MemoryValue to a MemoryCell.
            let cell = MemoryCell::from(val);

            // Convert the MemoryCell back to a MemoryValue.
            let roundtrip_val = MemoryValue::<F>::from(cell);

            // Assert that the original and round-tripped values are identical.
            prop_assert_eq!(val, roundtrip_val);
        }
    }
}
