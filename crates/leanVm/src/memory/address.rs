use std::{fmt::Display, ops::Add};

use num_traits::cast::ToPrimitive;
use p3_field::PrimeField64;
#[cfg(test)]
use proptest::prelude::*;

use super::val::MemoryValue;
use crate::{
    constant::F,
    errors::{math::MathError, memory::MemoryError},
};

#[derive(Eq, Ord, Hash, PartialEq, PartialOrd, Clone, Copy, Debug, Default)]
pub struct MemoryAddress {
    pub segment_index: usize,
    pub offset: usize,
}

impl MemoryAddress {
    #[must_use]
    pub const fn new(segment_index: usize, offset: usize) -> Self {
        Self {
            segment_index,
            offset,
        }
    }

    /// Add a `usize` to the address.
    pub fn add_usize(self, other: usize) -> Result<Self, MathError> {
        // Try to compute the new offset by adding `other` to the current offset.
        //
        // This uses `checked_add` to safely detect any potential `usize` overflow.
        self.offset
            .checked_add(other)
            .map(|offset| Self {
                segment_index: self.segment_index,
                offset,
            })
            .ok_or_else(|| MathError::MemoryAddressAddUsizeOffsetExceeded(Box::new((self, other))))
    }
}

impl Add<&F> for MemoryAddress {
    type Output = Result<Self, MathError>;

    fn add(self, other: &F) -> Self::Output {
        // This chained operation safely calculates the new offset.
        // - Cast the current `usize` offset to a `u64` to match the field element's type.
        // - Add the field element's canonical `u64` value, checking for arithmetic overflow.
        // - Chain another operation to convert the `u64` result back into a `usize`.
        // - If any of the chained steps returned `None`, create the specific overflow error.
        let new_offset = ((self.offset as u64).checked_add(other.as_canonical_u64()))
            .and_then(|x| x.to_usize())
            .ok_or_else(|| {
                MathError::MemoryAddressAddFieldOffsetExceeded(Box::new((self, *other)))
            })?;

        // If the addition was successful, create a new address with
        // - the same segment,
        // - the newly calculated offset.
        Ok(Self::new(self.segment_index, new_offset))
    }
}

impl Display for MemoryAddress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.segment_index, self.offset)
    }
}

impl TryFrom<MemoryValue> for MemoryAddress {
    type Error = MemoryError;

    fn try_from(value: MemoryValue) -> Result<Self, Self::Error> {
        match value {
            MemoryValue::Address(addr) => Ok(addr),
            MemoryValue::Int(_) => Err(MemoryError::ExpectedMemoryAddress),
        }
    }
}

#[cfg(test)]
impl Arbitrary for MemoryAddress {
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        (
            // segment_index fits in 29 bits
            0..((1u64 << 29) - 1) as usize,
            // offset fits in 32 bits
            0..((1u64 << 32) - 1) as usize,
        )
            .prop_map(|(segment_index, offset)| Self {
                segment_index,
                offset,
            })
            .boxed()
    }
}

#[cfg(test)]
mod tests {
    use p3_field::PrimeCharacteristicRing;
    use proptest::prelude::*;

    use super::*;

    #[test]
    fn test_add_usize_success() {
        let addr = MemoryAddress {
            segment_index: 2,
            offset: 100,
        };
        let result = addr.add_usize(25);
        assert_eq!(
            result,
            Ok(MemoryAddress {
                segment_index: 2,
                offset: 125
            })
        );
    }

    #[test]
    fn test_add_zero_offset() {
        let addr = MemoryAddress {
            segment_index: 5,
            offset: 500,
        };
        let result = addr.add_usize(0);
        assert_eq!(result, Ok(addr));
    }

    #[test]
    fn test_add_usize_overflow() {
        let addr = MemoryAddress {
            segment_index: 1,
            offset: usize::MAX,
        };
        let result = addr.add_usize(1);
        match result {
            Err(MathError::MemoryAddressAddUsizeOffsetExceeded(boxed)) => {
                let (original, added) = *boxed;
                assert_eq!(original.segment_index, 1);
                assert_eq!(original.offset, usize::MAX);
                assert_eq!(added, 1);
            }
            _ => panic!("Expected overflow error, got: {result:?}"),
        }
    }

    proptest! {
        #[test]
        fn test_add_does_not_overflow(addr in any::<MemoryAddress>(), delta in 0usize..1_000_000) {
            let result = addr.add_usize(delta);
            // Only test when offset + delta won't overflow
            if let Some(expected_offset) = addr.offset.checked_add(delta) {
                prop_assert_eq!(result, Ok(MemoryAddress {
                    segment_index: addr.segment_index,
                    offset: expected_offset,
                }));
            } else {
                prop_assert!(matches!(
                    result,
                    Err(MathError::MemoryAddressAddUsizeOffsetExceeded(_))
                ));
            }
        }
    }

    #[test]
    fn test_try_into_memory_address_ok() {
        // Construct a MemoryAddress.
        let addr = MemoryAddress {
            segment_index: 3,
            offset: 42,
        };

        // Wrap it in a MemoryValue::Address variant
        let val: MemoryValue = MemoryValue::Address(addr);

        // Try converting it into a MemoryAddress
        let result: Result<MemoryAddress, MemoryError> = val.try_into();

        // Assert it succeeds
        assert!(result.is_ok());

        // Assert the returned address is equal to the original
        assert_eq!(result.unwrap(), addr);
    }

    #[test]
    fn test_try_into_memory_address_err_on_int() {
        // Create an integer value
        let field_elem = F::from_u64(17);

        // Wrap it in a MemoryValue::Int variant
        let val: MemoryValue = MemoryValue::Int(field_elem);

        // Try converting it into a MemoryAddress
        let result: Result<MemoryAddress, MemoryError> = val.try_into();

        // Assert it fails
        assert!(result.is_err());

        // Assert the specific error is ExpectedMemoryAddress
        assert_eq!(result.unwrap_err(), MemoryError::ExpectedMemoryAddress);
    }

    #[test]
    fn test_add_field_element_success() {
        // Setup: An initial address and a field element to add.
        let addr = MemoryAddress::new(2, 100);
        let val = F::from_u64(50);

        // Execute: Add the field element to the address using the `+` operator.
        let result = addr + &val;

        // Verify: The result should be `Ok` and the offset should be updated correctly,
        // while the segment index remains the same.
        assert_eq!(result, Ok(MemoryAddress::new(2, 150)));
    }

    #[test]
    fn test_add_field_element_zero() {
        // Setup: An initial address.
        let addr = MemoryAddress::new(3, 123);
        let val = F::ZERO;

        // Execute: Add zero to the address.
        let result = addr + &val;

        // Verify: The address should remain unchanged.
        assert_eq!(result, Ok(addr));
    }

    #[test]
    fn test_add_field_element_overflow() {
        // Setup: An address with the maximum possible offset.
        let addr = MemoryAddress::new(1, usize::MAX);
        let val = F::ONE;

        // Execute: Add 1, which should cause an overflow.
        let result = addr + &val;

        // Verify: The result should be an `Err` with the specific offset overflow variant.
        assert!(matches!(
            result,
            Err(MathError::MemoryAddressAddFieldOffsetExceeded(_))
        ));
    }
}
