use std::{fmt::Display, ops::Add};

#[cfg(test)]
use proptest::prelude::*;

use crate::types::math_errors::MathError;

#[derive(Eq, Ord, Hash, PartialEq, PartialOrd, Clone, Copy, Debug, Default)]
pub struct MemoryAddress {
    pub segment_index: usize,
    pub offset: usize,
}

impl Add<usize> for MemoryAddress {
    type Output = Result<Self, MathError>;

    fn add(self, other: usize) -> Result<Self, MathError> {
        // Try to compute the new offset by adding `other` to the current offset.
        //
        // This uses `checked_add` to safely detect any potential `usize` overflow.
        self.offset
            .checked_add(other)
            .map(|offset| Self {
                // Keep the same segment index.
                segment_index: self.segment_index,
                // Use the new (safe) offset.
                offset,
            })
            .ok_or_else(|| MathError::MemoryAddressAddUsizeOffsetExceeded(Box::new((self, other))))
    }
}

impl Display for MemoryAddress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.segment_index, self.offset)
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
    use proptest::prelude::*;

    use super::*;

    #[test]
    fn test_add_usize_success() {
        let addr = MemoryAddress {
            segment_index: 2,
            offset: 100,
        };
        let result = addr + 25;
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
        let result = addr + 0;
        assert_eq!(result, Ok(addr));
    }

    #[test]
    fn test_add_usize_overflow() {
        let addr = MemoryAddress {
            segment_index: 1,
            offset: usize::MAX,
        };
        let result = addr + 1;
        match result {
            Err(MathError::MemoryAddressAddUsizeOffsetExceeded(boxed)) => {
                let (original, added) = *boxed;
                assert_eq!(original.segment_index, 1);
                assert_eq!(original.offset, usize::MAX);
                assert_eq!(added, 1);
            }
            _ => panic!("Expected overflow error, got: {:?}", result),
        }
    }

    proptest! {
        #[test]
        fn test_add_does_not_overflow(addr in any::<MemoryAddress>(), delta in 0usize..1_000_000) {
            // Only test when offset + delta won't overflow
            if let Some(expected_offset) = addr.offset.checked_add(delta) {
                let result = addr + delta;
                prop_assert_eq!(result, Ok(MemoryAddress {
                    segment_index: addr.segment_index,
                    offset: expected_offset,
                }));
            } else {
                let result = addr + delta;
                prop_assert!(matches!(
                    result,
                    Err(MathError::MemoryAddressAddUsizeOffsetExceeded(_))
                ));
            }
        }
    }
}
