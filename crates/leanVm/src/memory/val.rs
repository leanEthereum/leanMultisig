use p3_field::PrimeField64;
#[cfg(test)]
use proptest::prelude::*;

use super::address::MemoryAddress;
use crate::errors::memory::MemoryError;

#[derive(Eq, Ord, Hash, PartialEq, PartialOrd, Clone, Debug)]
pub enum MemoryValue<F> {
    Address(MemoryAddress),
    Int(F),
}

impl<F> MemoryValue<F>
where
    F: PrimeField64,
{
    pub const fn to_f(&self) -> Result<F, MemoryError<F>> {
        match self {
            Self::Address(_) => Err(MemoryError::ExpectedInteger),
            Self::Int(f) => Ok(*f),
        }
    }
}

#[cfg(test)]
impl<F> Arbitrary for MemoryValue<F>
where
    F: p3_field::PrimeField64,
{
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        prop_oneof![
            // Strategy for Int: any u64
            (0..u64::MAX).prop_map(|n| Self::Int(F::from_u64(n))),
            // Strategy for Address: use the Arbitrary impl
            any::<MemoryAddress>().prop_map(Self::Address),
        ]
        .boxed()
    }
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;
    use p3_field::PrimeCharacteristicRing;

    use super::*;

    type F = BabyBear;

    #[test]
    fn test_to_f_ok() {
        // Create an integer value
        let field_elem = F::from_u64(12345);

        // Wrap it in a MemoryValue::Int variant
        let val: MemoryValue<F> = MemoryValue::Int(field_elem);

        // Call to_f()
        let result = val.to_f();

        // Assert it succeeds
        assert!(result.is_ok());

        // Assert the returned value is equal to the original
        assert_eq!(result.unwrap(), field_elem);
    }

    #[test]
    fn test_to_f_err_on_address() {
        // Construct a MemoryAddress.
        let addr = MemoryAddress {
            segment_index: 1,
            offset: 99,
        };

        // Wrap it in a MemoryValue::Address variant
        let val: MemoryValue<F> = MemoryValue::Address(addr);

        // Call to_f()
        let result = val.to_f();

        // Assert it fails
        assert!(result.is_err());

        // Assert the specific error is ExpectedInteger
        assert_eq!(result.unwrap_err(), MemoryError::ExpectedInteger);
    }
}
