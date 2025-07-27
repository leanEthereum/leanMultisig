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

impl<F> TryInto<MemoryAddress> for MemoryValue<F>
where
    F: PrimeField64,
{
    type Error = MemoryError<F>;

    fn try_into(self) -> Result<MemoryAddress, Self::Error> {
        match self {
            Self::Address(addr) => Ok(addr),
            Self::Int(_) => Err(MemoryError::AddressNotRelocatable),
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
    fn test_try_into_memory_address_ok() {
        // Construct a MemoryAddress.
        let addr = MemoryAddress {
            segment_index: 3,
            offset: 42,
        };

        // Wrap it in a MemoryValue::Address variant
        let val: MemoryValue<F> = MemoryValue::Address(addr);

        // Try converting it into a MemoryAddress
        let result: Result<MemoryAddress, MemoryError<F>> = val.try_into();

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
        let val: MemoryValue<BabyBear> = MemoryValue::Int(field_elem);

        // Try converting it into a MemoryAddress
        let result: Result<MemoryAddress, MemoryError<BabyBear>> = val.try_into();

        // Assert it fails
        assert!(result.is_err());

        // Assert the specific error is AddressNotRelocatable
        assert_eq!(result.unwrap_err(), MemoryError::AddressNotRelocatable);
    }
}
