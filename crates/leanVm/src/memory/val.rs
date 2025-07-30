use std::ops::{Add, Mul};

use p3_field::PrimeCharacteristicRing;
#[cfg(test)]
use proptest::prelude::*;

use super::address::MemoryAddress;
use crate::{constant::F, errors::memory::MemoryError};

#[derive(Eq, Ord, Hash, PartialEq, PartialOrd, Clone, Copy, Debug)]
pub enum MemoryValue {
    Address(MemoryAddress),
    Int(F),
}

impl Default for MemoryValue {
    fn default() -> Self {
        Self::Int(F::default())
    }
}

impl MemoryValue {
    pub const fn to_f(&self) -> Result<F, MemoryError> {
        match self {
            Self::Address(_) => Err(MemoryError::ExpectedInteger),
            Self::Int(f) => Ok(*f),
        }
    }
}

impl Add for MemoryValue {
    type Output = Result<Self, MemoryError>;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            // Case 1: Add two integers, returning a new integer.
            (Self::Int(a), Self::Int(b)) => Ok(Self::Int(a + b)),

            // Case 2 & 3: Add an integer to an address (pointer arithmetic).
            (Self::Address(address), Self::Int(int)) | (Self::Int(int), Self::Address(address)) => {
                // The address computation by adding the integer to the address is safe.
                let new_address = (address + &int)?;
                Ok(Self::Address(new_address))
            }

            // Case 4: Adding two addresses is an invalid operation.
            (Self::Address(a), Self::Address(b)) => {
                Err(MemoryError::MemoryAddressAdd(Box::new((a, b))))
            }
        }
    }
}

impl Mul for MemoryValue {
    type Output = Result<Self, MemoryError>;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            // Case 1 (Success): Multiply two integers.
            (Self::Int(a), Self::Int(b)) => Ok(Self::Int(a * b)),

            // Case 2 (Error): Any other combination is invalid for multiplication.
            //
            // This includes:
            // - Address * Int,
            // - Int * Address,
            // - Address * Address.
            _ => Err(MemoryError::InvalidMul(Box::new((self, rhs)))),
        }
    }
}

impl Add<usize> for MemoryValue {
    type Output = Result<Self, MemoryError>;

    fn add(self, rhs: usize) -> Self::Output {
        match self {
            Self::Address(addr) => Ok(Self::Address(addr.add_usize(rhs)?)),
            Self::Int(int) => Ok(Self::Int(int + F::from_usize(rhs))),
        }
    }
}

impl From<MemoryAddress> for MemoryValue {
    fn from(addr: MemoryAddress) -> Self {
        Self::Address(addr)
    }
}

impl From<F> for MemoryValue {
    fn from(f: F) -> Self {
        Self::Int(f)
    }
}

#[cfg(test)]
impl Arbitrary for MemoryValue {
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
    use p3_field::PrimeCharacteristicRing;

    use super::*;
    use crate::errors::math::MathError;

    #[test]
    fn test_to_f_ok() {
        // Create an integer value
        let field_elem = F::from_u64(12345);

        // Wrap it in a MemoryValue::Int variant
        let val: MemoryValue = MemoryValue::Int(field_elem);

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
        let val: MemoryValue = MemoryValue::Address(addr);

        // Call to_f()
        let result = val.to_f();

        // Assert it fails
        assert!(result.is_err());

        // Assert the specific error is ExpectedInteger
        assert_eq!(result.unwrap_err(), MemoryError::ExpectedInteger);
    }

    #[test]
    fn test_add_two_ints_success() {
        // Setup: Create two integer memory values.
        let val1 = MemoryValue::Int(F::from_u64(100));
        let val2 = MemoryValue::Int(F::from_u64(50));

        // Action: Add the two values together.
        let result = (val1 + val2).unwrap();

        // Verify: The result should be an integer with the correct sum.
        assert_eq!(result, MemoryValue::Int(F::from_u64(150)));
    }

    #[test]
    fn test_add_int_to_address_success() {
        // Setup: Create an address and an integer value.
        let addr = MemoryAddress::new(1, 10);
        let val1 = MemoryValue::Address(addr);
        let val2 = MemoryValue::Int(F::from_u64(5));

        // Action: Add the integer to the address.
        let result = (val1 + val2).unwrap();

        // Verify: The result should be a new address with the offset correctly incremented.
        assert_eq!(result, MemoryValue::Address(MemoryAddress::new(1, 15)));
    }

    #[test]
    fn test_add_address_to_int_success() {
        // Setup: Create an integer and an address value (commutative test).
        let addr = MemoryAddress::new(1, 10);
        let val1 = MemoryValue::Int(F::from_u64(5));
        let val2 = MemoryValue::Address(addr);

        // Action: Add the address to the integer.
        let result = (val1 + val2).unwrap();

        // Verify: The result should be a new address with the offset correctly incremented.
        assert_eq!(result, MemoryValue::Address(MemoryAddress::new(1, 15)));
    }

    #[test]
    fn test_add_int_to_address_overflow_fails() {
        // Setup: Create an address at the maximum possible offset and an integer value of 1.
        let addr = MemoryAddress::new(1, usize::MAX);
        let val1 = MemoryValue::Address(addr);
        let val2 = MemoryValue::Int(F::from_u64(1));

        // Action: Attempt to add the integer, which should cause an overflow.
        let err = (val1 + val2).unwrap_err();

        // Verify: The operation should fail with the specific offset overflow error.
        assert!(matches!(
            err,
            MemoryError::Math(MathError::MemoryAddressAddFieldOffsetExceeded(_))
        ));
    }

    #[test]
    fn test_add_two_addresses_fails() {
        // Setup: Create two address values.
        let addr1 = MemoryAddress::new(1, 10);
        let addr2 = MemoryAddress::new(2, 20);
        let val1 = MemoryValue::Address(addr1);
        let val2 = MemoryValue::Address(addr2);

        // Action: Attempt to add the two addresses.
        let err = (val1 + val2).unwrap_err();

        // Verify: The operation should fail, as adding two addresses is not a valid operation.
        assert!(matches!(err, MemoryError::MemoryAddressAdd(_)));
    }

    #[test]
    fn test_mul_two_ints_success() {
        // Setup: Create two integer memory values.
        let val1 = MemoryValue::Int(F::from_u64(10));
        let val2 = MemoryValue::Int(F::from_u64(5));

        // Action: Multiply the two values.
        let result = (val1 * val2).unwrap();

        // Verify: The result should be an integer with the correct product.
        assert_eq!(result, MemoryValue::Int(F::from_u64(50)));
    }

    #[test]
    fn test_mul_int_and_address_fails() {
        // Setup: Create an address and an integer value.
        let val1 = MemoryValue::Address(MemoryAddress::new(1, 10));
        let val2 = MemoryValue::Int(F::from_u64(5));

        // Action: Attempt to multiply them.
        let err = (val1 * val2).unwrap_err();

        // Verify: The operation should fail with the specific `InvalidMul` error,
        // containing the values that caused the failure.
        assert!(matches!(err, MemoryError::InvalidMul(boxed) if *boxed == (val1, val2)));
    }

    #[test]
    fn test_mul_two_addresses_fails() {
        // Setup: Create two address values.
        let val1 = MemoryValue::Address(MemoryAddress::new(1, 10));
        let val2 = MemoryValue::Address(MemoryAddress::new(2, 20));

        // Action: Attempt to multiply them.
        let err = (val1 * val2).unwrap_err();

        // Verify: The operation should fail with the `InvalidMul` error.
        assert!(matches!(err, MemoryError::InvalidMul(boxed) if *boxed == (val1, val2)));
    }
}
