#[cfg(test)]
use proptest::prelude::*;

use super::address::MemoryAddress;

#[derive(Eq, Ord, Hash, PartialEq, PartialOrd, Clone, Debug)]
pub enum MemoryValue<F> {
    Address(MemoryAddress),
    Int(F),
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
