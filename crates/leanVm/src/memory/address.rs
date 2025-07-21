#[cfg(test)]
use proptest::prelude::*;

#[derive(Eq, Ord, Hash, PartialEq, PartialOrd, Clone, Copy, Debug, Default)]
pub struct MemoryAddress {
    pub segment_index: usize,
    pub offset: usize,
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
