// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use field::{Algebra, InjectiveMonomial};
use koala_bear::{
    ExternalLayer, InternalLayer, KoalaBear, KoalaBearInternalLayerParameters, KoalaBearParameters,
    Poseidon2ExternalLayerMonty31, Poseidon2InternalLayerMonty31, Poseidon2KoalaBear,
};

/// A permutation in the mathematical sense.
pub trait Permutation<T: Clone>: Clone + Sync {
    #[inline(always)]
    fn permute(&self, mut input: T) -> T {
        self.permute_mut(&mut input);
        input
    }

    fn permute_mut(&self, input: &mut T);
}

impl<A: Algebra<KoalaBear> + Send + Sync + InjectiveMonomial<3>> Permutation<[A; 16]> for Poseidon2KoalaBear<16>
where
    Poseidon2ExternalLayerMonty31<KoalaBearParameters, 16>: ExternalLayer<A, 16, 3>,
    Poseidon2InternalLayerMonty31<KoalaBearParameters, 16, KoalaBearInternalLayerParameters>: InternalLayer<A, 16, 3>,
{
    fn permute_mut(&self, input: &mut [A; 16]) {
        koala_bear::symmetric::Permutation::permute_mut(self, input);
    }
}
