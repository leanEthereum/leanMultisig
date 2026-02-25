// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use field::{Algebra, InjectiveMonomial};
use koala_bear::{
    ExternalLayer, InternalLayer, KoalaBear, KoalaBearInternalLayerParameters, KoalaBearParameters,
    Poseidon1KoalaBear16, Poseidon2ExternalLayerMonty31, Poseidon2InternalLayerMonty31, Poseidon2KoalaBear,
};

pub trait Compression<T: Clone>: Clone + Sync {
    #[inline(always)]
    fn compress(&self, mut input: T) -> T {
        self.compress_mut(&mut input);
        input
    }

    fn compress_mut(&self, input: &mut T);
}

impl<A: Algebra<KoalaBear> + Send + Sync + InjectiveMonomial<3>> Compression<[A; 16]> for Poseidon2KoalaBear<16>
where
    Poseidon2ExternalLayerMonty31<KoalaBearParameters, 16>: ExternalLayer<A, 16, 3>,
    Poseidon2InternalLayerMonty31<KoalaBearParameters, 16, KoalaBearInternalLayerParameters>: InternalLayer<A, 16, 3>,
{
    fn compress_mut(&self, input: &mut [A; 16]) {
        self.compress_in_place(input);
    }
}

impl<R: Algebra<KoalaBear> + InjectiveMonomial<3> + Send + Sync + 'static> Compression<[R; 16]>
    for Poseidon1KoalaBear16
{
    fn compress_mut(&self, input: &mut [R; 16]) {
        self.compress_in_place(input);
    }
}
