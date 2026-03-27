// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use field::{Algebra, InjectiveMonomial};
use koala_bear::{KoalaBear, Poseidon1KoalaBear16};

pub trait Compression<T: Clone>: Clone + Sync {
    #[inline(always)]
    fn compress(&self, mut input: T) -> T {
        self.compress_mut(&mut input);
        input
    }

    fn compress_mut(&self, input: &mut T);
}

impl<R: Algebra<KoalaBear> + InjectiveMonomial<3> + Send + Sync + 'static> Compression<[R; 16]>
    for Poseidon1KoalaBear16
{
    fn compress_mut(&self, input: &mut [R; 16]) {
        self.compress_in_place(input);
    }
}
