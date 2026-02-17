// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

//! The Poseidon2 permutation.

mod external;
mod generic;
mod internal;
mod round_numbers;
use alloc::vec::Vec;
use core::marker::PhantomData;

use crate::symmetric::{CryptographicPermutation, Permutation};
pub use external::*;
use field::{Algebra, InjectiveMonomial, PrimeField, PrimeField64};
pub use generic::*;
pub use internal::*;
use rand::Rng;
use rand::distr::{Distribution, StandardUniform};
pub use round_numbers::poseidon2_round_numbers_128;

const SUPPORTED_WIDTHS: [usize; 8] = [2, 3, 4, 8, 12, 16, 20, 24];

/// The Poseidon2 permutation.
#[derive(Clone, Debug)]
pub struct Poseidon2<F, ExternalPerm, InternalPerm, const WIDTH: usize, const D: u64> {
    /// The permutations used in External Rounds.
    external_layer: ExternalPerm,

    /// The permutation used in Internal Rounds.
    internal_layer: InternalPerm,

    _phantom: PhantomData<F>,
}

impl<F, ExternalPerm, InternalPerm, const WIDTH: usize, const D: u64> Poseidon2<F, ExternalPerm, InternalPerm, WIDTH, D>
where
    F: PrimeField,
    ExternalPerm: ExternalLayerConstructor<F, WIDTH>,
    InternalPerm: InternalLayerConstructor<F>,
{
    /// Create a new Poseidon2 configuration.
    /// This internally converts the given constants to the relevant packed versions.
    pub fn new(external_constants: ExternalLayerConstants<F, WIDTH>, internal_constants: Vec<F>) -> Self {
        assert!(SUPPORTED_WIDTHS.contains(&WIDTH));
        let external_layer = ExternalPerm::new_from_constants(external_constants);
        let internal_layer = InternalPerm::new_from_constants(internal_constants);

        Self {
            external_layer,
            internal_layer,
            _phantom: PhantomData,
        }
    }

    /// Create a new Poseidon2 configuration with random parameters.
    pub fn new_from_rng<R: Rng>(rounds_f: usize, rounds_p: usize, rng: &mut R) -> Self
    where
        StandardUniform: Distribution<F> + Distribution<[F; WIDTH]>,
    {
        let external_constants = ExternalLayerConstants::new_from_rng(rounds_f, rng);
        let internal_constants = rng.sample_iter(StandardUniform).take(rounds_p).collect();

        Self::new(external_constants, internal_constants)
    }
}

impl<F, ExternalPerm, InternalPerm, const WIDTH: usize, const D: u64> Poseidon2<F, ExternalPerm, InternalPerm, WIDTH, D>
where
    F: PrimeField64,
    ExternalPerm: ExternalLayerConstructor<F, WIDTH>,
    InternalPerm: InternalLayerConstructor<F>,
{
    /// Create a new Poseidon2 configuration with 128 bit security and random rounds constants.
    ///
    /// # Panics
    /// This will panic if D and F::ORDER_U64 - 1 are not relatively prime.
    /// This will panic if the optimal parameters for the given field and width have not been computed.
    pub fn new_from_rng_128<R: Rng>(rng: &mut R) -> Self
    where
        StandardUniform: Distribution<F> + Distribution<[F; WIDTH]>,
    {
        let round_numbers = poseidon2_round_numbers_128::<F>(WIDTH, D);
        let (rounds_f, rounds_p) = round_numbers.unwrap_or_else(|e| panic!("{e}"));
        Self::new_from_rng(rounds_f, rounds_p, rng)
    }
}

impl<F, A, ExternalPerm, InternalPerm, const WIDTH: usize, const D: u64> Permutation<[A; WIDTH]>
    for Poseidon2<F, ExternalPerm, InternalPerm, WIDTH, D>
where
    F: PrimeField + InjectiveMonomial<D>,
    A: Algebra<F> + Sync + InjectiveMonomial<D>,
    ExternalPerm: ExternalLayer<A, WIDTH, D>,
    InternalPerm: InternalLayer<A, WIDTH, D>,
{
    fn permute_mut(&self, state: &mut [A; WIDTH]) {
        let initial_state = state.clone();
        self.external_layer.permute_state_initial(state);
        self.internal_layer.permute_state(state);
        self.external_layer.permute_state_terminal(state);
        // Warning: this is not really poseidon2 permutation, this is poseidon2 in "compression" mode
        state.iter_mut().zip(initial_state.into_iter()).for_each(|(s, i)| {
            *s = s.clone() + i;
        });
    }
}

impl<F, A, ExternalPerm, InternalPerm, const WIDTH: usize, const D: u64> CryptographicPermutation<[A; WIDTH]>
    for Poseidon2<F, ExternalPerm, InternalPerm, WIDTH, D>
where
    F: PrimeField + InjectiveMonomial<D>,
    A: Algebra<F> + Sync + InjectiveMonomial<D>,
    ExternalPerm: ExternalLayer<A, WIDTH, D>,
    InternalPerm: InternalLayer<A, WIDTH, D>,
{
}
