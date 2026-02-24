// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use field::{Algebra, InjectiveMonomial, PackedValue};
use koala_bear::{
    ExternalLayer, InternalLayer, KoalaBear, KoalaBearInternalLayerParameters, KoalaBearParameters,
    Poseidon2ExternalLayerMonty31, Poseidon2InternalLayerMonty31, Poseidon2KoalaBear,
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

// Blake3-based compression for Merkle trees.

const KOALABEAR_ORDER: u32 = 0x7f00_0001;

#[derive(Clone)]
pub struct Blake3Compressor;

pub fn default_blake3_compressor() -> Blake3Compressor {
    Blake3Compressor
}

fn blake3_compress_scalar(input: &[KoalaBear; 16]) -> [KoalaBear; 8] {
    // KoalaBear (MontyField31) is repr(transparent) wrapping u32,
    // so [KoalaBear; 16] has the same layout as [u32; 16] = 64 bytes.
    let bytes: &[u8; 64] = unsafe { &*input.as_ptr().cast::<[u8; 64]>() };
    let hash = blake3::hash(bytes);
    let hash_bytes = hash.as_bytes();
    std::array::from_fn(|j| {
        let val = u32::from_le_bytes([
            hash_bytes[4 * j],
            hash_bytes[4 * j + 1],
            hash_bytes[4 * j + 2],
            hash_bytes[4 * j + 3],
        ]);
        KoalaBear::new(val % KOALABEAR_ORDER)
    })
}

impl<P: PackedValue<Value = KoalaBear> + Default> Compression<[P; 16]> for Blake3Compressor {
    fn compress_mut(&self, input: &mut [P; 16]) {
        for k in 0..P::WIDTH {
            let scalar_input: [KoalaBear; 16] = std::array::from_fn(|i| input[i].as_slice()[k]);
            let output = blake3_compress_scalar(&scalar_input);
            for j in 0..8 {
                input[j].as_slice_mut()[k] = output[j];
            }
        }
    }
}
