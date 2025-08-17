use crate::{constant::EF, memory::address::MemoryAddress};

#[derive(Debug)]
pub struct WitnessMultilinearEval {
    pub cycle: usize,
    pub addr_coeffs: MemoryAddress, // vectorized pointer, of size 8.2^size
    pub addr_point: MemoryAddress,  // vectorized pointer, of size `size`
    pub addr_res: MemoryAddress,    // vectorized pointer
    pub n_vars: usize,
    pub point: Vec<EF>,
    pub res: EF,
}
