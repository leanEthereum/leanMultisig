use vm::EF;

/// Holds the high-level witness data for a single multilinear evaluation precompile.
#[derive(Debug)]
pub struct WitnessMultilinearEval {
    /// The CPU cycle at which this operation is initiated.
    pub cycle: usize,
    /// The memory address of the polynomial's coefficients.
    pub addr_coeffs: usize,
    /// The memory address of the evaluation point's coordinates.
    pub addr_point: usize,
    /// The memory address where the final result is stored.
    pub addr_res: usize,
    /// The number of variables in the multilinear polynomial.
    pub n_vars: usize,
    /// The coordinates of the evaluation point.
    pub point: Vec<EF>,
    /// The final computed result of the evaluation.
    pub res: EF,
}
