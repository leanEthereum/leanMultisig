// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

use field::{Field, TwoAdicField};
use poly::*;

/// Defines the folding factor for polynomial commitments.
#[derive(Debug, Clone, Copy)]
pub struct FoldingFactor {
    first_round: usize, // batched
    subsequent_round: usize,
}

impl FoldingFactor {
    pub fn constant(factor: usize) -> Self {
        Self {
            first_round: factor,
            subsequent_round: factor,
        }
    }

    pub fn new(first_round: usize, subsequent_round: usize) -> Self {
        Self {
            first_round,
            subsequent_round,
        }
    }

    /// Retrieves the folding factor for a given round.
    #[must_use]
    pub const fn at_round(&self, round: usize) -> usize {
        if round == 0 {
            self.first_round
        } else {
            self.subsequent_round
        }
    }

    #[allow(clippy::result_unit_err)]
    pub const fn check_validity(&self, num_variables: usize) -> Result<(), ()> {
        if self.first_round > num_variables
            || self.subsequent_round > num_variables
            || self.subsequent_round == 0
            || self.first_round == 0
        {
            Err(())
        } else {
            Ok(())
        }
    }

    /// Computes the number of WHIR rounds and the number of rounds in the final sumcheck.
    #[must_use]
    pub fn compute_number_of_rounds(
        &self,
        num_variables: usize,
        max_num_variables_to_send_coeffs: usize,
    ) -> (usize, usize) {
        // Compute the number of variables remaining after the first round.
        let nv_except_first_round = num_variables - self.first_round;
        if nv_except_first_round < max_num_variables_to_send_coeffs {
            // This case is equivalent to Constant(first_round_factor)
            // the first folding is mandatory in the current implem (TODO don't fold, send directly the polynomial)
            return (0, nv_except_first_round);
        }
        // Starting from `num_variables`, the first round reduces the number of variables by `first_round_factor`,
        // and the next ones by `factor`. As soon as the number of variables is less of equal than
        // `MAX_NUM_VARIABLES_TO_SEND_COEFFS`, we stop folding and the prover sends directly the coefficients of the polynomial.
        let num_rounds = (nv_except_first_round - max_num_variables_to_send_coeffs).div_ceil(self.subsequent_round);
        let final_sumcheck_rounds = nv_except_first_round - num_rounds * self.subsequent_round;
        // No need to minus 1 because the initial round is already excepted out
        (num_rounds, final_sumcheck_rounds)
    }

    /// Computes the total number of folding rounds over `n_rounds` iterations.
    #[must_use]
    pub fn total_number(&self, n_rounds: usize) -> usize {
        self.first_round + self.subsequent_round * n_rounds
    }
}

/// Configuration parameters for WHIR proofs.
#[derive(Clone, Debug)]
pub struct WhirConfigBuilder {
    /// The logarithmic inverse rate for sampling.
    pub starting_log_inv_rate: usize,
    pub max_num_variables_to_send_coeffs: usize,
    /// The value v such that that the size of the Reed Solomon domain on which
    /// our polynomial is evaluated gets divided by `2^v` at the first round.
    /// RS domain size at commitment = 2^(num_variables + starting_log_inv_rate)
    /// RS domain size after the first round = 2^(num_variables + starting_log_inv_rate - v)
    /// The default value is 1 (halving the domain size, which is the behavior of the consecutive rounds).
    pub rs_domain_initial_reduction_factor: usize,
    /// The folding factor strategy.
    pub folding_factor: FoldingFactor,
    /// The type of soundness guarantee.
    pub soundness_type: SecurityAssumption,
    /// The security level in bits.
    pub security_level: usize,
    /// The number of bits required for proof-of-work (PoW).
    pub pow_bits: usize,
}

#[derive(Debug, Clone)]
pub struct RoundConfig<EF: Field> {
    pub query_pow_bits: usize,
    pub folding_pow_bits: usize,
    pub num_queries: usize,
    pub ood_samples: usize,
    pub log_inv_rate: usize,
    pub num_variables: usize,
    pub folding_factor: usize,
    pub domain_size: usize,
    pub folded_domain_gen: PF<EF>,
}

#[derive(Debug, Clone)]
pub struct WhirConfig<EF: Field> {
    pub num_variables: usize,

    pub commitment_ood_samples: usize,
    pub starting_log_inv_rate: usize,
    pub starting_folding_pow_bits: usize,

    pub folding_factor: FoldingFactor,
    pub rs_domain_initial_reduction_factor: usize,
    pub round_parameters: Vec<RoundConfig<EF>>,

    pub final_queries: usize,
    pub final_query_pow_bits: usize,
    pub final_log_inv_rate: usize,
    pub final_sumcheck_rounds: usize,
}

impl<EF> WhirConfig<EF>
where
    EF: Field,
    PF<EF>: TwoAdicField,
{
    /// TODO can we do better?
    fn compute_optimal_log_c(whir_parameters: &WhirConfigBuilder, field_size_bits: usize, num_variables: usize) -> f64 {
        if matches!(whir_parameters.soundness_type, SecurityAssumption::UniqueDecoding) {
            return 0.0;
        }

        let (num_rounds, _) = whir_parameters
            .folding_factor
            .compute_number_of_rounds(num_variables, whir_parameters.max_num_variables_to_send_coeffs);

        let s_0 = num_variables as f64 + 2.5 * whir_parameters.starting_log_inv_rate as f64;
        let worst_s = if num_rounds == 0 {
            s_0
        } else {
            let ff_0 = whir_parameters.folding_factor.at_round(0) as f64;
            let ff_sub = whir_parameters.folding_factor.at_round(1) as f64;
            let rs_red_0 = whir_parameters.rs_domain_initial_reduction_factor as f64;
            let delta_0 = 1.5 * ff_0 - 2.5 * rs_red_0;
            let per_round = 1.5 * ff_sub - 2.5;
            let s_last = s_0 + delta_0 + (num_rounds as f64 - 1.0) * per_round;
            s_0.max(s_last)
        };

        let budget = field_size_bits as f64
            - (whir_parameters.security_level.saturating_sub(whir_parameters.pow_bits)) as f64
            + 1.5_f64.log2()
            - worst_s;
        let m_opt = if budget > 0.0 {
            (2.0_f64.powf(budget / 5.0) - 0.5).floor() as usize
        } else {
            3
        }
        .clamp(3, 100);
        (2.0 * m_opt as f64).log2()
    }

    #[allow(clippy::too_many_lines)]
    pub fn new(whir_parameters: &WhirConfigBuilder, num_variables: usize) -> Self {
        whir_parameters.folding_factor.check_validity(num_variables).unwrap();

        assert!(
            whir_parameters.rs_domain_initial_reduction_factor <= whir_parameters.folding_factor.at_round(0),
            "Increasing the code rate is not a good idea"
        );

        let query_security_level = whir_parameters.security_level.saturating_sub(whir_parameters.pow_bits);
        let field_size_bits = EF::bits();
        let mut log_inv_rate = whir_parameters.starting_log_inv_rate;

        let log_domain_size = num_variables + log_inv_rate;
        let mut domain_size: usize = 1 << log_domain_size;

        let log_folded_domain_size = log_domain_size - whir_parameters.folding_factor.at_round(0);
        assert!(
            log_folded_domain_size <= PF::<EF>::TWO_ADICITY,
            "Increase folding_factor_0"
        );

        let (num_rounds, final_sumcheck_rounds) = whir_parameters
            .folding_factor
            .compute_number_of_rounds(num_variables, whir_parameters.max_num_variables_to_send_coeffs);

        let log_c = Self::compute_optimal_log_c(whir_parameters, field_size_bits, num_variables);

        let commitment_ood_samples = whir_parameters.soundness_type.determine_ood_samples(
            whir_parameters.security_level,
            num_variables,
            log_inv_rate,
            field_size_bits,
            log_c,
        );

        let starting_folding_pow_bits = Self::folding_pow_bits(
            whir_parameters.security_level,
            whir_parameters.soundness_type,
            field_size_bits,
            num_variables,
            log_inv_rate,
            log_c,
        );

        let mut round_parameters = Vec::with_capacity(num_rounds);

        let mut num_variables_moving = num_variables;
        num_variables_moving -= whir_parameters.folding_factor.at_round(0);
        for round in 0..num_rounds {
            // Queries are set w.r.t. to old rate, while the rest to the new rate
            let rs_reduction_factor = if round == 0 {
                whir_parameters.rs_domain_initial_reduction_factor
            } else {
                1
            };
            let next_rate = log_inv_rate + (whir_parameters.folding_factor.at_round(round) - rs_reduction_factor);

            let num_queries = whir_parameters
                .soundness_type
                .queries(query_security_level, log_inv_rate, log_c);

            let ood_samples = whir_parameters.soundness_type.determine_ood_samples(
                whir_parameters.security_level,
                num_variables_moving,
                next_rate,
                field_size_bits,
                log_c,
            );

            let query_error = whir_parameters
                .soundness_type
                .queries_error(log_inv_rate, num_queries, log_c);
            let combination_error = Self::rbr_soundness_queries_combination(
                whir_parameters.soundness_type,
                field_size_bits,
                num_variables_moving,
                next_rate,
                ood_samples,
                num_queries,
                log_c,
            );

            let query_pow_bits =
                0_f64.max(whir_parameters.security_level as f64 - (query_error.min(combination_error)));

            let folding_pow_bits = Self::folding_pow_bits(
                whir_parameters.security_level,
                whir_parameters.soundness_type,
                field_size_bits,
                num_variables_moving,
                next_rate,
                log_c,
            );
            let folding_factor = whir_parameters.folding_factor.at_round(round);
            let next_folding_factor = whir_parameters.folding_factor.at_round(round + 1);
            let folded_domain_gen = PF::<EF>::two_adic_generator(domain_size.ilog2() as usize - folding_factor);

            round_parameters.push(RoundConfig {
                query_pow_bits: query_pow_bits as usize,
                folding_pow_bits: folding_pow_bits as usize,
                num_queries,
                ood_samples,
                log_inv_rate,
                num_variables: num_variables_moving,
                folding_factor,
                domain_size,
                folded_domain_gen,
            });

            num_variables_moving -= next_folding_factor;
            log_inv_rate = next_rate;
            domain_size >>= rs_reduction_factor;
        }

        let final_queries = whir_parameters
            .soundness_type
            .queries(query_security_level, log_inv_rate, log_c);

        let final_query_pow_bits = 0_f64.max(
            whir_parameters.security_level as f64
                - whir_parameters
                    .soundness_type
                    .queries_error(log_inv_rate, final_queries, log_c),
        );

        assert!(
            field_size_bits > whir_parameters.security_level,
            "Field size must be greater than security level"
        );

        Self {
            commitment_ood_samples,
            num_variables,
            starting_log_inv_rate: whir_parameters.starting_log_inv_rate,
            starting_folding_pow_bits: starting_folding_pow_bits as usize,
            folding_factor: whir_parameters.folding_factor,
            rs_domain_initial_reduction_factor: whir_parameters.rs_domain_initial_reduction_factor,
            round_parameters,
            final_queries,
            final_query_pow_bits: final_query_pow_bits as usize,
            final_sumcheck_rounds,
            final_log_inv_rate: log_inv_rate,
        }
    }

    pub const fn starting_domain_size(&self) -> usize {
        1 << (self.num_variables + self.starting_log_inv_rate)
    }

    pub fn n_rounds(&self) -> usize {
        self.round_parameters.len()
    }

    pub const fn rs_reduction_factor(&self, round: usize) -> usize {
        if round == 0 {
            self.rs_domain_initial_reduction_factor
        } else {
            1
        }
    }

    pub fn log_inv_rate_at(&self, round: usize) -> usize {
        let mut res = self.starting_log_inv_rate;
        for r in 0..round {
            res += self.folding_factor.at_round(r);
            res -= self.rs_reduction_factor(r);
        }
        res
    }

    pub fn merkle_tree_height(&self, round: usize) -> usize {
        self.log_inv_rate_at(round) + self.num_variables - self.folding_factor.total_number(round)
    }

    pub fn n_vars_of_final_polynomial(&self) -> usize {
        self.num_variables - self.folding_factor.total_number(self.n_rounds())
    }

    pub fn max_folding_pow_bits(&self) -> usize {
        self.round_parameters.iter().map(|r| r.folding_pow_bits).max().unwrap()
    }

    #[must_use]
    pub fn rbr_soundness_fold_sumcheck(
        soundness_type: SecurityAssumption,
        field_size_bits: usize,
        num_variables: usize,
        log_inv_rate: usize,
        log_c: f64,
    ) -> f64 {
        let list_size = soundness_type.list_size_bits(num_variables, log_inv_rate, log_c);

        field_size_bits as f64 - (list_size + 1.)
    }

    #[must_use]
    pub fn folding_pow_bits(
        security_level: usize,
        soundness_type: SecurityAssumption,
        field_size_bits: usize,
        num_variables: usize,
        log_inv_rate: usize,
        log_c: f64,
    ) -> f64 {
        let prox_gaps_error = soundness_type.prox_gaps_error(num_variables, log_inv_rate, field_size_bits, 2, log_c);
        let sumcheck_error =
            Self::rbr_soundness_fold_sumcheck(soundness_type, field_size_bits, num_variables, log_inv_rate, log_c);

        let error = prox_gaps_error.min(sumcheck_error);

        0_f64.max(security_level as f64 - error)
    }

    #[must_use]
    pub fn rbr_soundness_queries_combination(
        soundness_type: SecurityAssumption,
        field_size_bits: usize,
        num_variables: usize,
        log_inv_rate: usize,
        ood_samples: usize,
        num_queries: usize,
        log_c: f64,
    ) -> f64 {
        let list_size = soundness_type.list_size_bits(num_variables, log_inv_rate, log_c);

        let log_combination = ((ood_samples + num_queries) as f64).log2();

        field_size_bits as f64 - (log_combination + list_size + 1.)
    }

    pub fn final_round_config(&self) -> RoundConfig<EF> {
        assert!(!self.round_parameters.is_empty());
        let rs_reduction_factor = self.rs_reduction_factor(self.n_rounds() - 1);
        let folding_factor = self.folding_factor.at_round(self.n_rounds());

        let last = self.round_parameters.last().unwrap();
        let domain_size = last.domain_size >> rs_reduction_factor;
        let folded_domain_gen =
            PF::<EF>::two_adic_generator(domain_size.ilog2() as usize - self.folding_factor.at_round(self.n_rounds()));

        RoundConfig {
            num_variables: last.num_variables - folding_factor,
            folding_factor,
            num_queries: self.final_queries,
            query_pow_bits: self.final_query_pow_bits,
            domain_size,
            folded_domain_gen,
            ood_samples: last.ood_samples,
            folding_pow_bits: 0,
            log_inv_rate: last.log_inv_rate,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SecurityAssumption {
    /// Unique decoding assumes that the distance of each oracle is within the UDR of the code.
    UniqueDecoding,

    /// Johnson bound assumes that the distance of each oracle is within the Johnson bound (1 - √ρ).
    JohnsonBound,

    /// Capacity bound assumes that the distance of each oracle is within the capacity bound 1 - ρ.
    CapacityBound,
}

impl SecurityAssumption {
    /// In both JB and CB theorems such as list-size only hold for proximity parameters slightly below the bound.
    /// E.g. in JB proximity gaps holds for every δ ∈ (0, 1 - √ρ).
    /// η is the distance between the chosen proximity parameter and the bound.
    /// I.e. in JB δ = 1 - √ρ - η and in CB δ = 1 - ρ - η.
    ///
    /// `log_c` is log2 of the divisor c, where η = √ρ/c (JB) or ρ/c (CB).
    /// It is computed by `WhirConfig::compute_optimal_log_c` to balance folding PoW vs queries.
    #[must_use]
    pub fn log_eta(&self, log_inv_rate: usize, log_c: f64) -> f64 {
        match self {
            Self::UniqueDecoding => panic!(),
            // η = √ρ/c
            Self::JohnsonBound => -(0.5 * log_inv_rate as f64 + log_c),
            // η = ρ/c
            Self::CapacityBound => -(log_inv_rate as f64 + log_c),
        }
    }

    /// Given a RS code (specified by the log of the degree and log inv of the rate), compute the list size at the specified distance δ.
    #[must_use]
    pub fn list_size_bits(&self, log_degree: usize, log_inv_rate: usize, log_c: f64) -> f64 {
        let log_eta = self.log_eta(log_inv_rate, log_c);
        match self {
            // In UD the list size is 1
            Self::UniqueDecoding => 0.,

            // By the JB, RS codes are (1 - √ρ - η, (2*η*√ρ)^-1)-list decodable.
            Self::JohnsonBound => {
                let log_inv_sqrt_rate: f64 = log_inv_rate as f64 / 2.;
                log_inv_sqrt_rate - (1. + log_eta)
            }

            // In CB we assume that RS codes are (1 - ρ - η, d/ρ*η)-list decodable (see Conjecture 5.6 in STIR).
            Self::CapacityBound => (log_degree + log_inv_rate) as f64 - log_eta,
        }
    }

    /// Given a RS code (specified by the log of the degree and log inv of the rate) a field_size and an arity, compute the proximity gaps error (in bits) at the specified distance
    #[must_use]
    pub fn prox_gaps_error(
        &self,
        log_degree: usize,
        log_inv_rate: usize,
        field_size_bits: usize,
        num_functions: usize,
        log_c: f64,
    ) -> f64 {
        let log_eta = self.log_eta(log_inv_rate, log_c);

        // Note that this does not include the field_size
        let error = match self {
            // In UD the error is |L|/|F| = d/ρ*|F|
            Self::UniqueDecoding => (log_degree + log_inv_rate) as f64,

            Self::JohnsonBound => {
                // From Theorem 1.5 in [BCSS25](https://eprint.iacr.org/2025/2055.pdf) "On Proximity Gaps for Reed-Solomon Codes":
                let eta = 2_f64.powf(log_eta);
                let rho = 1. / f64::from(1 << log_inv_rate);
                let rho_sqrt = rho.sqrt();
                let gamma = 1. - rho_sqrt - eta;
                let n = (1usize << (log_degree + log_inv_rate)) as f64;
                let m = (rho_sqrt / (2. * eta)).ceil().max(3.);
                let num_1 = (2. * (m + 0.5).powi(5) + 3. * (m + 0.5) * gamma * rho) * n;
                let den_1 = 3. * rho * rho_sqrt;
                let num_2 = m + 0.5;
                let den_2 = rho_sqrt;
                ((num_1 / den_1) + (num_2 / den_2)).log2()
            }

            Self::CapacityBound => (log_degree + 2 * log_inv_rate) as f64 - log_eta,
        };

        // Error is  (num_functions - 1) * error/|F|;
        let num_functions_1_log = (num_functions as f64 - 1.).log2();
        field_size_bits as f64 - (error + num_functions_1_log)
    }

    /// The query error is (1 - δ)^t where t is the number of queries.
    /// This computes log(1 - δ).
    /// - In UD, δ is (1 - ρ)/2
    /// - In JB, δ is (1 - √ρ - η)
    /// - In CB, δ is (1 - ρ - η)
    #[must_use]
    pub fn log_1_delta(&self, log_inv_rate: usize, log_c: f64) -> f64 {
        let eta = if matches!(self, Self::UniqueDecoding) {
            0.
        } else {
            2_f64.powf(self.log_eta(log_inv_rate, log_c))
        };
        let rate = 1. / f64::from(1 << log_inv_rate);

        let delta = match self {
            Self::UniqueDecoding => 0.5 * (1. - rate),
            Self::JohnsonBound => 1. - rate.sqrt() - eta,
            Self::CapacityBound => 1. - rate - eta,
        };

        (1. - delta).log2()
    }

    /// Compute the number of queries to match the security level
    #[must_use]
    pub fn queries(&self, protocol_security_level: usize, log_inv_rate: usize, log_c: f64) -> usize {
        let num_queries_f = -(protocol_security_level as f64) / self.log_1_delta(log_inv_rate, log_c);

        num_queries_f.ceil() as usize
    }

    /// Compute the error for the given number of queries
    #[must_use]
    pub fn queries_error(&self, log_inv_rate: usize, num_queries: usize, log_c: f64) -> f64 {
        let num_queries = num_queries as f64;

        -num_queries * self.log_1_delta(log_inv_rate, log_c)
    }

    /// Compute the error for the OOD samples of the protocol
    #[must_use]
    pub fn ood_error(
        &self,
        log_degree: usize,
        log_inv_rate: usize,
        field_size_bits: usize,
        ood_samples: usize,
        log_c: f64,
    ) -> f64 {
        if matches!(self, Self::UniqueDecoding) {
            return 0.;
        }

        let list_size_bits = self.list_size_bits(log_degree, log_inv_rate, log_c);

        let error = 2. * list_size_bits + (log_degree * ood_samples) as f64;
        (ood_samples * field_size_bits) as f64 + 1. - error
    }

    /// Computes the number of OOD samples required to achieve security_level bits of security
    #[must_use]
    pub fn determine_ood_samples(
        &self,
        security_level: usize,
        log_degree: usize,
        log_inv_rate: usize,
        field_size_bits: usize,
        log_c: f64,
    ) -> usize {
        if matches!(self, Self::UniqueDecoding) {
            return 0;
        }

        for ood_samples in 1..64 {
            if self.ood_error(log_degree, log_inv_rate, field_size_bits, ood_samples, log_c) >= security_level as f64 {
                return ood_samples;
            }
        }

        panic!("Could not find an appropriate number of OOD samples");
    }
}
