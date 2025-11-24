use multilinear_toolkit::prelude::{ExtensionField, PF};
use p3_air::AirBuilder;

use crate::ExtraDataForBuses;

pub(crate) fn eval_virtual_bus_column<AB: AirBuilder, EF: ExtensionField<PF<EF>>>(
    extra_data: &ExtraDataForBuses<EF>,
    precompile_index: AB::F,
    flag: AB::F,
    arg_a: AB::F,
    arg_b: AB::F,
    arg_c: AB::F,
    aux: AB::F,
) -> AB::EF {
    let (fingerprint_challenge_powers, bus_beta) = extra_data.transmute_bus_data::<AB::EF>();

    let data = fingerprint_challenge_powers[1].clone() * arg_a
        + fingerprint_challenge_powers[2].clone() * arg_b
        + fingerprint_challenge_powers[3].clone() * arg_c
        + fingerprint_challenge_powers[4].clone() * aux;

    (data + precompile_index) * bus_beta + flag
}
