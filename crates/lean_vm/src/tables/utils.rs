use multilinear_toolkit::prelude::{ExtensionField, PF};
use p3_air::AirBuilder;

use crate::ExtraDataForBuses;

pub(crate) fn eval_virtual_bus_column<AB: AirBuilder, EF: ExtensionField<PF<EF>>>(
    extra_data: &ExtraDataForBuses<EF>,
    precompile_index: AB::F,
    flag: AB::F,
    data: &[AB::F],
) -> AB::EF {
    let (fingerprint_challenge_powers, bus_beta) = extra_data.transmute_bus_data::<AB::EF>();

    assert!(data.len() + 1 <= fingerprint_challenge_powers.len());
    (fingerprint_challenge_powers[1..]
        .iter()
        .zip(data)
        .map(|(c, d)| c.clone() * d.clone())
        .sum::<AB::EF>()
        + precompile_index)
        * bus_beta.clone()
        + flag
}
