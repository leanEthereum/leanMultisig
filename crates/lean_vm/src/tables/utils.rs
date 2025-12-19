use multilinear_toolkit::prelude::*;

use crate::ExtraDataForBuses;

pub(crate) fn eval_virtual_bus_column<AB: AirBuilder, EF: ExtensionField<PF<EF>>>(
    extra_data: &ExtraDataForBuses<EF>,
    precompile_index: AB::F,
    flag: AB::F,
    data: &[AB::F],
) -> AB::EF {
    let (logup_alpha_powers, bus_beta) = extra_data.transmute_bus_data::<AB::EF>();

    assert!(data.len() < logup_alpha_powers.len());
    (logup_alpha_powers[1..]
        .iter()
        .zip(data)
        .map(|(c, d)| c.clone() * d.clone())
        .sum::<AB::EF>()
        + precompile_index)
        * bus_beta.clone()
        + flag
}
