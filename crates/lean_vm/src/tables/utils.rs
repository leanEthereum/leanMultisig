use multilinear_toolkit::prelude::*;

use crate::ExtraDataForBuses;

pub(crate) fn eval_virtual_bus_column<AB: AirBuilder, EF: ExtensionField<PF<EF>>>(
    extra_data: &ExtraDataForBuses<EF>,
    bus_index: AB::F,
    flag: AB::F,
    data: &[AB::F],
) -> AB::EF {
    let (logup_alphas_eq_poly, bus_beta) = extra_data.transmute_bus_data::<AB::EF>();

    assert!(data.len() < logup_alphas_eq_poly.len());
    (logup_alphas_eq_poly[0].clone() * bus_index
        + logup_alphas_eq_poly[1..]
            .iter()
            .zip(data)
            .map(|(c, d)| c.clone() * d.clone())
            .sum::<AB::EF>())
        * bus_beta.clone()
        + flag
}
