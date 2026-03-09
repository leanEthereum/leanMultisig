use backend::*;

use crate::{ExtraDataForBuses, LOGUP_PRECOMPILE_DOMAINSEP};

pub(crate) fn eval_virtual_bus_column<AB: AirBuilder, EF: ExtensionField<PF<EF>>>(
    extra_data: &ExtraDataForBuses<EF>,
    flag: AB::F,
    data: &[AB::F],
) -> AB::EF {
    let (logup_alphas_eq_poly, bus_beta) = extra_data.transmute_bus_data::<AB::EF>();

    assert!(data.len() < logup_alphas_eq_poly.len());
    (logup_alphas_eq_poly
        .iter()
        .zip(data)
        .map(|(c, d)| *c * *d)
        .sum::<AB::EF>()
        + *logup_alphas_eq_poly.last().unwrap() * AB::F::from_usize(LOGUP_PRECOMPILE_DOMAINSEP))
        * *bus_beta
        + flag
}
