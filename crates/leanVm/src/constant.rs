use p3_field::extension::BinomialExtensionField;
use p3_koala_bear::KoalaBear;

pub(crate) const DIMENSION: usize = 8;
pub(crate) type F = KoalaBear;
pub(crate) type EF = BinomialExtensionField<F, DIMENSION>;
