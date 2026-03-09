mod normal;
pub use normal::*;

mod packed;
pub use packed::*;

use field::Field;

pub trait AlphaPowers<EF> {
    fn alpha_powers(&self) -> &[EF];
}

impl<EF: Field> AlphaPowers<EF> for Vec<EF> {
    #[inline(always)]
    fn alpha_powers(&self) -> &[EF] {
        self
    }
}

pub trait AlphaPowersMut<EF> {
    fn alpha_powers_mut(&mut self) -> &mut Vec<EF>;
}

impl<EF: Field> AlphaPowersMut<EF> for Vec<EF> {
    #[inline(always)]
    fn alpha_powers_mut(&mut self) -> &mut Vec<EF> {
        self
    }
}
