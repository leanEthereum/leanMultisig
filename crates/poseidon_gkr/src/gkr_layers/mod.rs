mod full_round;
pub use full_round::*;

mod partial_round;
pub use partial_round::*;

use backend::*;

use crate::F;

pub fn poseidon_round_constants<const WIDTH: usize>() -> (&'static [[F; WIDTH]], &'static [F], &'static [[F; WIDTH]]) {
    match WIDTH {
        16 => unsafe {
            (
                &*(&KOALABEAR_RC16_EXTERNAL_INITIAL as *const [[F; 16]] as *const [[F; WIDTH]]),
                &KOALABEAR_RC16_INTERNAL,
                &*(&KOALABEAR_RC16_EXTERNAL_FINAL as *const [[F; 16]] as *const [[F; WIDTH]]),
            )
        },
        24 => unsafe {
            (
                &*(&KOALABEAR_RC24_EXTERNAL_INITIAL as *const [[F; 24]] as *const [[F; WIDTH]]),
                &KOALABEAR_RC24_INTERNAL,
                &*(&KOALABEAR_RC24_EXTERNAL_FINAL as *const [[F; 24]] as *const [[F; WIDTH]]),
            )
        },
        _ => panic!("Only Poseidon 16 and 24 are supported currently"),
    }
}
