mod full_round;
pub use full_round::*;

mod partial_round;
pub use partial_round::*;

use backend::*;

use crate::F;

pub fn poseidon_round_constants<const WIDTH: usize>()
-> (&'static [[F; WIDTH]], &'static [[F; WIDTH]], &'static [[F; WIDTH]]) {
    match WIDTH {
        16 => unsafe {
            (
                &*(poseidon1_initial_constants() as *const [[F; 16]] as *const [[F; WIDTH]]),
                &*(poseidon1_partial_constants() as *const [[F; 16]] as *const [[F; WIDTH]]),
                &*(poseidon1_final_constants() as *const [[F; 16]] as *const [[F; WIDTH]]),
            )
        },
        _ => panic!("Only Poseidon 16 is supported currently"),
    }
}
