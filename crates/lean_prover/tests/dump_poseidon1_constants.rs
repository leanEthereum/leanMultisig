//! Dumps all Poseidon1 round constants + matrices used by the leanVM AIR
//! into `crates/lean_prover/poseidon1_constants.json`, so the Python verifier
//! doesn't need to embed thousands of field literals.
//!
//! Run:
//!     cargo test --release -p lean_prover --test dump_poseidon1_constants -- --nocapture

use std::fs;
use std::path::PathBuf;

use backend::{
    KoalaBear, POSEIDON1_HALF_FULL_ROUNDS, POSEIDON1_PARTIAL_ROUNDS, PrimeField32,
    poseidon1_final_constants, poseidon1_initial_constants, poseidon1_sparse_first_round_constants,
    poseidon1_sparse_first_row, poseidon1_sparse_m_i, poseidon1_sparse_scalar_round_constants,
    poseidon1_sparse_v,
};
use serde::Serialize;

fn k(x: KoalaBear) -> u32 {
    x.as_canonical_u32()
}

#[derive(Serialize)]
struct Out {
    half_full_rounds: usize,
    partial_rounds: usize,
    initial_constants: Vec<Vec<u32>>,
    final_constants: Vec<Vec<u32>>,
    sparse_m_i: Vec<Vec<u32>>,
    sparse_first_row: Vec<Vec<u32>>,
    sparse_v: Vec<Vec<u32>>,
    sparse_first_round_constants: Vec<u32>,
    sparse_scalar_round_constants: Vec<u32>,
    mds_dense: Vec<Vec<u32>>,
}

/// Reconstruct the dense MDS matrix the way `mds_dense_16` does in
/// `lean_vm::tables::poseidon_16::mod.rs` — by running `mds_circ_16` on each
/// standard basis vector and stacking the columns into a row-major matrix.
/// We avoid touching the private `mds_circ_16` directly by recreating its
/// effect via `mds_fft_16` (which is the same map for KoalaBear).
fn dense_mds_matrix() -> [[KoalaBear; 16]; 16] {
    use backend::{PrimeCharacteristicRing, mds_circ_16};

    let mut cols = [[KoalaBear::ZERO; 16]; 16];
    for j in 0..16 {
        let mut e = [KoalaBear::ZERO; 16];
        e[j] = KoalaBear::ONE;
        mds_circ_16::<KoalaBear>(&mut e);
        cols[j] = e;
    }
    let mut rows = [[KoalaBear::ZERO; 16]; 16];
    for i in 0..16 {
        for j in 0..16 {
            rows[i][j] = cols[j][i];
        }
    }
    rows
}

#[test]
fn dump_poseidon1_constants() {
    let initial = poseidon1_initial_constants();
    let final_ = poseidon1_final_constants();
    let m_i = poseidon1_sparse_m_i();
    let first_row = poseidon1_sparse_first_row();
    let sparse_v = poseidon1_sparse_v();
    let first_rc = poseidon1_sparse_first_round_constants();
    let scalar_rc = poseidon1_sparse_scalar_round_constants();
    let mds = dense_mds_matrix();

    let out = Out {
        half_full_rounds: POSEIDON1_HALF_FULL_ROUNDS,
        partial_rounds: POSEIDON1_PARTIAL_ROUNDS,
        initial_constants: initial.iter().map(|row| row.iter().map(|&x| k(x)).collect()).collect(),
        final_constants: final_.iter().map(|row| row.iter().map(|&x| k(x)).collect()).collect(),
        sparse_m_i: m_i.iter().map(|row| row.iter().map(|&x| k(x)).collect()).collect(),
        sparse_first_row: first_row.iter().map(|row| row.iter().map(|&x| k(x)).collect()).collect(),
        sparse_v: sparse_v.iter().map(|row| row.iter().map(|&x| k(x)).collect()).collect(),
        sparse_first_round_constants: first_rc.iter().map(|&x| k(x)).collect(),
        sparse_scalar_round_constants: scalar_rc.iter().map(|&x| k(x)).collect(),
        mds_dense: mds.iter().map(|row| row.iter().map(|&x| k(x)).collect()).collect(),
    };

    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("poseidon1_constants.json");
    fs::write(&path, serde_json::to_string(&out).unwrap()).unwrap();
    println!(
        "wrote poseidon1 constants ({:.1} KiB) to {}",
        path.metadata().unwrap().len() as f64 / 1024.0,
        path.display()
    );
}
