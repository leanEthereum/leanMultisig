// GPU (Metal) backend for Poseidon1-16 leaf hashing.
//
// On macOS this dispatches the first-digest layer of the WHIR Merkle tree to the
// integrated Apple GPU via a Metal compute kernel. On other platforms the GPU
// path is a stub and callers should fall back to the CPU implementation.

use std::sync::atomic::{AtomicBool, Ordering};

#[cfg(target_os = "macos")]
mod metal_impl;

#[cfg(target_os = "macos")]
pub use metal_impl::*;

#[cfg(not(target_os = "macos"))]
pub fn metal_available() -> bool {
    false
}

/// Runtime toggle for routing Poseidon work to the GPU. Off by default so
/// existing benchmarks and tests stay on the CPU path; flip it on with
/// [`set_gpu_enabled(true)`] (typically from a CLI flag) before any prover work.
static GPU_ENABLED: AtomicBool = AtomicBool::new(false);

pub fn set_gpu_enabled(enabled: bool) {
    GPU_ENABLED.store(enabled, Ordering::Relaxed);
}

pub fn gpu_enabled() -> bool {
    GPU_ENABLED.load(Ordering::Relaxed)
}
