//! On-disk cache for compiled `Bytecode`.
//!
//! Keyed by SHA3-256 of the embedded zkDSL sources + placeholder replacements,
//! so any edit to a `.py` file or to LOG_M / n_blobs invalidates the entry.
//! The platform-specific `instructions_multilinear_packed` is skipped on the
//! wire and recomputed from `instructions_multilinear` on load.

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::{env, fs};

use lean_vm::Bytecode;
use sha3::{Digest, Sha3_256};

/// Bumped whenever the on-disk layout changes (e.g. new field on `Bytecode`).
const CACHE_FORMAT_VERSION: u32 = 1;

/// Look up a cached `Bytecode` for the given embedded sources + replacements.
/// Returns `None` on miss or unreadable/corrupt cache.
pub fn try_load(dir: &include_dir::Dir<'_>, replacements: &BTreeMap<String, String>) -> Option<(Bytecode, PathBuf)> {
    let path = cache_path(dir, replacements);
    let bytes = fs::read(&path).ok()?;
    match postcard::from_bytes::<Bytecode>(&bytes) {
        Ok(mut bc) => {
            bc.recompute_packed();
            Some((bc, path))
        }
        Err(e) => {
            eprintln!("Warning: ignoring corrupt bytecode cache at {}: {e}", path.display());
            None
        }
    }
}

/// Persist `bytecode` to the cache. Errors are non-fatal; on failure a warning
/// is printed and the function returns `Err`.
pub fn try_store(
    dir: &include_dir::Dir<'_>,
    replacements: &BTreeMap<String, String>,
    bytecode: &Bytecode,
) -> std::io::Result<PathBuf> {
    let path = cache_path(dir, replacements);
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    let bytes = postcard::to_allocvec(bytecode).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
    fs::write(&path, bytes)?;
    Ok(path)
}

fn cache_path(dir: &include_dir::Dir<'_>, replacements: &BTreeMap<String, String>) -> PathBuf {
    cache_dir().join(format!("{}.bin", compute_key(dir, replacements)))
}

fn compute_key(dir: &include_dir::Dir<'_>, replacements: &BTreeMap<String, String>) -> String {
    let mut hasher = Sha3_256::new();
    hasher.update(CACHE_FORMAT_VERSION.to_le_bytes());

    // Hash every embedded source file (path + content), in deterministic order.
    let mut files: Vec<&include_dir::File<'_>> = dir.files().collect();
    files.sort_by_key(|f| f.path());
    for file in files {
        hasher.update((file.path().to_string_lossy().len() as u64).to_le_bytes());
        hasher.update(file.path().to_string_lossy().as_bytes());
        hasher.update((file.contents().len() as u64).to_le_bytes());
        hasher.update(file.contents());
    }

    // Hash replacements (BTreeMap iterates in sorted key order).
    for (k, v) in replacements {
        hasher.update((k.len() as u64).to_le_bytes());
        hasher.update(k.as_bytes());
        hasher.update((v.len() as u64).to_le_bytes());
        hasher.update(v.as_bytes());
    }

    hex_encode(&hasher.finalize())
}

fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        out.push(HEX[(b >> 4) as usize] as char);
        out.push(HEX[(b & 0xf) as usize] as char);
    }
    out
}

fn cache_dir() -> PathBuf {
    let target_dir = match env::var_os("CARGO_TARGET_DIR") {
        Some(dir) => PathBuf::from(dir),
        None => PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("..")
            .join("target"),
    };
    target_dir.join("lean_da_cache")
}
