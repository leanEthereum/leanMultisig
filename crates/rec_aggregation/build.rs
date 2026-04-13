use std::path::Path;

use sha3::{Digest, Sha3_256};

fn main() {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed={}", manifest_dir.display());

    let mut py_files: Vec<(String, String)> = Vec::new();
    for entry in std::fs::read_dir(manifest_dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().is_some_and(|ext| ext == "py") {
            let name = path.file_name().unwrap().to_string_lossy().to_string();
            let content = std::fs::read_to_string(&path).unwrap();
            println!("cargo:rerun-if-changed={}", path.display());
            py_files.push((name, content));
        }
    }
    py_files.sort();

    let mut hasher = Sha3_256::new();
    for (name, content) in &py_files {
        hasher.update(name.as_bytes());
        hasher.update(b"\0");
        hasher.update(content.as_bytes());
        hasher.update(b"\0");
    }
    let fingerprint: [u8; 32] = hasher.finalize().into();

    let hex: String = fingerprint.iter().map(|b| format!("{:02x}", b)).collect();
    println!("cargo:rustc-env=REC_AGGREGATION_PY_FINGERPRINT={}", hex);
}
