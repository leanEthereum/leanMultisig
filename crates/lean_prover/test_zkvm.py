"""Run the Python `verify_execution` prologue + stacked-PCS parse against
the Rust-generated zkVM test vectors.

Regenerate the vectors with:
    cargo test --release -p lean_prover --test dump_zkvm_vector -- --nocapture

Then run:
    .venv/bin/python crates/lean_prover/test_zkvm.py
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))

from verifier import (  # noqa: E402
    Bytecode,
    Fp,
    MerkleOpening,
    Proof,
    TableInfo,
    prunedpaths_from_json,
    restore_merkle_paths,
    verify_execution,
)


def _load(path: Path):
    raw = json.loads(path.read_text())
    bytecode = Bytecode(
        hash=[Fp(v) for v in raw["bytecode_hash"]],
        log_size=raw["bytecode_log_size"],
    )
    public_input = [Fp(v) for v in raw["public_input"]]
    transcript = [Fp(v) for v in raw["proof"]["transcript"]]
    openings: list[MerkleOpening] = []
    for bucket in raw["proof"]["merkle_paths"]:
        for r in restore_merkle_paths(prunedpaths_from_json(bucket)):
            openings.append(MerkleOpening(leaf_data=r.leaf_data, path=r.sibling_hashes))
    proof = Proof(transcript=transcript, merkle_openings=openings)
    tables = [TableInfo(name=t["name"], n_columns=t["n_columns"]) for t in raw["tables"]]
    return bytecode, public_input, proof, tables


def run(path: Path) -> bool:
    bytecode, public_input, proof, tables = _load(path)
    try:
        partial = verify_execution(bytecode, public_input, proof, tables)
    except Exception as e:
        print(f"  {path.name}: FAILED: {type(e).__name__}: {e}")
        return False
    pc = partial.parsed_commitment
    print(
        f"  {path.name}: OK  "
        f"log_inv_rate={partial.log_inv_rate}, log_memory={partial.log_memory}, "
        f"stacked_n_vars={partial.stacked_n_vars}, "
        f"table_log_heights={partial.table_log_heights}, "
        f"commitment ood_points={len(pc.ood_points)}"
    )
    return True


def main() -> int:
    out_dir = Path(__file__).resolve().parents[2] / "target" / "zkvm_test_vectors"
    vectors = sorted(out_dir.glob("*.json"))
    if not vectors:
        print(f"No test vectors in {out_dir}.")
        return 1
    ok = True
    for v in vectors:
        ok &= run(v)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
