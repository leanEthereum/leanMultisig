"""Run the Python `verify_execution` (prologue + stacked-PCS + generic logup)
against the Rust-generated zkVM test vector.

Regenerate the vector with:
    cargo test --release -p lean_prover --test dump_zkvm_vector -- --nocapture

Then run:
    .venv/bin/python crates/lean_prover/test_zkvm.py
"""

import array
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
    tables_from_json,
    verify_execution,
)


def _load_bytecode_mle(json_path: Path, raw: dict) -> list[Fp]:
    bin_path = json_path.parent / raw["bytecode_multilinear_path"]
    data = bin_path.read_bytes()
    n = raw["bytecode_multilinear_len"]
    assert len(data) == n * 4, (len(data), n * 4)
    arr = array.array("I")
    arr.frombytes(data)
    return [Fp(v) for v in arr]


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

    metas = tables_from_json(raw["tables"])
    tables = [
        TableInfo(name=m.name, n_columns=m.n_columns, bus=m.bus, lookups=m.lookups)
        for m in metas
    ]
    bytecode_mle = _load_bytecode_mle(path, raw)
    return bytecode, public_input, proof, tables, raw["constants"], bytecode_mle


def run(path: Path) -> bool:
    bytecode, public_input, proof, tables, constants, bytecode_mle = _load(path)
    try:
        partial = verify_execution(bytecode, public_input, proof, tables, constants, bytecode_mle)
    except Exception as e:
        print(f"  {path.name}: FAILED: {type(e).__name__}: {e}")
        return False
    logup = partial.logup_statements
    print(
        f"  {path.name}: OK  "
        f"log_inv_rate={partial.log_inv_rate}, log_memory={partial.log_memory}, "
        f"stacked_n_vars={partial.stacked_n_vars}, "
        f"gkr_n_vars={logup.total_gkr_n_vars}, "
        f"bytecode_eval_point.len={len(logup.bytecode_evaluation.point)}"
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
