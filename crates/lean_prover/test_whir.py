"""Run the Python WHIR verifier against the Rust-generated test vectors.

Generate the vectors first (in this repo's `target/whir_test_vectors/`):
    cargo test --release -p mt-whir --test dump_test_vectors -- --nocapture
Then run:
    .venv/bin/python crates/lean_prover/test_whir.py
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))

from verifier import (  # noqa: E402
    EF,
    Fp,
    MerkleOpening,
    ParsedCommitment,
    Proof,
    ProofError,
    SparseStatement,
    SparseValue,
    VerifierState,
    prunedpaths_from_json,
    restore_merkle_paths,
    whir_config,
    whir_verify,
)


def _ef(coords: list[int]) -> EF:
    return EF([Fp(v) for v in coords])


def _load(path: Path) -> tuple:
    raw = json.loads(path.read_text())
    statement = [
        SparseStatement(
            total_num_variables=s["total_num_variables"],
            point=[_ef(p) for p in s["point"]],
            values=[SparseValue(v["selector"], _ef(v["value"])) for v in s["values"]],
            is_next=s["is_next"],
        )
        for s in raw["statement"]
    ]
    transcript = [Fp(v) for v in raw["proof"]["transcript"]]
    openings: list[MerkleOpening] = []
    for bucket in raw["proof"]["merkle_paths"]:
        restored = restore_merkle_paths(prunedpaths_from_json(bucket))
        for r in restored:
            openings.append(MerkleOpening(leaf_data=r.leaf_data, path=r.sibling_hashes))
    proof = Proof(transcript=transcript, merkle_openings=openings)
    expected = [_ef(p) for p in raw["expected_folding_randomness"]]
    return raw["num_variables"], raw["log_inv_rate"], statement, proof, expected


def run(path: Path) -> bool:
    num_vars, log_inv_rate, statement, proof, expected = _load(path)
    cfg = whir_config(log_inv_rate, num_vars)
    state = VerifierState(proof)
    parsed = ParsedCommitment(
        num_variables=num_vars,
        root=state.next_base_scalars_vec(8),
        ood_points=state.sample_vec(cfg.commitment_ood_samples) if cfg.commitment_ood_samples > 0 else [],
        ood_answers=[],
    )
    if cfg.commitment_ood_samples > 0:
        parsed.ood_answers = state.next_extension_scalars_vec(cfg.commitment_ood_samples)
    try:
        got = whir_verify(state, cfg, parsed, statement)
    except ProofError as e:
        print(f"  {path.name}: ProofError: {e}")
        return False
    if len(got) != len(expected):
        print(f"  {path.name}: evaluation-point length mismatch ({len(got)} vs {len(expected)})")
        return False
    for i, (a, b) in enumerate(zip(got, expected)):
        if a != b:
            print(f"  {path.name}: evaluation_point[{i}] mismatch (got {a}, expected {b})")
            return False
    print(f"  {path.name}: OK")
    return True


def main() -> int:
    out_dir = Path(__file__).resolve().parents[2] / "target" / "whir_test_vectors"
    skip = {"challenger_sanity.json", "merkle_sanity.json", "state_trace.json", "permute_oracle.json"}
    vectors = sorted(p for p in out_dir.glob("*.json") if p.name not in skip)
    if not vectors:
        print(f"No test vectors in {out_dir}.")
        return 1
    ok = True
    for v in vectors:
        ok &= run(v)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
