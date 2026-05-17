"""Validate the Python `verify_gkr_quotient` against the Rust dump.

Regenerate the vectors with:
    cargo test --release -p lean_prover --test dump_gkr_vector -- --nocapture

Then run:
    .venv/bin/python crates/lean_prover/test_gkr.py
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))

from verifier import (  # noqa: E402
    EF,
    Fp,
    MerkleOpening,
    Proof,
    VerifierState,
    prunedpaths_from_json,
    restore_merkle_paths,
    verify_gkr_quotient,
)


def _ef(coords) -> EF:
    return EF([Fp(v) for v in coords])


def run(path: Path) -> bool:
    raw = json.loads(path.read_text())
    transcript = [Fp(v) for v in raw["proof"]["transcript"]]
    openings: list[MerkleOpening] = []
    for bucket in raw["proof"]["merkle_paths"]:
        for r in restore_merkle_paths(prunedpaths_from_json(bucket)):
            openings.append(MerkleOpening(leaf_data=r.leaf_data, path=r.sibling_hashes))
    proof = Proof(transcript=transcript, merkle_openings=openings)

    state = VerifierState(proof)
    try:
        quotient, point, claims_num, claims_den = verify_gkr_quotient(state, raw["n_vars"])
    except Exception as e:
        print(f"  {path.name}: FAILED: {type(e).__name__}: {e}")
        return False

    expected_quotient = _ef(raw["expected_quotient"])
    expected_point = [_ef(p) for p in raw["expected_point"]]
    expected_num = _ef(raw["expected_claims_num"])
    expected_den = _ef(raw["expected_claims_den"])

    ok = True
    if quotient != expected_quotient:
        ok = False
        print(f"  {path.name}: quotient mismatch")
    if len(point) != len(expected_point):
        ok = False
        print(f"  {path.name}: gkr_point length mismatch ({len(point)} vs {len(expected_point)})")
    else:
        for i, (a, b) in enumerate(zip(point, expected_point)):
            if a != b:
                ok = False
                print(f"  {path.name}: gkr_point[{i}] mismatch")
                break
    if claims_num != expected_num:
        ok = False
        print(f"  {path.name}: claims_num mismatch")
    if claims_den != expected_den:
        ok = False
        print(f"  {path.name}: claims_den mismatch")

    if ok:
        print(f"  {path.name}: OK")
    return ok


def main() -> int:
    out_dir = Path(__file__).resolve().parents[2] / "target" / "gkr_test_vectors"
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
