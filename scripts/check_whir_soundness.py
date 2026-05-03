#!/usr/bin/env python3
"""
Verify that the WhirConfig produced by `crates/whir/src/config.rs` achieves
≥ SECURITY_BITS bits of round-by-round soundness, by feeding its parameters
to soundcalc.

Setup (one-time):

    git clone -b custom_shrinking_factor https://github.com/TomWambsgans/soundcalc
    git -C soundcalc checkout 55026468557867ff93071e19ebc88f7eaf3d1ab5

Run:

    python3 scripts/check_whir_soundness.py            # sweep
    python3 scripts/check_whir_soundness.py --verbose  # + worst rounds per cell

soundcalc must live inside this repo (`./soundcalc`, gitignored) or next to it
(`../soundcalc`). The Rust binary `dump_whir_config` is built automatically.

This uses the `custom_shrinking_factor` fork, which lets us pass per-iteration
folding factors (k_i) and domain shrink factors (d_i) directly to `WHIRConfig`.
The only override we still need is per-iteration JBR multiplicity `m`, which
soundcalc exposes through a single `regime` argument — we subclass to plug a
different regime per iteration.
"""
import json
import math
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOUNDCALC_CANDIDATES = [ROOT / "soundcalc", ROOT.parent / "soundcalc"]
SOUNDCALC = next((p for p in SOUNDCALC_CANDIDATES if (p / "soundcalc").is_dir()), None)
if SOUNDCALC is None:
    raise SystemExit(
        "soundcalc not found. Clone https://github.com/TomWambsgans/soundcalc into this repo:\n"
        f"  git clone -b custom_shrinking_factor https://github.com/TomWambsgans/soundcalc {ROOT / 'soundcalc'}\n"
        "(commit 55026468557867ff93071e19ebc88f7eaf3d1ab5 is known good)"
    )
sys.path.insert(0, str(SOUNDCALC))

from soundcalc.common.fields import GOLDILOCKS_3  # noqa: E402
from soundcalc.pcs.whir import WHIR, WHIRConfig  # noqa: E402
from soundcalc.proxgaps.johnson_bound import JohnsonBoundRegime  # noqa: E402

SECURITY_BITS = 128
FIELD = GOLDILOCKS_3
DUMP_BIN = ROOT / "target" / "release" / "dump_whir_config"

NUM_VARS_RANGE = range(15, 33)
LOG_INV_RATE_RANGE = range(1, 5)


def ensure_binary():
    """Build the Rust dumper if missing or stale (cargo no-ops if up-to-date)."""
    print(f"{DIM}Building dump_whir_config...{RESET}", file=sys.stderr)
    subprocess.run(
        ["cargo", "build", "--release", "--bin", "dump_whir_config"],
        cwd=ROOT, check=True,
    )


def fetch_config(num_variables, log_inv_rate):
    proc = subprocess.run(
        [str(DUMP_BIN), "--num-variables", str(num_variables), "--log-inv-rate", str(log_inv_rate)],
        capture_output=True, text=True,
    )
    if proc.returncode != 0:
        raise RuntimeError((proc.stderr.strip().splitlines() or ["rust panic"])[0])
    return json.loads(proc.stdout)


def _build_whir_config(cfg):
    """Translate the Rust dump's `codewords` array into a soundcalc `WHIRConfig`."""
    cws = cfg["codewords"]
    M = len(cws)

    folding_factors = [c["fold_factor"] for c in cws]

    # Reconstruct log_inv_rates and derive d_i from the recurrence
    #     log_inv_rates[i+1] = log_inv_rates[i] + (k_i - d_i)
    # log_inv_rates[i] is the rate at the *start* of iteration i.
    # The dump emits log_inv_rate as the rate at iteration i (i.e. of the
    # codeword that round i queries); for the implicit "final" iteration
    # M-1 we assume d_{M-1} = 1 (matches our Rust: only round 0 differs).
    log_inv_rates = [c["log_inv_rate"] for c in cws] + [
        cws[-1]["log_inv_rate"] + cws[-1]["fold_factor"] - 1
    ]
    domain_log_shrink_factors = [
        folding_factors[i] - (log_inv_rates[i + 1] - log_inv_rates[i]) for i in range(M)
    ]

    return WHIRConfig(
        # hash_size_bits only affects proof-size estimation, not soundness.
        hash_size_bits=256,
        log_inv_rate=cws[0]["log_inv_rate"],
        num_iterations=M,
        folding_factors=folding_factors,
        domain_log_shrink_factors=domain_log_shrink_factors,
        field=FIELD,
        log_degree=cws[0]["num_vars"],
        # No batching at the WHIR layer (stacking happens above).
        batch_size=1,
        power_batching=True,
        grinding_batching_phase=0,
        constraint_degree=cfg["constraint_degree"],
        grinding_bits_folding=[[c["fold_pow"]] * c["fold_factor"] for c in cws],
        num_queries=[c["queries"] for c in cws],
        grinding_bits_queries=[c["query_pow"] for c in cws],
        num_ood_samples=[c["ood_samples"] for c in cws[1:]],
        grinding_bits_ood=[0] * (M - 1),
    )


# soundcalc's WHIR ties soundness analysis to a single `ProximityGapsRegime`,
# but our Rust picks an optimal JBR multiplicity `m` per round. We subclass
# to use a per-iteration regime in the two methods that consult it.
class PerIterationRegimeWHIR(WHIR):
    def __init__(self, cfg):
        super().__init__(_build_whir_config(cfg))
        self._regimes = [
            JohnsonBoundRegime(FIELD, explicit_m=c["m"]) for c in cfg["codewords"]
        ]

    def _get_delta_for_iteration(self, iteration, _regime):
        reg = self._regimes[iteration]
        delta = 1.0
        for s in range(self.folding_factors[iteration] + 1):
            (rate, dimension) = self._get_code_for_iteration_and_round(iteration, s)
            delta = min(delta, reg.get_proximity_parameter(rate, dimension))
        return delta

    def _get_list_size_for_iteration_and_round(self, iteration, round, _regime):
        reg = self._regimes[iteration]
        (rate, dimension) = self._get_code_for_iteration_and_round(iteration, round)
        return reg.get_max_list_size(rate, dimension)

    def soundness_in_bits(self):
        levels = {}
        for s in range(1, self.folding_factors[0] + 1):
            levels[f"fold(0,s={s})"] = -math.log2(self._epsilon_fold(0, s, self._regimes[0]))
        for i in range(1, self.num_iterations):
            levels[f"OOD(i={i})"] = -math.log2(self._epsilon_out(i, self._regimes[i]))
            levels[f"shift(i={i})"] = -math.log2(self._epsilon_shift(i, self._regimes[i]))
            for s in range(1, self.folding_factors[i] + 1):
                levels[f"fold(i={i},s={s})"] = -math.log2(self._epsilon_fold(i, s, self._regimes[i]))
        levels["fin"] = -math.log2(self._epsilon_final(self._regimes[-1]))
        return levels


GREEN, RED, DIM, BOLD, RESET = "\033[32m", "\033[31m", "\033[2m", "\033[1m", "\033[0m"


def main():
    ensure_binary()
    print(f"{BOLD}WHIR soundness sweep — JohnsonBound, target {SECURITY_BITS} bits{RESET}")
    print(f"{DIM}Field: {FIELD.name} · params dumped from Rust{RESET}\n")

    header = f"  {'num_vars':>8} │ " + " │ ".join(f"r={r:<2d}  " for r in LOG_INV_RATE_RANGE)
    print(header + "\n  " + "─" * (len(header) - 2))

    verbose = "--verbose" in sys.argv
    fail = False
    # Goldilocks two-adicity is 32; after the initial fold of 7 the domain has
    # 2^(num_vars + log_inv_rate - 7) elements, which must fit. So skip cells
    # with num_vars + log_inv_rate > 39.
    max_sum = FIELD.two_adicity + 7

    for nv in NUM_VARS_RANGE:
        cells = []
        for r in LOG_INV_RATE_RANGE:
            if nv + r > max_sum:
                cells.append(f"{DIM}  —   {RESET}")
                continue
            try:
                bits = PerIterationRegimeWHIR(fetch_config(nv, r)).soundness_in_bits()
                worst_name, worst_b = min(bits.items(), key=lambda kv: kv[1])
                cells.append(f"{GREEN if worst_b >= SECURITY_BITS else RED}{worst_b:6.2f}{RESET}")
                fail |= worst_b < SECURITY_BITS
                if verbose:
                    print(f"  ↳ ({nv},{r}) min={worst_b:.2f} ({worst_name})")
                    for name, b in sorted(bits.items(), key=lambda kv: kv[1])[:5]:
                        print(f"      {name:<22s} {b:6.2f}")
            except Exception as e:  # noqa: BLE001
                cells.append(f"{RED}  ERR {RESET}")
                if verbose:
                    print(f"  ↳ ({nv},{r}) ERROR: {e}")
        print(f"  {nv:>8d} │ " + " │ ".join(cells))

    print()
    print(f"{RED}✗ some configurations fall below {SECURITY_BITS} bits.{RESET}" if fail
          else f"{GREEN}✓ all configurations meet {SECURITY_BITS}-bit soundness per soundcalc.{RESET}")
    return 1 if fail else 0


if __name__ == "__main__":
    sys.exit(main())
