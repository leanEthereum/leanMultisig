#!/bin/bash
# Runs the README benchmark scenarios and renders the markdown tables to
# new_tables.md (next to this script). Scenario logs go to stderr.
#
# Requires: jq

OUTPUT_FILE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/new_tables.md"

set -euo pipefail

if ! command -v jq >/dev/null 2>&1; then
    echo "error: jq is required (brew install jq)" >&2
    exit 1
fi

# Run a benchmark scenario and echo the BenchmarkReport JSON.
# Args: <features-or-empty> <subcommand> [extra args...]
# Logs the exact cargo command being run to stderr.
run_bench() {
    local features="$1"
    shift
    local cmd
    if [[ -n "$features" ]]; then
        cmd="cargo run --release --features $features -- $* --json"
    else
        cmd="cargo run --release -- $* --json"
    fi
    echo -e "\033[32m$cmd\033[0m" >&2
    if [[ -n "$features" ]]; then
        cargo run --release --features "$features" -q -- "$@" --json
    else
        cargo run --release -q -- "$@" --json
    fi | grep -E '^\{' | tail -n 1
}

# "$THROUGHPUT XMSS/s - $PROOF KiB" extracted from a leaf XMSS run.
xmss_cell() {
    echo "$1" | jq -r '
        (.nodes | map(select(.path == [])) | .[0].stats) as $r
        | "\((($r.n_xmss / $r.time_secs) + 0.5) | floor) XMSS/s - \($r.proof_kib) KiB"
    '
}

# "{root_time}s = 'n x {root_time/n}s' - {proof_kib} KiB" for a recursion run.
# Time is the root recursion step's time; n is the number of leaves; the
# per-leaf figure is the root time divided by n.
recursion_cell() {
    echo "$1" | jq -r '
        (.nodes | map(select(.path != []))) as $leaves
        | (.nodes | map(select(.path == [])) | .[0]) as $root
        | ($leaves | length) as $n
        | $root.stats.time_secs as $root_t
        | (if $n > 0 then $root_t / $n else 0 end) as $per_leaf
        | "\(($root_t * 100 + 0.5 | floor) / 100)s = \($n) x \(($per_leaf * 100 + 0.5 | floor) / 100)s - \($root.stats.proof_kib) KiB"
    '
}

# --- XMSS aggregation runs ---
xmss_r1_proven=$(run_bench "" xmss --n-signatures 1400 --log-inv-rate 1); sleep 1
xmss_r2_proven=$(run_bench "" xmss --n-signatures 1400 --log-inv-rate 2); sleep 1
xmss_r1_conj=$(run_bench prox-gaps-conjecture xmss --n-signatures 1400 --log-inv-rate 1); sleep 1
xmss_r2_conj=$(run_bench prox-gaps-conjecture xmss --n-signatures 1400 --log-inv-rate 2); sleep 1

# --- Recursion runs: 3 fan-ins x 2 rates x 2 regimes = 12 runs ---
# Stored in flat shell variables `rec_<n>_<rate>_<regime>` for bash 3.2 compatibility.
for n in 2 3 4; do
    for rate in 1 2; do
        out=$(run_bench "" recursion --n "$n" --log-inv-rate "$rate")
        printf -v "rec_${n}_${rate}_proven" '%s' "$out"
        sleep 1
        out=$(run_bench prox-gaps-conjecture recursion --n "$n" --log-inv-rate "$rate")
        printf -v "rec_${n}_${rate}_conj" '%s' "$out"
        sleep 1
    done
done

rec_get() { local v="rec_$1"; echo "${!v}"; }

# --- Render ---
{
    echo
    echo "### XMSS aggregation"
    echo
    echo "| WHIR rate          | Proven Regime        | Proximity Gaps Conjecture           |"
    echo "| ------------------ | --------------------- | ----------------------------------- |"
    echo "| 1/2                | $(xmss_cell "$xmss_r1_proven") | $(xmss_cell "$xmss_r1_conj") |"
    echo "| 1/4                | $(xmss_cell "$xmss_r2_proven") | $(xmss_cell "$xmss_r2_conj") |"
    echo
    echo "### n-to-1 recursion"
    echo
    echo "| n | WHIR rate | Proven Regime                       | Proximity Gaps Conjecture           |"
    echo "| - | --------- | ----------------------------------- | ----------------------------------- |"
    for n in 2 3 4; do
        for rate in 1 2; do
            rate_label="1/$((1 << rate))"
            echo "| $n | $rate_label       | $(recursion_cell "$(rec_get "${n}_${rate}_proven")") | $(recursion_cell "$(rec_get "${n}_${rate}_conj")") |"
        done
    done
} >"$OUTPUT_FILE"

echo -e "\033[32mWrote $OUTPUT_FILE\033[0m" >&2
