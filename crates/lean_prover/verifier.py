"""
Setup:
    uv venv .venv --python 3.12
    VIRTUAL_ENV=.venv uv pip install "git+https://github.com/leanEthereum/leanSpec.git"
    .venv/bin/python crates/lean_prover/verifier.py
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterable, Sequence

from lean_spec.subspecs.koalabear import Fp, P
from lean_spec.subspecs.poseidon1 import PARAMS_16, Poseidon1

SECURITY_BITS = 124
MAX_NUM_VARIABLES_TO_SEND_COEFFS = 8
WHIR_INITIAL_FOLDING_FACTOR = 7
WHIR_SUBSEQUENT_FOLDING_FACTOR = 5
RS_DOMAIN_INITIAL_REDUCTION_FACTOR = 5

# Poseidon16 challenger parameters (challenger.rs).
# Note: this branch uses the older "compression with domain separator" design.
# The state is just the RATE-sized output of the last permute; sampling pulls
# fresh hashes by re-permuting with a per-call domain separator. There is no
# `rate_fresh` flag and no `duplex` call.
RATE = 8
WIDTH = 16
CAPACITY = WIDTH - RATE
DIGEST_LEN_FE = 8
DIGEST_ELEMS = 8

# Hardcoded leanVM SNARK domain separator (lean_prover/src/lib.rs)
SNARK_DOMAIN_SEP = [
    Fp(v) for v in (
        130704175, 1303721200, 493664240, 1035493700,
        2063844858, 1410214009, 1938905908, 1696767928,
    )
]

# Bounds (mirrors lean_vm/src/core/constants.rs).
MIN_WHIR_LOG_INV_RATE = 1
MAX_WHIR_LOG_INV_RATE = 4
MIN_LOG_MEMORY_SIZE = 16
MAX_LOG_MEMORY_SIZE = 26
MIN_LOG_N_ROWS_PER_TABLE = 8
MIN_BYTECODE_LOG_SIZE = 8
BASE_TWO_ADICITY = 24  # KoalaBear

# WHIR config table dumped by `cargo test -p lean_prover --test dump_whir_configs`.
# Lives next to this file.
WHIR_CONFIGS_PATH = "whir_configs.json"


# ---------------------------------------------------------------------------
# Error type
# ---------------------------------------------------------------------------


class ProofError(Exception):
    """Mirrors backend::ProofError."""


# ---------------------------------------------------------------------------
# Quintic extension field: EF = Fp[X] / (X^5 + X^2 - 1)
# Reduction rule: X^5 = 1 - X^2.
# ---------------------------------------------------------------------------


class EF:
    """Element of the degree-5 extension of KoalaBear.

    Stored as 5 base coefficients `c[0..5]` representing `c0 + c1 X + ... + c4 X^4`.
    Irreducible polynomial: X^5 + X^2 - 1, i.e. X^5 ≡ 1 - X^2.
    """

    __slots__ = ("c",)
    DIMENSION = 5

    def __init__(self, coeffs: Sequence[Fp]):
        assert len(coeffs) == 5
        self.c = tuple(coeffs)

    # --- constructors -----------------------------------------------------

    @staticmethod
    def zero() -> "EF":
        return EF([Fp(0)] * 5)

    @staticmethod
    def one() -> "EF":
        return EF([Fp(1), Fp(0), Fp(0), Fp(0), Fp(0)])

    @staticmethod
    def from_base(x: Fp) -> "EF":
        return EF([x, Fp(0), Fp(0), Fp(0), Fp(0)])

    @staticmethod
    def from_basis_coefficients(coeffs: Sequence[Fp]) -> "EF":
        return EF(coeffs)

    # --- arithmetic -------------------------------------------------------

    def __add__(self, other) -> "EF":
        if isinstance(other, Fp):
            return EF([self.c[0] + other, *self.c[1:]])
        return EF([a + b for a, b in zip(self.c, other.c)])

    __radd__ = __add__

    def __sub__(self, other) -> "EF":
        if isinstance(other, Fp):
            return EF([self.c[0] - other, *self.c[1:]])
        return EF([a - b for a, b in zip(self.c, other.c)])

    def __rsub__(self, other) -> "EF":
        # other - self, where other is Fp
        return EF([other - self.c[0], *[-c for c in self.c[1:]]])

    def __neg__(self) -> "EF":
        return EF([-a for a in self.c])

    def __mul__(self, other: "EF | Fp | int") -> "EF":
        if isinstance(other, Fp):
            return EF([a * other for a in self.c])
        if isinstance(other, int):
            f = Fp(other % P)
            return EF([a * f for a in self.c])
        # Schoolbook poly mul mod (X^5 + X^2 - 1).
        a, b = self.c, other.c
        prod = [Fp(0)] * 9  # degree up to 8
        for i in range(5):
            for j in range(5):
                prod[i + j] = prod[i + j] + a[i] * b[j]
        # Reduce: X^5 = 1 - X^2,  X^k for k >= 5 reduced repeatedly.
        for k in range(8, 4, -1):  # 8,7,6,5
            coef = prod[k]
            if int(coef.value) == 0:
                continue
            # X^k = X^(k-5) * X^5 = X^(k-5) * (1 - X^2)
            prod[k] = Fp(0)
            prod[k - 5] = prod[k - 5] + coef
            prod[k - 3] = prod[k - 3] - coef
        return EF(prod[:5])

    __rmul__ = __mul__

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, EF):
            return NotImplemented
        return self.c == other.c

    def __hash__(self) -> int:
        return hash(self.c)

    def __repr__(self) -> str:
        return f"EF({[int(x.value) for x in self.c]})"

    def is_zero(self) -> bool:
        return all(int(x.value) == 0 for x in self.c)

    def inv(self) -> "EF":
        """Inverse via Fermat: a^(q-2) where q = P^5. Slow but simple."""
        if self.is_zero():
            raise ZeroDivisionError("EF inverse of zero")
        exp = P ** 5 - 2
        return self.pow(exp)

    def pow(self, n: int) -> "EF":
        if n < 0:
            return self.inv().pow(-n)
        result = EF.one()
        base = self
        while n > 0:
            if n & 1:
                result = result * base
            base = base * base
            n >>= 1
        return result


# ---------------------------------------------------------------------------
# Poseidon16-based Challenger (duplex sponge)
# ---------------------------------------------------------------------------


_POSEIDON16 = Poseidon1(PARAMS_16)


def poseidon16_permute(state: list[Fp]) -> list[Fp]:
    """Apply the Poseidon16 permutation to a length-WIDTH state.

    NOTE: this is the bare permutation. For the Davies-Meyer-style
    *compression* used by Merkle trees use `poseidon16_compress_in_place`.
    The Fiat-Shamir challenger uses the bare permutation (no feed-forward).
    """
    assert len(state) == WIDTH
    return _POSEIDON16.permute(state)


def poseidon16_compress_in_place(state: list[Fp]) -> list[Fp]:
    """`compress_in_place`: out = permute(state) + state (feed-forward)."""
    assert len(state) == WIDTH
    permuted = _POSEIDON16.permute(state)
    return [a + b for a, b in zip(permuted, state)]


def poseidon16_compress(left: Sequence[Fp], right: Sequence[Fp]) -> list[Fp]:
    """2:1 Merkle compression: `compress_in_place(left || right)[:DIGEST_ELEMS]`."""
    assert len(left) == DIGEST_ELEMS and len(right) == DIGEST_ELEMS
    return poseidon16_compress_in_place(list(left) + list(right))[:DIGEST_ELEMS]


def hash_slice(data: Sequence[Fp]) -> list[Fp]:
    """`symetric::hash_slice` with WIDTH=16, RATE=OUT=8 (right-to-left absorbing).

    Uses the same `compress_in_place` (feed-forward) primitive as Merkle, NOT
    the bare permutation used by the challenger.
    """
    assert len(data) % RATE == 0
    n_chunks = len(data) // RATE
    assert n_chunks >= 2
    state = list(data[len(data) - WIDTH :])
    state = poseidon16_compress_in_place(state)
    for chunk_idx in range(n_chunks - 3, -1, -1):
        offset = chunk_idx * RATE
        state = state[:CAPACITY] + list(data[offset : offset + RATE])
        state = poseidon16_compress_in_place(state)
    return state[:DIGEST_ELEMS]


class Challenger:
    """Poseidon16 challenger (old "compression + domain-separator" design).

    Mirrors `fiat_shamir::challenger` on this branch:
      - `state` is a length-RATE buffer (8 elements).
      - `observe(value)`: `state = permute(state || value)[:RATE]`.
      - `sample_many(n)`: hash `(domain_sep_i || state)` for `i ∈ 0..=n`;
        return the first `n`, advance `state` to the last one.
    """

    def __init__(self) -> None:
        self.state: list[Fp] = [Fp(0)] * RATE

    def observe(self, value: Sequence[Fp]) -> None:
        assert len(value) == RATE
        out = poseidon16_compress_in_place(list(self.state) + list(value))
        self.state = out[:RATE]

    def observe_many(self, scalars: Sequence[Fp]) -> None:
        for i in range(0, len(scalars), RATE):
            chunk = list(scalars[i : i + RATE])
            if len(chunk) < RATE:
                chunk = chunk + [Fp(0)] * (RATE - len(chunk))
            self.observe(chunk)

    # Alias matching `Challenger::observe_scalars` on this branch.
    observe_scalars = observe_many

    def sample_many(self, n: int) -> list[list[Fp]]:
        sampled: list[list[Fp]] = []
        last: list[Fp] | None = None
        for i in range(n + 1):
            domain_sep = [Fp(i)] + [Fp(0)] * (RATE - 1)
            hashed = poseidon16_compress_in_place(domain_sep + list(self.state))[:RATE]
            if i < n:
                sampled.append(hashed)
            else:
                last = hashed
        if last is not None:
            self.state = last
        return sampled

    def sample_ef_vec(self, n: int) -> list[EF]:
        """Mirrors utils::sample_vec — pulls ceil(n*5/8) blocks, takes first n*5."""
        n_blocks = (n * EF.DIMENSION + RATE - 1) // RATE
        flat: list[Fp] = []
        for block in self.sample_many(n_blocks):
            flat.extend(block)
        flat = flat[: n * EF.DIMENSION]
        return [EF(flat[i : i + EF.DIMENSION]) for i in range(0, len(flat), EF.DIMENSION)]

    def sample_ef(self) -> EF:
        return self.sample_ef_vec(1)[0]

    def sample_in_range(self, bits: int, n_samples: int) -> list[int]:
        """Mirrors challenger::sample_in_range — not perfectly uniform."""
        assert bits < 31
        n_blocks = (n_samples + RATE - 1) // RATE
        flat: list[Fp] = []
        for block in self.sample_many(n_blocks):
            flat.extend(block)
        mask = (1 << bits) - 1
        return [int(x.value) & mask for x in flat[:n_samples]]


# ---------------------------------------------------------------------------
# Proof container + VerifierState (transcript reader)
# ---------------------------------------------------------------------------


@dataclass
class MerkleOpening:
    """Restored Merkle opening: matches fiat_shamir::transcript::MerkleOpening."""

    leaf_data: list[Fp]
    path: list[list[Fp]]  # each sibling is a length-DIGEST_ELEMS digest


@dataclass
class Proof:
    """Verifier-side proof: matches backend::Proof.

    `merkle_openings` is the RESTORED list of openings (post-pruning), in the
    order the verifier consumes them.
    """

    transcript: list[Fp]
    merkle_openings: list[MerkleOpening] = field(default_factory=list)


class VerifierState:
    """Mirrors fiat_shamir::verifier::VerifierState exactly."""

    def __init__(self, proof: Proof) -> None:
        self.challenger = Challenger()
        self.transcript: list[Fp] = list(proof.transcript)
        self.offset = 0
        self.merkle_openings: list[MerkleOpening] = list(proof.merkle_openings)
        self.merkle_opening_index = 0
        self.raw_transcript: list[Fp] = []

    # ---- internal helpers ----------------------------------------------

    def _read(self, n: int) -> list[Fp]:
        if self.offset + n > len(self.transcript):
            raise ProofError("ExceededTranscript")
        out = self.transcript[self.offset : self.offset + n]
        self.offset += n
        return out

    def _absorb_and_record(self, scalars: list[Fp]) -> None:
        self.challenger.observe_many(scalars)
        self.raw_transcript.extend(scalars)
        padded = (len(scalars) + RATE - 1) // RATE * RATE
        self.raw_transcript.extend([Fp(0)] * (padded - len(scalars)))

    # ---- FSVerifier trait surface --------------------------------------

    def observe_scalars(self, scalars: Sequence[Fp]) -> None:
        self.challenger.observe_many(list(scalars))

    def duplex(self) -> None:
        """No-op on this branch — the older challenger has no rate-staleness
        notion, so duplex calls in the WHIR verifier are simply skipped."""
        pass

    def next_base_scalars_vec(self, n: int) -> list[Fp]:
        scalars = self._read(n)
        self._absorb_and_record(scalars)
        return scalars

    def next_extension_scalars_vec(self, n: int) -> list[EF]:
        flat = self.next_base_scalars_vec(n * EF.DIMENSION)
        return [EF(flat[i : i + EF.DIMENSION]) for i in range(0, len(flat), EF.DIMENSION)]

    def next_extension_scalar(self) -> EF:
        return self.next_extension_scalars_vec(1)[0]

    def sample(self) -> EF:
        return self.challenger.sample_ef()

    def sample_vec(self, n: int) -> list[EF]:
        return self.challenger.sample_ef_vec(n)

    def sample_in_range(self, bits: int, n_samples: int) -> list[int]:
        return self.challenger.sample_in_range(bits, n_samples)

    def next_merkle_opening(self) -> MerkleOpening:
        if self.merkle_opening_index >= len(self.merkle_openings):
            raise ProofError("ExceededTranscript: no more Merkle openings")
        op = self.merkle_openings[self.merkle_opening_index]
        self.merkle_opening_index += 1
        return op

    def check_pow_grinding(self, bits: int) -> None:
        if bits == 0:
            return
        witness = self._read(1)
        self.challenger.observe_many(witness)
        # OLD challenger: state is the RATE-sized output of the last permute;
        # grinding checks state[0].
        if int(self.challenger.state[0].value) & ((1 << bits) - 1) != 0:
            raise ProofError("InvalidGrindingWitness")
        self.raw_transcript.append(witness[0])
        self.raw_transcript.extend([Fp(0)] * (RATE - 1))

    def next_sumcheck_polynomial(
        self,
        n_coeffs: int,
        claimed_sum: EF,
        eq_alpha: EF | None,
    ) -> list[EF]:
        """Mirrors `verifier::next_sumcheck_polynomial`.

        With `eq_alpha=None`: prover sends h(X) of `n_coeffs` coeffs, omitting
        `c0` (recovered from `claimed_sum = h(0) + h(1)`). We read
        `(n_coeffs-1) * 5` base scalars, recover `c0`, and absorb the full
        flattened polynomial.

        With `eq_alpha=Some(α)`: prover sends a "bare" polynomial of
        `n_coeffs - 1` coefficients; the verifier recovers `h0` and expands to
        the full degree polynomial via `expand_bare_to_full`.
        """
        if eq_alpha is None:
            rest = self.next_extension_scalars_vec_no_record(n_coeffs - 1)
            c0 = _ef_halve(claimed_sum - _ef_sum(rest))
            full = [c0] + rest
            self._absorb_and_record(_flatten_ef_list(full))
            return full

        # eq_alpha path
        rest_scalars = self._read((n_coeffs - 2) * EF.DIMENSION)
        rest_bare = [
            EF(rest_scalars[i : i + EF.DIMENSION])
            for i in range(0, len(rest_scalars), EF.DIMENSION)
        ]
        h0 = claimed_sum - eq_alpha * _ef_sum(rest_bare)
        bare = [h0] + rest_bare
        full_coeffs = _expand_bare_to_full(bare, eq_alpha)
        self._absorb_and_record(_flatten_ef_list(full_coeffs))
        return full_coeffs

    def next_extension_scalars_vec_no_record(self, n: int) -> list[EF]:
        """Read `n` extension scalars but DON'T record/absorb yet — caller does."""
        flat = self._read(n * EF.DIMENSION)
        return [EF(flat[i : i + EF.DIMENSION]) for i in range(0, len(flat), EF.DIMENSION)]


# ---------------------------------------------------------------------------
# Bytecode (minimal placeholder) + helpers
# ---------------------------------------------------------------------------


@dataclass
class Bytecode:
    """Subset of lean_vm::Bytecode needed by the verifier."""

    hash: list[Fp]                       # 8 base elements
    log_size: int                        # log2 of bytecode length
    instructions_multilinear: object | None = None  # TODO: multilinear repr

    def log_size_(self) -> int:
        return self.log_size


poseidon16_compress_pair = poseidon16_compress  # alias for utils::poseidon16_compress_pair


# --- small helpers used by next_sumcheck_polynomial ---


def _halve_fp() -> Fp:
    # Multiplicative inverse of 2 mod P. Computed once at import time.
    return Fp(pow(2, P - 2, P))


_HALVE_FP = _halve_fp()


def _ef_halve(x: EF) -> EF:
    return EF([c * _HALVE_FP for c in x.c])


def _ef_sum(xs: Sequence[EF]) -> EF:
    acc = EF.zero()
    for x in xs:
        acc = acc + x
    return acc


def _flatten_ef_list(xs: Sequence[EF]) -> list[Fp]:
    out: list[Fp] = []
    for x in xs:
        out.extend(x.c)
    return out


def _expand_bare_to_full(bare: list[EF], alpha: EF) -> list[EF]:
    """utils::expand_bare_to_full: g(X) = eq(α, X) * h(X)."""
    one_minus_alpha = EF.one() - alpha
    two_alpha_minus_one = (alpha + alpha) - EF.one()
    d = len(bare) - 1
    full: list[EF] = [one_minus_alpha * bare[0]]
    for k in range(1, d + 1):
        full.append(one_minus_alpha * bare[k] + two_alpha_minus_one * bare[k - 1])
    full.append(two_alpha_minus_one * bare[d])
    return full


def log2_ceil_usize(x: int) -> int:
    if x <= 1:
        return 0
    return (x - 1).bit_length()


def log2_strict_usize(x: int) -> int:
    assert x > 0 and (x & (x - 1)) == 0, f"{x} is not a power of two"
    return x.bit_length() - 1


def padd_with_zero_to_next_power_of_two(values: Sequence[Fp]) -> list[Fp]:
    if not values:
        return [Fp(0)]
    n = 1
    while n < len(values):
        n <<= 1
    return list(values) + [Fp(0)] * (n - len(values))


# ---------------------------------------------------------------------------
# Merkle: hashing primitives, pruned-paths restoration, Merkle verify.
# Mirrors symetric::merkle + fiat_shamir::merkle_pruning.
# ---------------------------------------------------------------------------


@dataclass
class MerklePath:
    """Mirror of fiat_shamir::MerklePath (the un-pruned form)."""

    leaf_data: list[Fp]
    sibling_hashes: list[list[Fp]]  # each entry has DIGEST_ELEMS Fp
    leaf_index: int


@dataclass
class PrunedMerklePaths:
    """Mirror of fiat_shamir::PrunedMerklePaths — input to restore()."""

    merkle_height: int
    original_order: list[int]
    leaf_data: list[list[Fp]]
    paths: list[tuple[int, list[list[Fp]]]]  # (leaf_index, siblings) with skips
    n_trailing_zeros: int


def _lca_level(a: int, b: int) -> int:
    """Number of bits needed to differ — i.e., ceiling-LCA level over the tree."""
    diff = a ^ b
    return diff.bit_length()


def restore_merkle_paths(p: PrunedMerklePaths) -> list[MerklePath]:
    """Port of `merkle_pruning::restore` (fiat_shamir).

    Reconstructs full sibling arrays from the pruned form using leaf hashing
    and 2:1 compression (Poseidon16). Raises ProofError on malformed inputs.
    """

    h = p.merkle_height
    if h >= 32:
        raise ProofError("Merkle height too large")
    if p.n_trailing_zeros > 1024:
        raise ProofError("Merkle leaf trailing-zero count too large")

    leaf_data = [list(d) + [Fp(0)] * p.n_trailing_zeros for d in p.leaf_data]
    n = len(p.paths)

    def levels(i: int) -> int:
        if i == 0:
            return h
        return _lca_level(p.paths[i - 1][0], p.paths[i][0])

    def skip(i: int) -> int | None:
        if i + 1 < n:
            return _lca_level(p.paths[i][0], p.paths[i + 1][0]) - 1
        return None

    # Backward pass: build subtree hashes.
    subtree_hashes: list[list[list[Fp]]] = [[] for _ in range(n)]
    for i in range(n - 1, -1, -1):
        leaf_idx, stored = p.paths[i]
        if leaf_idx >= (1 << h):
            raise ProofError("Merkle leaf index out of range")
        stored_iter = iter(stored)
        cur = hash_slice(leaf_data[i])
        subtree_hashes[i].append(list(cur))
        for lvl in range(levels(i)):
            if skip(i) == lvl:
                try:
                    sibling = subtree_hashes[i + 1][lvl]
                except IndexError as e:
                    raise ProofError("Merkle restore: missing sibling") from e
            else:
                try:
                    sibling = next(stored_iter)
                except StopIteration as e:
                    raise ProofError("Merkle restore: stored siblings exhausted") from e
            if ((leaf_idx >> lvl) & 1) == 0:
                cur = poseidon16_compress(cur, sibling)
            else:
                cur = poseidon16_compress(sibling, cur)
            subtree_hashes[i].append(list(cur))

    # Forward pass: build the full sibling lists.
    restored: list[MerklePath] = []
    for i in range(n):
        leaf_idx, stored = p.paths[i]
        stored_iter = iter(stored)
        siblings: list[list[Fp]] = []
        for lvl in range(levels(i)):
            if skip(i) == lvl:
                sibling = subtree_hashes[i + 1][lvl]
            else:
                try:
                    sibling = next(stored_iter)
                except StopIteration as e:
                    raise ProofError("Merkle restore: stored siblings exhausted (fwd)") from e
            siblings.append(list(sibling))
        if restored:
            # Reuse the previous restored path's siblings for the levels above.
            siblings.extend(restored[-1].sibling_hashes[levels(i) :])
        restored.append(MerklePath(leaf_data=leaf_data[i], sibling_hashes=siblings, leaf_index=leaf_idx))

    # Reorder by original_order.
    return [restored[idx] for idx in p.original_order]


def merkle_verify_path(
    commit: list[Fp],
    log_height: int,
    index: int,
    opened_values: Sequence[Fp],
    opening_proof: Sequence[list[Fp]],
) -> bool:
    """Mirror of symetric::merkle::merkle_verify (length-DIGEST_ELEMS digests)."""

    if len(opening_proof) != log_height:
        return False
    cur = hash_slice(list(opened_values))
    idx = index
    for sibling in opening_proof:
        if idx & 1 == 0:
            cur = poseidon16_compress(cur, sibling)
        else:
            cur = poseidon16_compress(sibling, cur)
        idx >>= 1
    return list(commit) == list(cur)


def prunedpaths_from_json(obj: dict) -> PrunedMerklePaths:
    """Helper for test vectors: parse the JSON shape dumped by Rust."""
    return PrunedMerklePaths(
        merkle_height=obj["merkle_height"],
        original_order=list(obj["original_order"]),
        leaf_data=[[Fp(v) for v in chunk] for chunk in obj["leaf_data"]],
        paths=[(p["leaf_index"], [[Fp(v) for v in s] for s in p["siblings"]]) for p in obj["paths"]],
        n_trailing_zeros=obj["n_trailing_zeros"],
    )


# ---------------------------------------------------------------------------
# WHIR polynomial primitives (poly + whir crates)
# ---------------------------------------------------------------------------


def expand_from_univariate(x: EF, num_variables: int) -> list[EF]:
    """[x, x^2, x^4, ..., x^{2^{n-1}}] — matches MultilinearPoint::expand_from_univariate."""
    out: list[EF] = []
    cur = x
    for _ in range(num_variables):
        out.append(cur)
        cur = cur * cur
    return out


def eq_poly_outside(a: Sequence[EF], b: Sequence[EF]) -> EF:
    """Π (1 + 2 a_i b_i − a_i − b_i)  (eq polynomial)."""
    assert len(a) == len(b)
    one = EF.one()
    acc = one
    for x, y in zip(a, b):
        acc = acc * (one + (x * y) + (x * y) - x - y)
    return acc


def next_mle(x: Sequence[EF], y: Sequence[EF]) -> EF:
    """Port of poly::next_mle (the "next" multilinear on the boolean cube)."""
    assert len(x) == len(y)
    n = len(x)
    one = EF.one()
    eq_prefix: list[EF] = [one]
    for i in range(n):
        eq_i = x[i] * y[i] + (one - x[i]) * (one - y[i])
        eq_prefix.append(eq_prefix[i] * eq_i)
    low_suffix: list[EF] = [one] * (n + 1)
    for i in range(n - 1, -1, -1):
        low_suffix[i] = low_suffix[i + 1] * x[i] * (one - y[i])
    s = EF.zero()
    for arr in range(n):
        carry = (one - x[arr]) * y[arr]
        s = s + eq_prefix[arr] * carry * low_suffix[arr + 1]
    prod = one
    for v in list(x) + list(y):
        prod = prod * v
    return s + prod


def eval_multilinear_evals(evals: Sequence[EF], point: Sequence[EF]) -> EF:
    """Evaluate a multilinear in *evaluation* form (length 2^n) at point ∈ EF^n.

    Big-endian indexing: index `i` corresponds to the bits `(b_0, ..., b_{n-1})`
    where `b_0` is the *most significant* bit, matching `poly::eval_multilinear`.
    Fold variables from the last to the first.
    """
    assert len(evals) == 1 << len(point)
    cur = list(evals)
    for r in reversed(point):
        nxt: list[EF] = []
        for j in range(0, len(cur), 2):
            nxt.append(cur[j] + (cur[j + 1] - cur[j]) * r)
        cur = nxt
    return cur[0]


def eval_multilinear_coeffs(coeffs: Sequence[EF], point: Sequence[EF]) -> EF:
    """poly::eval_multilinear_coeffs: split coeffs in half, recurse.

    `coeffs` represents `Σ_b c_b · x_0^{b_0} · ... · x_{n-1}^{b_{n-1}}`
    in the standard multilinear coefficient basis.
    """
    assert len(coeffs) == 1 << len(point)
    if not point:
        return coeffs[0]
    x = point[0]
    tail = point[1:]
    half = len(coeffs) // 2
    return eval_multilinear_coeffs(coeffs[:half], tail) + eval_multilinear_coeffs(coeffs[half:], tail) * x


@dataclass
class SparseValue:
    selector: int
    value: EF


@dataclass
class SparseStatement:
    """Mirror of whir::SparseStatement."""

    total_num_variables: int
    point: list[EF]  # the "inner" point, length = inner_num_variables
    values: list[SparseValue]
    is_next: bool = False

    @property
    def inner_num_variables(self) -> int:
        return len(self.point)

    @property
    def selector_num_variables(self) -> int:
        return self.total_num_variables - self.inner_num_variables

    @staticmethod
    def new_(total: int, point: list[EF], values: list[SparseValue]) -> "SparseStatement":
        assert total >= len(point)
        return SparseStatement(total, point, values, is_next=False)

    @staticmethod
    def dense(point: list[EF], value: EF) -> "SparseStatement":
        return SparseStatement(len(point), point, [SparseValue(0, value)], is_next=False)

    @staticmethod
    def unique_value(total: int, index: int, value: EF) -> "SparseStatement":
        return SparseStatement(total, [], [SparseValue(index, value)], is_next=False)

    @staticmethod
    def new_next(total: int, point: list[EF], values: list[SparseValue]) -> "SparseStatement":
        assert total >= len(point)
        return SparseStatement(total, point, values, is_next=True)


# ---------------------------------------------------------------------------
# WHIR config helpers: derive integer-only parameters from the trimmed JSON
# ---------------------------------------------------------------------------


def whir_n_rounds_and_final_sumcheck(num_variables: int) -> tuple[int, int]:
    """FoldingFactor::compute_number_of_rounds with default (7, 5, max_send=8)."""
    nv_except_first = num_variables - WHIR_INITIAL_FOLDING_FACTOR
    max_send = MAX_NUM_VARIABLES_TO_SEND_COEFFS
    if nv_except_first < max_send:
        return 0, nv_except_first
    n_rounds = -(-(nv_except_first - max_send) // WHIR_SUBSEQUENT_FOLDING_FACTOR)
    final_sumcheck_rounds = nv_except_first - n_rounds * WHIR_SUBSEQUENT_FOLDING_FACTOR
    return n_rounds, final_sumcheck_rounds


def whir_folding_factor_at_round(r: int) -> int:
    return WHIR_INITIAL_FOLDING_FACTOR if r == 0 else WHIR_SUBSEQUENT_FOLDING_FACTOR


def whir_rs_reduction_factor(r: int) -> int:
    return RS_DOMAIN_INITIAL_REDUCTION_FACTOR if r == 0 else 1


def whir_log_inv_rate_at(starting_log_inv_rate: int, round_index: int) -> int:
    rate = starting_log_inv_rate
    for r in range(round_index):
        rate += whir_folding_factor_at_round(r) - whir_rs_reduction_factor(r)
    return rate


def whir_num_variables_at_round(num_variables: int, round_index: int) -> int:
    """num_variables remaining at the START of round `round_index` (the verifier
    parses a new commitment at this num_variables for that round).
    """
    rem = num_variables
    for r in range(round_index + 1):
        rem -= whir_folding_factor_at_round(r)
    return rem


# KoalaBear two-adic generators: index `bits` is the primitive 2^bits-th root of unity.
# Mirrors KoalaBearParameters::TWO_ADIC_GENERATORS (canonical-form u32 values).
KB_TWO_ADIC_GENERATORS: list[int] = [
    0x1, 0x7F000000, 0x7E010002, 0x6832FE4A, 0x08DBD69C, 0x0A28F031, 0x5C4A5B99,
    0x29B75A80, 0x17668B8A, 0x27AD539B, 0x334D48C7, 0x7744959C, 0x768FC6FA,
    0x303964B2, 0x3E687D4D, 0x45A60E61, 0x6E2F4D7A, 0x163BD499, 0x6C4A8A45,
    0x143EF899, 0x514DDCAD, 0x484EF19B, 0x205D63C3, 0x68E7DD49, 0x6AC49F88,
]


def two_adic_generator(bits: int) -> Fp:
    """Mirror of KoalaBear::two_adic_generator(bits)."""
    assert 0 <= bits <= BASE_TWO_ADICITY
    return Fp(KB_TWO_ADIC_GENERATORS[bits])


def whir_domain_size_at(num_variables: int, starting_log_inv_rate: int, round_index: int) -> int:
    """domain_size that goes into `round_parameters[round_index]`.

    The Rust code seeds `domain_size = 1 << (num_variables + log_inv_rate)` and
    halves by `rs_reduction_factor(round)` BEFORE moving to the next round, so
    the value stored in round r is the *current* domain_size pre-reduction.
    """
    domain_log = num_variables + starting_log_inv_rate
    for r in range(round_index):
        domain_log -= whir_rs_reduction_factor(r)
    return 1 << domain_log


# ---------------------------------------------------------------------------
# WHIR config table — float-derived numbers only, dumped by the Rust test.
#
# Everything not in the JSON (n_rounds, per-round num_variables/log_inv_rate/
# domain_size/folding_factor/folded_domain_gen, final_sumcheck_rounds,
# final_log_inv_rate, ...) is integer arithmetic and should be derived on the
# Python side when it's actually needed.
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class WhirRoundConfig:
    num_queries: int
    ood_samples: int
    query_pow_bits: int
    folding_pow_bits: int


@dataclass(frozen=True)
class WhirConfig:
    log_inv_rate: int
    num_variables: int
    commitment_ood_samples: int
    starting_folding_pow_bits: int
    final_queries: int
    final_query_pow_bits: int
    rounds: tuple[WhirRoundConfig, ...]


def _load_whir_configs() -> dict[tuple[int, int], WhirConfig]:
    import json
    from pathlib import Path

    path = Path(__file__).with_name(WHIR_CONFIGS_PATH)
    with open(path) as f:
        raw = json.load(f)

    out: dict[tuple[int, int], WhirConfig] = {}
    for c in raw:
        cfg = WhirConfig(
            log_inv_rate=c["log_inv_rate"],
            num_variables=c["num_variables"],
            commitment_ood_samples=c["commitment_ood_samples"],
            starting_folding_pow_bits=c["starting_folding_pow_bits"],
            final_queries=c["final_queries"],
            final_query_pow_bits=c["final_query_pow_bits"],
            rounds=tuple(WhirRoundConfig(**r) for r in c["rounds"]),
        )
        out[(cfg.log_inv_rate, cfg.num_variables)] = cfg
    return out


_WHIR_CONFIGS: dict[tuple[int, int], WhirConfig] | None = None


def whir_config(log_inv_rate: int, num_variables: int) -> WhirConfig:
    global _WHIR_CONFIGS
    if _WHIR_CONFIGS is None:
        _WHIR_CONFIGS = _load_whir_configs()
    key = (log_inv_rate, num_variables)
    if key not in _WHIR_CONFIGS:
        raise KeyError(
            f"No WHIR config for log_inv_rate={log_inv_rate}, num_variables={num_variables}. "
            f"Regenerate with: cargo test -p lean_prover --test dump_whir_configs"
        )
    return _WHIR_CONFIGS[key]


# ---------------------------------------------------------------------------
# WHIR verifier (port of crates/whir/src/verify.rs)
# ---------------------------------------------------------------------------


@dataclass
class ParsedCommitment:
    """Mirror of whir::ParsedCommitment<F, EF>."""

    num_variables: int
    root: list[Fp]              # length DIGEST_ELEMS
    ood_points: list[EF]
    ood_answers: list[EF]

    def oods_constraints(self) -> list[SparseStatement]:
        """One dense SparseStatement per (point, eval) pair."""
        out: list[SparseStatement] = []
        for p, ev in zip(self.ood_points, self.ood_answers):
            point = expand_from_univariate(p, self.num_variables)
            out.append(SparseStatement.dense(point, ev))
        return out


def parsed_commitment_parse(state: VerifierState, num_variables: int, ood_samples: int) -> ParsedCommitment:
    """Port of ParsedCommitment::parse."""
    root = state.next_base_scalars_vec(DIGEST_ELEMS)
    ood_points: list[EF] = []
    ood_answers: list[EF] = []
    if ood_samples > 0:
        ood_points = state.sample_vec(ood_samples)
        ood_answers = state.next_extension_scalars_vec(ood_samples)
    return ParsedCommitment(
        num_variables=num_variables,
        root=root,
        ood_points=ood_points,
        ood_answers=ood_answers,
    )


def verify_sumcheck_rounds(
    state: VerifierState,
    claimed_sum_ref: list[EF],   # 1-element box, mutated in-place
    rounds: int,
    pow_bits: int,
) -> list[EF]:
    """Port of whir::verify::verify_sumcheck_rounds.

    Returns the folding randomness for these rounds. Mutates `claimed_sum_ref[0]`.
    """
    randomness: list[EF] = []
    for _ in range(rounds):
        coeffs = state.next_sumcheck_polynomial(3, claimed_sum_ref[0], None)
        state.check_pow_grinding(pow_bits)
        r = state.sample()
        # Evaluate cubic poly (length-3 coeffs in standard univariate basis).
        # DensePolynomial::evaluate uses Horner-style on coeffs[0..n].
        claimed_sum_ref[0] = _eval_univariate(coeffs, r)
        randomness.append(r)
    return randomness


def _eval_univariate(coeffs: list[EF], x: EF) -> EF:
    """Standard univariate evaluation: c[0] + c[1]*x + c[2]*x^2 + ..."""
    acc = EF.zero()
    for c in reversed(coeffs):
        acc = acc * x + c
    return acc


def combine_constraints(
    state: VerifierState,
    claimed_sum_ref: list[EF],
    constraints: list[SparseStatement],
) -> list[EF]:
    """Port of combine_constraints — mutates claimed_sum_ref[0] in-place."""
    gamma: EF = state.sample()
    combination = [EF.one()]
    for smt in constraints:
        for v in smt.values:
            pow_prev = combination[-1]
            claimed_sum_ref[0] = claimed_sum_ref[0] + pow_prev * v.value
            combination.append(pow_prev * gamma)
    combination.pop()
    return combination


def verify_stir_challenges(
    state: VerifierState,
    cfg: WhirConfig,
    round_index: int,
    num_variables: int,
    log_inv_rate: int,
    folding_factor: int,
    next_folding_factor: int,
    num_queries: int,
    query_pow_bits: int,
    commitment: ParsedCommitment,
    folding_randomness: list[EF],
) -> list[SparseStatement]:
    """Port of WhirConfig::verify_stir_challenges (incl. Merkle verification).

    `folding_factor` is the folding factor applied AT this round (i.e. how the
    leaves are arranged). `next_folding_factor` is the AIR sumcheck folding for
    the *next* hop; for the final pseudo-round it equals `folding_factor`.

    Returns STIR constraints (SparseStatements) for the next claim-combining.
    """
    # Domain size at this round (pre-RS-reduction for round `round_index`).
    domain_size = whir_domain_size_at(cfg.num_variables, cfg.log_inv_rate, round_index)
    folded_domain_size = domain_size >> folding_factor
    folded_domain_gen = two_adic_generator(domain_size.bit_length() - 1 - folding_factor)

    state.check_pow_grinding(query_pow_bits)
    indices = state.sample_in_range(folded_domain_size.bit_length() - 1, num_queries)

    leafs_base_field = round_index == 0
    log_height = folded_domain_size.bit_length() - 1
    answers_ef: list[list[EF]] = []
    for idx in indices:
        op = state.next_merkle_opening()
        if not merkle_verify_path(commitment.root, log_height, idx, op.leaf_data, op.path):
            raise ProofError("Merkle verification failed")
        # leaf_data is base; if leafs encode EF, pack 5 base → 1 EF.
        if leafs_base_field:
            answers_ef.append([EF.from_base(f) for f in op.leaf_data])
        else:
            ans: list[EF] = []
            for i in range(0, len(op.leaf_data), EF.DIMENSION):
                ans.append(EF(op.leaf_data[i : i + EF.DIMENSION]))
            answers_ef.append(ans)

    # Each answer is a length-(2^folding_factor) eval-form multilinear; fold at folding_randomness.
    folds: list[EF] = [eval_multilinear_evals(a, folding_randomness) for a in answers_ef]

    stir_constraints: list[SparseStatement] = []
    for idx, fold in zip(indices, folds):
        point = folded_domain_gen.value
        # point = folded_domain_gen ^ idx, as a base-field element wrapped into EF.
        gen_pow = pow(int(folded_domain_gen.value), idx, P)
        ef_pt = EF.from_base(Fp(gen_pow))
        expanded = expand_from_univariate(ef_pt, num_variables)
        stir_constraints.append(SparseStatement.dense(expanded, fold))
    return stir_constraints


def verify_constraint_coeffs(constraint: SparseStatement, coeffs: list[EF]) -> bool:
    """Port of verify_constraint_coeffs.

    Checks that the constraint's point is `[α, α^2, α^4, ...]` and that
    the univariate polynomial (Horner) evaluates to each claimed value.
    """
    assert constraint.selector_num_variables == 0
    alpha = constraint.point[0]
    for a, b in zip(constraint.point, constraint.point[1:]):
        if a * a != b:
            return False
    # Horner from highest-degree coefficient (last in `coeffs`) downward.
    univ_eval = EF.zero()
    for c in reversed(coeffs):
        univ_eval = univ_eval * alpha + c
    return all(univ_eval == v.value for v in constraint.values)


def eval_constraints_poly(
    constraints: list[tuple[list[EF], list[SparseStatement]]],
    point: list[EF],
) -> EF:
    """Port of WhirConfig::eval_constraints_poly.

    `constraints` is a list of (combination_randomness, sparse_statements) per
    round. `point` is the global folding randomness; it is sliced down by the
    folding factor of each preceding round before use.
    """
    value = EF.zero()
    pt = list(point)
    for round_idx, (randomness, smts) in enumerate(constraints):
        if round_idx > 0:
            k = whir_folding_factor_at_round(round_idx - 1)
            pt = pt[k:]
        i = 0
        for smt in smts:
            inner_pt = pt[len(pt) - smt.inner_num_variables :]
            if smt.is_next:
                common_weight = next_mle(smt.point, inner_pt)
            else:
                common_weight = eq_poly_outside(smt.point, inner_pt)
            for v in smt.values:
                # Per-selector lagrange weight on bits NOT covered by the inner point.
                lagrange = EF.one()
                for j in range(smt.selector_num_variables):
                    bit = (v.selector >> (smt.selector_num_variables - 1 - j)) & 1
                    lagrange = lagrange * (pt[j] if bit else (EF.one() - pt[j]))
                value = value + lagrange * common_weight * randomness[i]
                i += 1
        assert i == len(randomness)
    return value


def whir_verify(
    state: VerifierState,
    cfg: WhirConfig,
    parsed_commitment: ParsedCommitment,
    statement: list[SparseStatement],
) -> list[EF]:
    """Port of WhirConfig::verify. Returns the folding randomness."""
    for s in statement:
        assert s.total_num_variables == parsed_commitment.num_variables

    n_rounds, final_sumcheck_rounds = whir_n_rounds_and_final_sumcheck(cfg.num_variables)

    round_constraints: list[tuple[list[EF], list[SparseStatement]]] = []
    round_folding: list[list[EF]] = []
    claimed_sum_ref: list[EF] = [EF.zero()]
    prev_commitment = parsed_commitment

    # OODS + initial statement combine.
    state.duplex()
    initial_constraints = prev_commitment.oods_constraints() + statement
    combo = combine_constraints(state, claimed_sum_ref, initial_constraints)
    round_constraints.append((combo, initial_constraints))

    # Initial sumcheck.
    folding_rand = verify_sumcheck_rounds(
        state,
        claimed_sum_ref,
        whir_folding_factor_at_round(0),
        cfg.starting_folding_pow_bits,
    )
    round_folding.append(folding_rand)

    # Round loop.
    for r in range(n_rounds):
        rp = cfg.rounds[r]
        # New num_variables = num_variables_at_round(after this round's first absorb)
        # In Rust: round_state.num_variables = num_variables - folding_factor.total_number(r+1)
        nvars_round = cfg.num_variables - sum(
            whir_folding_factor_at_round(i) for i in range(r + 1)
        )
        new_commitment = parsed_commitment_parse(state, nvars_round, rp.ood_samples)

        stir_constraints = verify_stir_challenges(
            state,
            cfg,
            round_index=r,
            num_variables=nvars_round,
            log_inv_rate=whir_log_inv_rate_at(cfg.log_inv_rate, r),
            folding_factor=whir_folding_factor_at_round(r),
            next_folding_factor=whir_folding_factor_at_round(r + 1),
            num_queries=rp.num_queries,
            query_pow_bits=rp.query_pow_bits,
            commitment=prev_commitment,
            folding_randomness=round_folding[-1],
        )
        constraints_r = new_commitment.oods_constraints() + stir_constraints

        state.duplex()
        combo_r = combine_constraints(state, claimed_sum_ref, constraints_r)
        round_constraints.append((combo_r, constraints_r))

        folding_rand_r = verify_sumcheck_rounds(
            state,
            claimed_sum_ref,
            whir_folding_factor_at_round(r + 1),
            rp.folding_pow_bits,
        )
        round_folding.append(folding_rand_r)
        prev_commitment = new_commitment

    # Final round: read the final polynomial coefficients (length 2^n_vars_final).
    n_vars_final = cfg.num_variables - sum(
        whir_folding_factor_at_round(i) for i in range(n_rounds + 1)
    )
    final_coeffs = state.next_extension_scalars_vec(1 << n_vars_final)

    # Final STIR challenges (against the last commitment) — uses final_round_config.
    # In Rust: final.domain_size = round_params.last().domain_size >> rs_reduction_factor(n_rounds-1).
    # `whir_domain_size_at(num_variables, log_inv_rate, n_rounds)` already applies all the
    # reductions for rounds 0..n_rounds, so it equals final.domain_size directly.
    final_domain_size = whir_domain_size_at(cfg.num_variables, cfg.log_inv_rate, n_rounds)
    final_folding_factor = whir_folding_factor_at_round(n_rounds)
    final_num_variables = (
        cfg.num_variables - sum(whir_folding_factor_at_round(i) for i in range(n_rounds + 1))
    )
    folded_domain_size_final = final_domain_size >> final_folding_factor
    folded_gen_final = two_adic_generator(
        final_domain_size.bit_length() - 1 - final_folding_factor
    )

    state.check_pow_grinding(cfg.final_query_pow_bits)
    indices_final = state.sample_in_range(
        folded_domain_size_final.bit_length() - 1, cfg.final_queries
    )
    log_height_final = folded_domain_size_final.bit_length() - 1
    answers_ef: list[list[EF]] = []
    for idx in indices_final:
        op = state.next_merkle_opening()
        if not merkle_verify_path(
            prev_commitment.root, log_height_final, idx, op.leaf_data, op.path
        ):
            raise ProofError("Final Merkle verification failed")
        if n_rounds == 0:
            answers_ef.append([EF.from_base(f) for f in op.leaf_data])
        else:
            ans: list[EF] = []
            for i in range(0, len(op.leaf_data), EF.DIMENSION):
                ans.append(EF(op.leaf_data[i : i + EF.DIMENSION]))
            answers_ef.append(ans)
    folds_final = [eval_multilinear_evals(a, round_folding[-1]) for a in answers_ef]
    final_stir: list[SparseStatement] = []
    for idx, fold in zip(indices_final, folds_final):
        gen_pow = pow(int(folded_gen_final.value), idx, P)
        ef_pt = EF.from_base(Fp(gen_pow))
        expanded = expand_from_univariate(ef_pt, final_num_variables)
        final_stir.append(SparseStatement.dense(expanded, fold))

    # Verify STIR constraints directly on final polynomial coefficients.
    for c in final_stir:
        if not verify_constraint_coeffs(c, final_coeffs):
            raise ProofError("Final STIR constraint mismatch")

    # Final sumcheck.
    final_sumcheck_rand = verify_sumcheck_rounds(
        state, claimed_sum_ref, final_sumcheck_rounds, 0
    )
    round_folding.append(final_sumcheck_rand)

    # Flatten all folding randomness; evaluate the constraint weights polynomial.
    folding_randomness_flat = [r for chunk in round_folding for r in chunk]
    eval_weights = eval_constraints_poly(round_constraints, folding_randomness_flat)

    # Final coeffs are evaluated at REVERSED final_sumcheck_rand.
    reversed_point = list(reversed(final_sumcheck_rand))
    final_value = eval_multilinear_coeffs(final_coeffs, reversed_point)
    if claimed_sum_ref[0] != eval_weights * final_value:
        raise ProofError("WHIR final sumcheck check failed")

    return folding_randomness_flat


# ---------------------------------------------------------------------------
# Table metadata (mirror of lean_vm::tables::table_trait)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class BusData:
    """One field of a precompile bus message: either a column index or a
    constant. Mirrors `lean_vm::BusData`.
    """

    kind: str            # "Column" or "Constant"
    value: int

    @classmethod
    def from_json(cls, obj: dict) -> "BusData":
        return cls(kind=obj["kind"], value=int(obj["value"]))


@dataclass(frozen=True)
class Bus:
    """Per-table bus descriptor. `direction` is "Pull" or "Push"."""

    direction: str
    selector: int
    data: tuple[BusData, ...]

    @property
    def direction_flag(self) -> Fp:
        # Mirrors `BusDirection::to_field_flag`: Pull = -1, Push = +1.
        return Fp(P - 1) if self.direction == "Pull" else Fp(1)


@dataclass(frozen=True)
class Lookup:
    """A single memory lookup descriptor (`LookupIntoMemory` in Rust)."""

    index: int
    values: tuple[int, ...]


@dataclass(frozen=True)
class TableMeta:
    """Bundle of everything the verifier needs about one table."""

    name: str
    n_columns: int
    bus: Bus
    lookups: tuple[Lookup, ...]


def tables_from_json(obj: list[dict]) -> list[TableMeta]:
    out: list[TableMeta] = []
    for t in obj:
        bus_obj = t["bus"]
        bus = Bus(
            direction=bus_obj["direction"],
            selector=int(bus_obj["selector"]),
            data=tuple(BusData.from_json(d) for d in bus_obj["data"]),
        )
        lookups = tuple(
            Lookup(index=int(l["index"]), values=tuple(int(v) for v in l["values"]))
            for l in t["lookups"]
        )
        out.append(
            TableMeta(
                name=t["name"],
                n_columns=int(t["n_columns"]),
                bus=bus,
                lookups=lookups,
            )
        )
    return out


# ---------------------------------------------------------------------------
# Stacked PCS — port of sub_protocols/stacked_pcs.rs
# ---------------------------------------------------------------------------


def compute_stacked_n_vars(
    log_memory: int,
    log_bytecode: int,
    table_log_heights: dict[str, int],
    table_n_columns: dict[str, int],
) -> int:
    """Mirror of `stacked_pcs::compute_stacked_n_vars`.

    The stacked polynomial concatenates:
      - 2 copies of memory               -> 2 * 2^log_memory
      - one bytecode accumulator padded  -> 2^max(log_bytecode, max_table_log_n_rows)
      - per table: n_columns * 2^log_n_rows
    """
    max_table_log_n_rows = max(table_log_heights.values())
    total_len = (2 << log_memory) + (
        1 << max(log_bytecode, max_table_log_n_rows)
    )
    for name, log_n_rows in table_log_heights.items():
        total_len += table_n_columns[name] << log_n_rows
    return log2_ceil_usize(total_len)


def stacked_pcs_global_statements(
    stacked_n_vars: int,
    memory_n_vars: int,
    bytecode_n_vars: int,
    previous_statements: list[SparseStatement],
    table_log_heights: dict[str, int],
    committed_statements: dict[str, list[tuple[list[EF], dict[int, EF], dict[int, EF]]]],
    tables: dict[str, TableMeta],
    constants: dict,
) -> list[SparseStatement]:
    """Port of `stacked_pcs::stacked_pcs_global_statements`.

    Stacks the per-table column claims into the global statement list passed to
    `WhirConfig::verify`. Tables are processed in descending-height order.
    """
    assert len(table_log_heights) == len(committed_statements)
    tables_sorted = sort_tables_by_height(table_log_heights)

    out = list(previous_statements)
    offset = 2 << memory_n_vars  # memory + memory_acc
    max_table_n_vars = tables_sorted[0][1]
    offset += 1 << max(bytecode_n_vars, max_table_n_vars)  # bytecode acc

    col_pc = constants["col_pc"]
    starting_pc = constants["starting_pc"]
    ending_pc = constants["ending_pc"]

    for name, n_vars in tables_sorted:
        if name == "execution":
            out.append(
                SparseStatement.unique_value(
                    stacked_n_vars,
                    offset + (col_pc << n_vars),
                    EF.from_base(Fp(starting_pc)),
                )
            )
            out.append(
                SparseStatement.unique_value(
                    stacked_n_vars,
                    offset + ((col_pc + 1) << n_vars) - 1,
                    EF.from_base(Fp(ending_pc)),
                )
            )

        for (point, eq_values, next_values) in committed_statements[name]:
            # Rust uses BTreeMap → ascending-key iteration. Python dicts are
            # insertion-ordered, so we have to sort explicitly here.
            if next_values:
                out.append(
                    SparseStatement.new_next(
                        stacked_n_vars,
                        list(point),
                        [
                            SparseValue((offset >> n_vars) + col_index, value)
                            for col_index, value in sorted(next_values.items())
                        ],
                    )
                )
            out.append(
                SparseStatement(
                    total_num_variables=stacked_n_vars,
                    point=list(point),
                    values=[
                        SparseValue((offset >> n_vars) + col_index, value)
                        for col_index, value in sorted(eq_values.items())
                    ],
                    is_next=False,
                )
            )

        offset += tables[name].n_columns << n_vars

    return out


def stacked_pcs_parse_commitment(
    state: VerifierState,
    log_inv_rate: int,
    log_memory: int,
    log_bytecode: int,
    table_log_heights: dict[str, int],
    table_n_columns: dict[str, int],
    execution_table_name: str = "execution",
) -> ParsedCommitment:
    """Port of `stacked_pcs_parse_commitment`.

    - Memory must be at least as wide as the execution table.
    - The execution table must be the tallest table.
    - The stacked-poly size must fit within the WHIR domain bound.
    The actual commitment parsing is then delegated to `parsed_commitment_parse`.
    """
    exec_log = table_log_heights[execution_table_name]
    if log_memory < exec_log or exec_log < max(table_log_heights.values()):
        raise ProofError("InvalidProof: memory or execution table size invariants broken")

    stacked_n_vars = compute_stacked_n_vars(
        log_memory, log_bytecode, table_log_heights, table_n_columns
    )
    # `WhirConfig::new` asserts stacked_n_vars + log_inv_rate - first_round <= F::TWO_ADICITY.
    max_nv = BASE_TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - log_inv_rate
    if stacked_n_vars > max_nv:
        raise ProofError("InvalidProof: stacked_n_vars exceeds WHIR domain bound")

    cfg = whir_config(log_inv_rate, stacked_n_vars)
    return parsed_commitment_parse(state, stacked_n_vars, cfg.commitment_ood_samples)


# ---------------------------------------------------------------------------
# Generic sumcheck verifier (port of `backend/sumcheck/src/verify.rs`)
# ---------------------------------------------------------------------------


@dataclass
class Evaluation:
    """Pair (point, value): claim that a multilinear evaluates to `value` at
    `point`. Mirrors `poly::Evaluation`.
    """

    point: list[EF]
    value: EF


def sumcheck_verify(
    state: VerifierState,
    n_vars: int,
    degree: int,
    expected_sum: EF,
    eq_alphas: Sequence[EF] | None,
) -> Evaluation:
    """Mirror of `sumcheck::sumcheck_verify`.

    Reads `n_vars` round polynomials, each of `degree + 1` coefficients (so the
    bare polynomial is degree-`degree`; in the `eq_alphas` path the verifier
    extracts the bare poly and re-expands with `eq(α_round, X)`).
    Returns the final point + claimed value.
    """
    target = expected_sum
    challenges: list[EF] = []
    for round_idx in range(n_vars):
        eq_alpha = eq_alphas[round_idx] if eq_alphas is not None else None
        coeffs = state.next_sumcheck_polynomial(degree + 1, target, eq_alpha)
        r = state.sample()
        challenges.append(r)
        target = _eval_univariate(coeffs, r)
    return Evaluation(point=challenges, value=target)


# ---------------------------------------------------------------------------
# GKR-quotient verifier (port of `sub_protocols::quotient_gkr`)
#
# Verifies the protocol `Σ nᵢ/dᵢ` via a layered sumcheck.
# ---------------------------------------------------------------------------


N_VARS_TO_SEND_GKR_COEFFS = 5


def verify_gkr_quotient(
    state: VerifierState,
    n_vars: int,
) -> tuple[EF, list[EF], EF, EF]:
    """Mirror of `verify_gkr_quotient`. Returns
    `(quotient, gkr_point, claims_num, claims_den)`.
    """
    assert n_vars > N_VARS_TO_SEND_GKR_COEFFS
    send_len = 1 << N_VARS_TO_SEND_GKR_COEFFS

    last_nums = state.next_extension_scalars_vec(send_len)
    last_dens = state.next_extension_scalars_vec(send_len)
    quotient = _quotient_sum(last_nums, last_dens)

    point: list[EF] = state.sample_vec(N_VARS_TO_SEND_GKR_COEFFS)
    claims_num = eval_multilinear_evals(last_nums, point)
    claims_den = eval_multilinear_evals(last_dens, point)

    for i in range(N_VARS_TO_SEND_GKR_COEFFS, n_vars):
        point, claims_num, claims_den = _verify_gkr_quotient_step(
            state, i, point, claims_num, claims_den
        )
    return quotient, point, claims_num, claims_den


def _verify_gkr_quotient_step(
    state: VerifierState,
    n_vars: int,
    point: list[EF],
    claims_num: EF,
    claims_den: EF,
) -> tuple[list[EF], EF, EF]:
    alpha = state.sample()
    expected_sum = claims_num + alpha * claims_den
    eq_alphas_rev = list(reversed(point))
    postponed = sumcheck_verify(state, n_vars, 3, expected_sum, eq_alphas_rev)
    # Rust: postponed.point.0.reverse();
    postponed_point = list(reversed(postponed.point))
    inner_evals = state.next_extension_scalars_vec(4)

    # constraints_eval = α · n_r · d_r + (n_l · d_r + n_r · d_l)
    constraints_eval = (
        alpha * inner_evals[2] * inner_evals[3]
        + (inner_evals[0] * inner_evals[3] + inner_evals[1] * inner_evals[2])
    )

    if postponed.value != eq_poly_outside(point, postponed_point) * constraints_eval:
        raise ProofError("GKR step: postponed value mismatch")

    beta = state.sample()
    one_minus_beta = EF.one() - beta
    next_num = one_minus_beta * inner_evals[0] + beta * inner_evals[1]
    next_den = one_minus_beta * inner_evals[2] + beta * inner_evals[3]
    next_point = postponed_point + [beta]
    return next_point, next_num, next_den


def _quotient_sum(nums: Sequence[EF], dens: Sequence[EF]) -> EF:
    acc = EF.zero()
    for n, d in zip(nums, dens):
        acc = acc + n * d.inv()
    return acc


# ---------------------------------------------------------------------------
# Logup helpers (utils + poly)
# ---------------------------------------------------------------------------


def to_big_endian_in_field(value: int, bit_count: int) -> list[EF]:
    """Mirror of `poly::to_big_endian_in_field`.

    Returns the `bit_count` bits of `value` MSB-first, each as `EF::ZERO`/`EF::ONE`.
    """
    return [EF.one() if (value >> (bit_count - 1 - i)) & 1 else EF.zero() for i in range(bit_count)]


def from_end(seq: Sequence, n: int) -> list:
    """`utils::from_end` — the last `n` elements."""
    if n == 0:
        return []
    return list(seq[len(seq) - n :])


def mle_of_01234567_etc(point: Sequence[EF]) -> EF:
    """Mirror of `utils::mle_of_01234567_etc`.

    Evaluates the multilinear polynomial whose evaluations on `{0,1}^n` are
    `f(i) = i` (with `i` interpreted big-endian), at `point`.
    """
    if not point:
        return EF.zero()
    e = mle_of_01234567_etc(point[1:])
    bit = EF(_from_int(1 << (len(point) - 1)).c)
    return (EF.one() - point[0]) * e + point[0] * (e + bit)


def mle_of_zeros_then_ones(n_zeros: int, point: Sequence[EF]) -> EF:
    """Mirror of `poly::mle_of_zeros_then_ones`.

    Evaluates the multilinear of `[0, ..., 0, 1, ..., 1]` (`n_zeros` zeros, then
    `2^len(point) - n_zeros` ones) at `point`.
    """
    n_values = 1 << len(point)
    assert n_zeros <= n_values
    if n_zeros == 0:
        return EF.one()
    if n_zeros == n_values:
        return EF.zero()
    half = n_values >> 1
    if n_zeros < half:
        return (EF.one() - point[0]) * mle_of_zeros_then_ones(n_zeros, point[1:]) + point[0]
    return point[0] * mle_of_zeros_then_ones(n_zeros - half, point[1:])


def finger_print(table: Fp, data: Sequence[EF], alphas_eq_poly: Sequence[EF]) -> EF:
    """Mirror of `utils::finger_print`.

    Computes `Σᵢ alphas_eq_poly[i] · data[i] + alphas_eq_poly[-1] · table`.
    """
    assert len(alphas_eq_poly) > len(data)
    acc = EF.zero()
    for a, d in zip(alphas_eq_poly, data):
        acc = acc + a * d
    acc = acc + alphas_eq_poly[-1] * EF.from_base(table)
    return acc


def _from_int(x: int) -> EF:
    return EF.from_base(Fp(x % P))


def sort_tables_by_height(
    table_log_heights: dict[str, int],
) -> list[tuple[str, int]]:
    """Mirror of `lean_vm::sort_tables_by_height` — descending by `log_n_rows`,
    `BTreeMap` ordering (= alphabetical) breaks ties.
    """
    items = sorted(table_log_heights.items())  # alphabetical
    items.sort(key=lambda kv: -kv[1])
    return items


def eval_eq(point: Sequence[EF]) -> list[EF]:
    """Evaluation table of `eq(point, ·)`: the length-`2^n` vector with
    `eq[i] = Πⱼ (point[j] if bitⱼ(i) else 1 - point[j])` for big-endian `i`.
    """
    out = [EF.one()]
    for p in point:
        nxt: list[EF] = []
        for v in out:
            nxt.append(v * (EF.one() - p))
            nxt.append(v * p)
        out = nxt
    return out


# ---------------------------------------------------------------------------
# Generic logup verifier — port of sub_protocols/logup.rs::verify_generic_logup
# ---------------------------------------------------------------------------


@dataclass
class GenericLogupStatements:
    """Mirror of `GenericLogupStatements` returned by `verify_generic_logup`."""

    memory_and_acc_point: list[EF]
    value_memory: EF
    value_memory_acc: EF
    bytecode_and_acc_point: list[EF]
    value_bytecode_acc: EF
    bus_numerators_values: dict[str, EF]
    bus_denominators_values: dict[str, EF]
    gkr_point: list[EF]
    columns_values: dict[str, dict[int, EF]]
    total_gkr_n_vars: int
    bytecode_evaluation: Evaluation


def _compute_total_active_len_logup(
    log_memory: int,
    log_bytecode: int,
    tables_sorted: list[tuple[str, int]],
    table_lookups: dict[str, list[Lookup]],
    execution_name: str,
) -> int:
    """Mirror of `logup::compute_total_active_len`."""
    max_table_height = 1 << tables_sorted[0][1]
    log_n_cycles = next(h for n, h in tables_sorted if n == execution_name)

    def offset_for_table(name: str, log_n_rows: int) -> int:
        num_cols = sum(len(l.values) for l in table_lookups[name]) + 1  # +1 for the bus
        return num_cols << log_n_rows

    return (
        (1 << log_memory)
        + max(1 << log_bytecode, max_table_height)
        + (1 << log_n_cycles)
        + sum(offset_for_table(name, h) for name, h in tables_sorted)
    )


def verify_generic_logup(
    state: VerifierState,
    c: EF,
    alphas: list[EF],
    alphas_eq_poly: list[EF],
    log_memory: int,
    bytecode_multilinear: list[Fp],
    table_log_heights: dict[str, int],
    tables: dict[str, TableMeta],
    constants: dict,
    execution_name: str = "execution",
) -> GenericLogupStatements:
    """Port of `verify_generic_logup`.

    `bytecode_multilinear` is the flat coefficient vector of length
    `2^(log_bytecode + ceil(log2(N_INSTRUCTION_COLUMNS)))` — what the Rust
    verifier holds as `&bytecode.instructions_multilinear`.

    `alphas` and `alphas_eq_poly` come from sampling `c` and `log2_ceil(max_bus_width)`
    extension-field elements (per the leanVM `verify_execution`).
    """

    n_instr_cols = constants["n_instruction_columns"]
    n_runtime_cols = constants["n_runtime_columns"]
    col_pc = constants["col_pc"]
    dom_mem = constants["logup_memory_domainsep"]
    dom_byte = constants["logup_bytecode_domainsep"]

    tables_sorted = sort_tables_by_height(table_log_heights)
    log_bytecode = log2_strict_usize(
        len(bytecode_multilinear) // _next_pow_two(n_instr_cols)
    )

    table_lookups = {name: list(tables[name].lookups) for name in table_log_heights}
    total_active_len = _compute_total_active_len_logup(
        log_memory, log_bytecode, tables_sorted, table_lookups, execution_name
    )
    total_gkr_n_vars = log2_ceil_usize(total_active_len)

    quotient, point_gkr, numerators_value, denominators_value = verify_gkr_quotient(
        state, total_gkr_n_vars
    )

    if quotient != EF.zero():
        raise ProofError("logup: GKR sum != 0")

    retrieved_num = EF.zero()
    retrieved_den = EF.zero()

    def pref_at(offset: int, log_height: int) -> EF:
        n_missing = total_gkr_n_vars - log_height
        bits = to_big_endian_in_field(offset >> log_height, n_missing)
        return eq_poly_outside(bits, point_gkr[:n_missing])

    # ---- Memory section --------------------------------------------------
    memory_and_acc_point = from_end(point_gkr, log_memory)
    pref = pref_at(0, log_memory)

    value_memory_acc = state.next_extension_scalar()
    retrieved_num = retrieved_num - pref * value_memory_acc

    value_memory = state.next_extension_scalar()
    value_index = mle_of_01234567_etc(memory_and_acc_point)
    retrieved_den = retrieved_den + pref * (
        c - finger_print(Fp(dom_mem), [value_memory, value_index], alphas_eq_poly)
    )
    offset = 1 << log_memory

    # ---- Bytecode section ------------------------------------------------
    log_bytecode_padded = max(log_bytecode, tables_sorted[0][1])
    bytecode_and_acc_point = from_end(point_gkr, log_bytecode)
    pref = pref_at(offset, log_bytecode)
    pref_padded = pref_at(offset, log_bytecode_padded)

    value_bytecode_acc = state.next_extension_scalar()
    retrieved_num = retrieved_num - pref * value_bytecode_acc

    bytecode_index_value = mle_of_01234567_etc(bytecode_and_acc_point)
    log_instr = log2_ceil_usize(n_instr_cols)
    bytecode_point = list(bytecode_and_acc_point) + list(from_end(alphas, log_instr))
    bytecode_value = eval_multilinear_evals(
        [EF.from_base(x) for x in bytecode_multilinear], bytecode_point
    )
    # Correction: `(1 - alpha[0]) * (1 - alpha[1]) * ... * (1 - alpha[k-1])`
    # over the alphas BEFORE the last `log_instr` (= the bus-data slot bits).
    correction = EF.one()
    for a in alphas[: len(alphas) - log_instr]:
        correction = correction * (EF.one() - a)
    bytecode_value_corrected = bytecode_value * correction
    retrieved_den = retrieved_den + pref * (
        c
        - (
            bytecode_value_corrected
            + bytecode_index_value * alphas_eq_poly[n_instr_cols]
            + alphas_eq_poly[-1] * EF.from_base(Fp(dom_byte))
        )
    )

    # Padding for bytecode (bytecode_acc shorter than max_table_height).
    retrieved_den = retrieved_den + pref_padded * mle_of_zeros_then_ones(
        1 << log_bytecode, from_end(point_gkr, log_bytecode_padded)
    )
    offset += 1 << log_bytecode_padded

    # ---- Per-table sections ----------------------------------------------
    bus_num_vals: dict[str, EF] = {}
    bus_den_vals: dict[str, EF] = {}
    columns_values: dict[str, dict[int, EF]] = {}

    for name, log_n_rows in tables_sorted:
        meta = tables[name]
        table_values: dict[int, EF] = {}

        if name == execution_name:
            # 0] Bytecode lookup for the execution table.
            eval_on_pc = state.next_extension_scalar()
            table_values[col_pc] = eval_on_pc

            instr_evals = state.next_extension_scalars_vec(n_instr_cols)
            for i, e in enumerate(instr_evals):
                table_values[n_runtime_cols + i] = e

            pref = pref_at(offset, log_n_rows)
            retrieved_num = retrieved_num + pref  # numerator is 1
            retrieved_den = retrieved_den + pref * (
                c
                - finger_print(
                    Fp(dom_byte),
                    list(instr_evals) + [eval_on_pc],
                    alphas_eq_poly,
                )
            )
            offset += 1 << log_n_rows

        # I] Bus (data flow between tables)
        eval_on_selector = state.next_extension_scalar()
        pref = pref_at(offset, log_n_rows)
        retrieved_num = retrieved_num + pref * eval_on_selector

        eval_on_data = state.next_extension_scalar()
        retrieved_den = retrieved_den + pref * eval_on_data

        bus_num_vals[name] = eval_on_selector
        bus_den_vals[name] = eval_on_data
        offset += 1 << log_n_rows

        # II] Lookups into memory
        for lookup in meta.lookups:
            index_eval = state.next_extension_scalar()
            assert lookup.index not in table_values
            table_values[lookup.index] = index_eval

            for i, col_index in enumerate(lookup.values):
                value_eval = state.next_extension_scalar()
                assert col_index not in table_values
                table_values[col_index] = value_eval

                pref = pref_at(offset, log_n_rows)
                retrieved_num = retrieved_num + pref
                retrieved_den = retrieved_den + pref * (
                    c
                    - finger_print(
                        Fp(dom_mem),
                        [value_eval, index_eval + EF.from_base(Fp(i))],
                        alphas_eq_poly,
                    )
                )
                offset += 1 << log_n_rows

        columns_values[name] = table_values

    # Padding tail (xxx..xxx111...1 region beyond `offset`).
    retrieved_den = retrieved_den + mle_of_zeros_then_ones(offset, point_gkr)

    if retrieved_num != numerators_value:
        raise ProofError("logup: numerators value mismatch")
    if retrieved_den != denominators_value:
        raise ProofError("logup: denominators value mismatch")

    return GenericLogupStatements(
        memory_and_acc_point=list(memory_and_acc_point),
        value_memory=value_memory,
        value_memory_acc=value_memory_acc,
        bytecode_and_acc_point=list(bytecode_and_acc_point),
        value_bytecode_acc=value_bytecode_acc,
        bus_numerators_values=bus_num_vals,
        bus_denominators_values=bus_den_vals,
        gkr_point=list(point_gkr),
        columns_values=columns_values,
        total_gkr_n_vars=total_gkr_n_vars,
        bytecode_evaluation=Evaluation(point=bytecode_point, value=bytecode_value),
    )


def _next_pow_two(x: int) -> int:
    if x <= 1:
        return 1
    return 1 << (x - 1).bit_length()


# ---------------------------------------------------------------------------
# AIR sumcheck helpers (port of sub_protocols/air_sumcheck.rs)
# ---------------------------------------------------------------------------


def natural_ordering_point_for_session(
    sumcheck_air_point: Sequence[EF], log_n_rows: int
) -> list[EF]:
    """Mirror of `air_sumcheck::natural_ordering_point_for_session`.

    Takes the last `log_n_rows` coordinates of the AIR sumcheck point and
    reverses them.
    """
    if log_n_rows == 0:
        return []
    return list(reversed(sumcheck_air_point[-log_n_rows:]))


def back_loaded_table_contribution(
    bus_point: Sequence[EF],
    sumcheck_air_point: Sequence[EF],
    natural_ordering_point: Sequence[EF],
    constraint_eval: EF,
    eta_power: EF,
) -> EF:
    """Mirror of `verify_execution::back_loaded_table_contribution`.

        eta^t · (Π i∈[0, n_max - n_t) sumcheck_point[i]) · eq(bus_point, natural_point) · constraint_eval
    """
    n_t = len(bus_point)
    n_max = len(sumcheck_air_point)
    suffix_start = n_max - n_t
    assert len(natural_ordering_point) == n_t
    eq_val = eq_poly_outside(bus_point, natural_ordering_point)
    k_t = EF.one()
    for x in sumcheck_air_point[:suffix_start]:
        k_t = k_t * x
    return eta_power * k_t * eq_val * constraint_eval


def columns_evals_up_and_down(
    n_columns: int,
    down_column_indexes: Sequence[int],
    col_evals: Sequence[EF],
    natural_ordering_point: Sequence[EF],
) -> tuple[list[EF], dict[int, EF], dict[int, EF]]:
    """Mirror of `air_sumcheck::columns_evals_up_and_down`.

    Splits `col_evals` into the per-column evaluation map plus the "next"
    (= `down`) columns. Returns `(point, eq_values, next_values)`.
    """
    n_up = n_columns
    assert len(col_evals) == n_up + len(down_column_indexes)
    eq_values = {i: col_evals[i] for i in range(n_up)}
    next_values = {
        idx: col_evals[n_up + j] for j, idx in enumerate(down_column_indexes)
    }
    return list(natural_ordering_point), eq_values, next_values


# ---------------------------------------------------------------------------
# Pluggable per-table AIR constraint evaluator
# ---------------------------------------------------------------------------


class ConstraintFolder:
    """Mirror of `air::constraint_folder::ConstraintFolder` over EF.

    Each `assert_zero(x)` (or `assert_zero_ef`) contributes
    `alpha_powers[constraint_index] · x` to the accumulator.
    """

    def __init__(self, up: Sequence[EF], down: Sequence[EF], alpha_powers: Sequence[EF]) -> None:
        self.up = list(up)
        self.down = list(down)
        self.alpha_powers = list(alpha_powers)
        self.accumulator: EF = EF.zero()
        self.constraint_index = 0

    def assert_zero(self, x: EF) -> None:
        a = self.alpha_powers[self.constraint_index]
        self.accumulator = self.accumulator + a * x
        self.constraint_index += 1

    # `assert_zero_ef` is identical in EF.
    assert_zero_ef = assert_zero

    def assert_eq(self, x: EF, y: EF) -> None:
        self.assert_zero(x - y)

    def assert_bool(self, x: EF) -> None:
        # bool_check(x) = x * (1 - x). Zero iff x is 0 or 1.
        self.assert_zero(x * (EF.one() - x))


# Registry of per-table AIR constraint evaluators. Each function takes
# `(folder, table_meta, extra_data)` and emits constraints via the folder.
_AIR_EVALUATORS: dict[str, "callable"] = {}


def register_air_evaluator(name: str):
    def decorator(fn):
        _AIR_EVALUATORS[name] = fn
        return fn
    return decorator


def _eval_virtual_bus_column(extra_data: dict, flag: EF, data: Sequence[EF]) -> EF:
    """Port of `tables::utils::eval_virtual_bus_column`.

    `(Σ alphas[i] · data[i] + alphas[-1] · LOGUP_PRECOMPILE_DOMAINSEP) · bus_beta + flag`.
    """
    alphas: list[EF] = extra_data["logup_alphas_eq_poly"]
    bus_beta: EF = extra_data["bus_beta"]
    assert len(data) < len(alphas)
    inner = EF.zero()
    for a, d in zip(alphas, data):
        inner = inner + a * d
    inner = inner + alphas[-1] * EF.from_base(Fp(1))  # LOGUP_PRECOMPILE_DOMAINSEP = 1
    return inner * bus_beta + flag


def air_constraint_eval(
    table: TableMeta,
    col_evals: Sequence[EF],
    alpha_powers: Sequence[EF],
    extra_data: dict,
) -> EF:
    """Evaluate the table's AIR constraint polynomial at `col_evals`.

    `col_evals[:n_columns]` is the `up` row, `col_evals[n_columns:]` is the
    `down` row (only for tables with `down_column_indexes`).
    `extra_data` carries `logup_alphas_eq_poly`, `bus_beta`, `c` (logup_c) —
    used by the precompile bus constraints.
    """
    n_up = table.n_columns
    folder = ConstraintFolder(col_evals[:n_up], col_evals[n_up:], alpha_powers)
    impl = _AIR_EVALUATORS.get(table.name)
    if impl is None:
        raise NotImplementedError(f"AIR evaluator not yet ported for table {table.name!r}")
    impl(folder, table, extra_data)
    return folder.accumulator


# ---------------------------------------------------------------------------
# Execution-table AIR (lean_vm/src/tables/execution/air.rs)
# ---------------------------------------------------------------------------


# Column indexes for the execution table (mirrors execution/air.rs).
_EXEC = {
    "PC": 0, "FP": 1,
    "MEM_ADDRESS_A": 2, "MEM_ADDRESS_B": 3, "MEM_ADDRESS_C": 4,
    "MEM_VALUE_A": 5, "MEM_VALUE_B": 6, "MEM_VALUE_C": 7,
    "OPERAND_A": 8, "OPERAND_B": 9, "OPERAND_C": 10,
    "FLAG_A": 11, "FLAG_B": 12, "FLAG_C": 13, "FLAG_C_FP": 14,
    "FLAG_AB_FP": 15, "MUL": 16, "JUMP": 17, "AUX": 18, "PRECOMPILE_DATA": 19,
}


@register_air_evaluator("execution")
def _eval_air_execution(folder: ConstraintFolder, table: TableMeta, extra_data: dict) -> None:
    up = folder.up
    down = folder.down
    one = EF.one()

    next_pc = down[0]
    next_fp = down[1]

    operand_a = up[_EXEC["OPERAND_A"]]
    operand_b = up[_EXEC["OPERAND_B"]]
    operand_c = up[_EXEC["OPERAND_C"]]
    flag_a = up[_EXEC["FLAG_A"]]
    flag_b = up[_EXEC["FLAG_B"]]
    flag_c = up[_EXEC["FLAG_C"]]
    flag_c_fp = up[_EXEC["FLAG_C_FP"]]
    flag_ab_fp = up[_EXEC["FLAG_AB_FP"]]
    mul = up[_EXEC["MUL"]]
    jump = up[_EXEC["JUMP"]]
    aux = up[_EXEC["AUX"]]
    precompile_data = up[_EXEC["PRECOMPILE_DATA"]]

    value_a = up[_EXEC["MEM_VALUE_A"]]
    value_b = up[_EXEC["MEM_VALUE_B"]]
    value_c = up[_EXEC["MEM_VALUE_C"]]
    pc = up[_EXEC["PC"]]
    fp = up[_EXEC["FP"]]
    addr_a = up[_EXEC["MEM_ADDRESS_A"]]
    addr_b = up[_EXEC["MEM_ADDRESS_B"]]
    addr_c = up[_EXEC["MEM_ADDRESS_C"]]

    one_minus_flag_a_and_flag_ab_fp = -(flag_a + flag_ab_fp - one)
    one_minus_flag_b_and_flag_ab_fp = -(flag_b + flag_ab_fp - one)
    one_minus_flag_c_and_flag_c_fp = -(flag_c + flag_c_fp - one)

    nu_a = (
        flag_a * operand_a
        + one_minus_flag_a_and_flag_ab_fp * value_a
        + flag_ab_fp * (fp + operand_a)
    )
    nu_b = (
        flag_b * operand_b
        + one_minus_flag_b_and_flag_ab_fp * value_b
        + flag_ab_fp * (fp + operand_b)
    )
    nu_c = (
        flag_c * operand_c
        + one_minus_flag_c_and_flag_c_fp * value_c
        + flag_c_fp * (fp + operand_c)
    )

    fp_plus_op_a = fp + operand_a
    fp_plus_op_b = fp + operand_b
    fp_plus_op_c = fp + operand_c
    pc_plus_one = pc + one
    nu_a_minus_one = nu_a - one

    add = aux * EF.from_base(Fp(2)) - aux * aux
    deref = _ef_halve(aux * (aux - one))
    is_precompile = -(add + mul + deref + jump - one)

    # Constraint 1: bus column (assert_zero_ef)
    folder.assert_zero_ef(
        _eval_virtual_bus_column(
            extra_data, is_precompile, [precompile_data, nu_a, nu_b, nu_c]
        )
    )

    # Constraints 2-4: address consistency
    folder.assert_zero(one_minus_flag_a_and_flag_ab_fp * (addr_a - fp_plus_op_a))
    folder.assert_zero(one_minus_flag_b_and_flag_ab_fp * (addr_b - fp_plus_op_b))
    folder.assert_zero(one_minus_flag_c_and_flag_c_fp * (addr_c - fp_plus_op_c))

    # Constraints 5-6: add/mul
    folder.assert_zero(add * (nu_b - (nu_a + nu_c)))
    folder.assert_zero(mul * (nu_b - nu_a * nu_c))

    # Constraints 7-8: deref
    folder.assert_zero(deref * (addr_b - (value_a + operand_b)))
    folder.assert_zero(deref * (value_b - nu_c))

    # Constraints 9-13: jump
    jump_and_condition = jump * nu_a
    folder.assert_zero(jump_and_condition * nu_a_minus_one)
    folder.assert_zero(jump_and_condition * (next_pc - nu_b))
    folder.assert_zero(jump_and_condition * (next_fp - nu_c))
    not_jump_and_condition = -(jump_and_condition - one)
    folder.assert_zero(not_jump_and_condition * (next_pc - pc_plus_one))
    folder.assert_zero(not_jump_and_condition * (next_fp - fp))


# ---------------------------------------------------------------------------
# Extension-op-table AIR (lean_vm/src/tables/extension_op/air.rs)
# ---------------------------------------------------------------------------


_EXT_OP_COL = {
    "IS_BE": 0, "START": 1, "FLAG_ADD": 2, "FLAG_MUL": 3, "FLAG_POLY_EQ": 4,
    "LEN": 5, "IDX_A": 6, "IDX_B": 7, "IDX_RES": 8,
    "VA": 9, "VB": 14, "VRES": 19, "COMP": 24,
}

_EXT_OP_FLAG_IS_BE = 4
_EXT_OP_FLAG_ADD = 8
_EXT_OP_FLAG_MUL = 16
_EXT_OP_FLAG_POLY_EQ = 32
_EXT_OP_LEN_MULTIPLIER = 64


def _quintic_mul_ef(a: Sequence[EF], b: Sequence[EF]) -> list[EF]:
    """Quintic-extension multiplication on 5-element EF arrays.

    Direct port of `quintic_mul` from koalabear/quintic_extension/extension.rs
    using EF-level arithmetic — the dot-product becomes `Σ a[i]·b'[i]`.
    """
    assert len(a) == 5 and len(b) == 5
    b0m3 = b[0] - b[3]
    b1m4 = b[1] - b[4]
    b4m2 = b[4] - b[2]

    def dot(av: Sequence[EF], bv: Sequence[EF]) -> EF:
        acc = EF.zero()
        for x, y in zip(av, bv):
            acc = acc + x * y
        return acc

    return [
        dot(a, [b[0], b[4], b[3], b[2], b1m4]),
        dot(a, [b[1], b[0], b[4], b[3], b[2]]),
        dot(a, [b[2], b1m4, b0m3, b4m2, b[3] - b1m4]),
        dot(a, [b[3], b[2], b1m4, b0m3, b4m2]),
        dot(a, [b[4], b[3], b[2], b1m4, b0m3]),
    ]


@register_air_evaluator("extension_op")
def _eval_air_extension_op(folder: ConstraintFolder, table: TableMeta, extra_data: dict) -> None:
    up = folder.up
    down = folder.down
    one = EF.one()

    is_be = up[_EXT_OP_COL["IS_BE"]]
    start = up[_EXT_OP_COL["START"]]
    flag_add = up[_EXT_OP_COL["FLAG_ADD"]]
    flag_mul = up[_EXT_OP_COL["FLAG_MUL"]]
    flag_poly_eq = up[_EXT_OP_COL["FLAG_POLY_EQ"]]
    len_col = up[_EXT_OP_COL["LEN"]]
    idx_a = up[_EXT_OP_COL["IDX_A"]]
    idx_b = up[_EXT_OP_COL["IDX_B"]]
    idx_res = up[_EXT_OP_COL["IDX_RES"]]

    va = [up[_EXT_OP_COL["VA"] + k] for k in range(5)]
    vb = [up[_EXT_OP_COL["VB"] + k] for k in range(5)]
    vres = [up[_EXT_OP_COL["VRES"] + k] for k in range(5)]
    comp = [up[_EXT_OP_COL["COMP"] + k] for k in range(5)]

    start_down = down[0]
    is_be_down = down[1]
    len_down = down[2]
    flag_add_down = down[3]
    flag_mul_down = down[4]
    flag_poly_eq_down = down[5]
    idx_a_down = down[6]
    idx_b_down = down[7]
    comp_down = [down[8 + k] for k in range(5)]

    active = flag_add + flag_mul + flag_poly_eq
    activation_flag = start * active

    aux = (
        is_be * EF.from_base(Fp(_EXT_OP_FLAG_IS_BE))
        + flag_add * EF.from_base(Fp(_EXT_OP_FLAG_ADD))
        + flag_mul * EF.from_base(Fp(_EXT_OP_FLAG_MUL))
        + flag_poly_eq * EF.from_base(Fp(_EXT_OP_FLAG_POLY_EQ))
        + len_col * EF.from_base(Fp(_EXT_OP_LEN_MULTIPLIER))
    )

    # Constraint 1: bus
    folder.assert_zero_ef(
        _eval_virtual_bus_column(extra_data, activation_flag, [aux, idx_a, idx_b, idx_res])
    )

    is_ee = -(is_be - one)
    not_start_down = -(start_down - one)

    va_f_or_ef = [va[0]] + [va[k] * is_ee for k in range(1, 5)]
    comp_tail = [comp_down[k] * not_start_down for k in range(5)]

    # Constraints 2-6: bool flags
    folder.assert_bool(is_be)
    folder.assert_bool(start)
    folder.assert_bool(flag_add)
    folder.assert_bool(flag_mul)
    folder.assert_bool(flag_poly_eq)

    # Constraints 7-11: add
    for k in range(5):
        folder.assert_zero((comp[k] - (va_f_or_ef[k] + vb[k] + comp_tail[k])) * flag_add)

    va_times_vb = _quintic_mul_ef(va_f_or_ef, vb)

    # Constraints 12-16: mul
    for k in range(5):
        folder.assert_zero((comp[k] - (va_times_vb[k] + comp_tail[k])) * flag_mul)

    # Constraints 17-21: poly_eq
    poly_eq_val = []
    for k in range(5):
        base = va_times_vb[k] + va_times_vb[k] - va_f_or_ef[k] - vb[k]
        poly_eq_val.append(base + one if k == 0 else base)
    comp_down_or_one = []
    for k in range(5):
        if k == 0:
            comp_down_or_one.append(comp_down[0] * not_start_down + start_down)
        else:
            comp_down_or_one.append(comp_down[k] * not_start_down)
    poly_eq_result = _quintic_mul_ef(poly_eq_val, comp_down_or_one)
    for k in range(5):
        folder.assert_zero((comp[k] - poly_eq_result[k]) * flag_poly_eq)

    # Constraints 22-26: result matches comp when start
    for k in range(5):
        folder.assert_zero((comp[k] - vres[k]) * start)

    # Constraints 27-31: down-row consistency on non-start rows
    folder.assert_zero(not_start_down * (len_col - len_down - one))
    folder.assert_zero(not_start_down * (is_be - is_be_down))
    folder.assert_zero(not_start_down * (flag_add - flag_add_down))
    folder.assert_zero(not_start_down * (flag_mul - flag_mul_down))
    folder.assert_zero(not_start_down * (flag_poly_eq - flag_poly_eq_down))

    # Constraint 32-33: idx_a / idx_b increment
    a_increment = is_be + is_ee * EF.from_base(Fp(5))  # DIMENSION = 5
    folder.assert_zero(not_start_down * (idx_a_down - idx_a - a_increment))
    folder.assert_zero(not_start_down * (idx_b_down - idx_b - EF.from_base(Fp(5))))

    # Constraint 34: start_down enforces len=1
    folder.assert_zero(start_down * (len_col - one))


# ---------------------------------------------------------------------------
# Poseidon16-compress AIR (lean_vm/src/tables/poseidon_16/mod.rs)
# ---------------------------------------------------------------------------


def _ef_cube(x: EF) -> EF:
    return x * x * x


def _load_poseidon1_constants() -> dict:
    import json
    from pathlib import Path

    raw = json.loads(
        (Path(__file__).with_name("poseidon1_constants.json")).read_text()
    )

    def to_fp_mat(m: list[list[int]]) -> list[list[Fp]]:
        return [[Fp(v) for v in row] for row in m]

    return {
        "half_full_rounds": raw["half_full_rounds"],
        "partial_rounds": raw["partial_rounds"],
        "initial_constants": to_fp_mat(raw["initial_constants"]),
        "final_constants": to_fp_mat(raw["final_constants"]),
        "sparse_m_i": to_fp_mat(raw["sparse_m_i"]),
        "sparse_first_row": to_fp_mat(raw["sparse_first_row"]),
        "sparse_v": to_fp_mat(raw["sparse_v"]),
        "sparse_first_rc": [Fp(v) for v in raw["sparse_first_round_constants"]],
        "sparse_scalar_rc": [Fp(v) for v in raw["sparse_scalar_round_constants"]],
        "mds_dense": to_fp_mat(raw["mds_dense"]),
    }


_POSEIDON1_CONSTS: dict | None = None


def _p1c() -> dict:
    global _POSEIDON1_CONSTS
    if _POSEIDON1_CONSTS is None:
        _POSEIDON1_CONSTS = _load_poseidon1_constants()
    return _POSEIDON1_CONSTS


_POSEIDON_WIDTH = 16
_HALF_DIGEST_LEN = 4
_POSEIDON_HALF_OUTPUT_SHIFT = 1 << 1            # = 2
_POSEIDON_HARDCODED_LEFT_4_FLAG_SHIFT = 1 << 2  # = 4
_POSEIDON_HARDCODED_LEFT_4_OFFSET_SHIFT = 1 << 3  # = 8


def _mds_dense_apply(state: list[EF]) -> list[EF]:
    """state := mds_dense × state (dense MDS matrix multiplication)."""
    mds = _p1c()["mds_dense"]
    out: list[EF] = []
    for i in range(_POSEIDON_WIDTH):
        acc = EF.zero()
        for j in range(_POSEIDON_WIDTH):
            acc = acc + state[j] * mds[i][j]
        out.append(acc)
    return out


def _add_kb_vec(state: list[EF], rc: list[Fp]) -> list[EF]:
    return [s + EF.from_base(r) for s, r in zip(state, rc)]


def _cube_vec(state: list[EF]) -> list[EF]:
    return [_ef_cube(s) for s in state]


def _eval_2_full_rounds(
    folder: ConstraintFolder,
    state: list[EF],
    post_full_round: Sequence[EF],
    rc1: list[Fp],
    rc2: list[Fp],
) -> list[EF]:
    """Mirror of `eval_2_full_rounds_16` (16 constraints emitted)."""
    state = _cube_vec(_add_kb_vec(state, rc1))
    state = _mds_dense_apply(state)
    state = _cube_vec(_add_kb_vec(state, rc2))
    state = _mds_dense_apply(state)
    for i in range(_POSEIDON_WIDTH):
        folder.assert_eq(state[i], post_full_round[i])
        state[i] = post_full_round[i]
    return state


def _eval_last_2_full_rounds(
    folder: ConstraintFolder,
    initial_state: Sequence[EF],
    state: list[EF],
    outputs: Sequence[EF],
    rc1: list[Fp],
    rc2: list[Fp],
    flag_half_output: EF,
) -> None:
    """Mirror of `eval_last_2_full_rounds_16` (4 + 4 = 8 constraints)."""
    state = _cube_vec(_add_kb_vec(state, rc1))
    state = _mds_dense_apply(state)
    state = _cube_vec(_add_kb_vec(state, rc2))
    state = _mds_dense_apply(state)
    # Davies-Meyer: state += initial_state.
    state = [s + init for s, init in zip(state, initial_state)]
    one_minus_half = EF.one() - flag_half_output
    for idx in range(_POSEIDON_WIDTH // 2):
        if idx < _HALF_DIGEST_LEN:
            folder.assert_eq(state[idx], outputs[idx])
        else:
            folder.assert_zero(one_minus_half * (state[idx] - outputs[idx]))


def _eval_poseidon1_16(folder: ConstraintFolder, cols: dict, extra_data: dict) -> None:
    """Mirror of `eval_poseidon1_16`. Emits 80 (non-bus) constraints."""
    const = _p1c()
    state = list(cols["inputs"])
    initial_state = list(cols["inputs"])  # used for compression at the end

    # --- initial full rounds (HALF_INITIAL_FULL_ROUNDS = 2) ---
    half_initial = const["half_full_rounds"] // 2
    initial_consts = const["initial_constants"]
    for r in range(half_initial):
        state = _eval_2_full_rounds(
            folder, state, cols["beginning_full_rounds"][r],
            initial_consts[2 * r], initial_consts[2 * r + 1],
        )

    # --- transition into partial rounds (no constraints emitted here) ---
    # Rust uses the sparse `m_i` matrix, NOT the dense MDS.
    state = _add_kb_vec(state, const["sparse_first_rc"])
    state = _matvec_kb(const["sparse_m_i"], state)

    first_rows = const["sparse_first_row"]
    v_vecs = const["sparse_v"]
    scalar_rc = const["sparse_scalar_rc"]
    n_partial = const["partial_rounds"]
    for r in range(n_partial):
        # S-box on state[0]; the cubed value is committed in `partial_rounds[r]`.
        cubed = _ef_cube(state[0])
        folder.assert_eq(cubed, cols["partial_rounds"][r])  # assert_eq_low ≡ assert_eq
        state[0] = cols["partial_rounds"][r]
        if r < n_partial - 1:
            state[0] = state[0] + scalar_rc[r]
        # Sparse mat: new_s0 = first_row[r] · state; state[i] += old_s0 * v[r][i-1].
        old_s0 = state[0]
        new_s0 = EF.zero()
        for j in range(_POSEIDON_WIDTH):
            new_s0 = new_s0 + state[j] * first_rows[r][j]
        state[0] = new_s0
        for i in range(1, _POSEIDON_WIDTH):
            state[i] = state[i] + old_s0 * v_vecs[r][i - 1]

    # --- ending full rounds (HALF_FINAL_FULL_ROUNDS - 1 = 1) ---
    half_final = const["half_full_rounds"] // 2
    final_consts = const["final_constants"]
    for r in range(half_final - 1):
        state = _eval_2_full_rounds(
            folder, state, cols["ending_full_rounds"][r],
            final_consts[2 * r], final_consts[2 * r + 1],
        )

    # --- last 2 full rounds (8 constraints) ---
    last_idx = 2 * (half_final - 1)
    _eval_last_2_full_rounds(
        folder, initial_state, state, cols["outputs"],
        final_consts[last_idx], final_consts[last_idx + 1],
        cols["flag_half_output"],
    )


def _matvec_kb(mat: list[list[Fp]], state: list[EF]) -> list[EF]:
    """16x16 base-field matrix · EF-vector."""
    out = []
    for i in range(_POSEIDON_WIDTH):
        acc = EF.zero()
        for j in range(_POSEIDON_WIDTH):
            acc = acc + state[j] * mat[i][j]
        out.append(acc)
    return out


@register_air_evaluator("poseidon16_compress")
def _eval_air_poseidon16(folder: ConstraintFolder, table: TableMeta, extra_data: dict) -> None:
    up = folder.up
    one = EF.one()
    const = _p1c()

    # Decode the Poseidon1Cols16 layout.
    o = 0
    flag_active = up[o]; o += 1
    index_b = up[o]; o += 1
    index_res = up[o]; o += 1
    flag_half_output = up[o]; o += 1
    flag_hardcoded_left = up[o]; o += 1
    offset_hardcoded_left = up[o]; o += 1
    effective_index_left_first = up[o]; o += 1
    effective_index_left_second = up[o]; o += 1
    inputs = up[o : o + _POSEIDON_WIDTH]; o += _POSEIDON_WIDTH
    half_initial = const["half_full_rounds"] // 2
    beginning_full_rounds = []
    for _ in range(half_initial):
        beginning_full_rounds.append(up[o : o + _POSEIDON_WIDTH])
        o += _POSEIDON_WIDTH
    partial_cols = up[o : o + const["partial_rounds"]]; o += const["partial_rounds"]
    half_final = const["half_full_rounds"] // 2
    ending_full_rounds = []
    for _ in range(half_final - 1):
        ending_full_rounds.append(up[o : o + _POSEIDON_WIDTH])
        o += _POSEIDON_WIDTH
    outputs = up[o : o + _POSEIDON_WIDTH // 2]; o += _POSEIDON_WIDTH // 2

    precompile_data_reconstructed = (
        one
        + flag_half_output * EF.from_base(Fp(_POSEIDON_HALF_OUTPUT_SHIFT))
        + flag_hardcoded_left * EF.from_base(Fp(_POSEIDON_HARDCODED_LEFT_4_FLAG_SHIFT))
        + flag_hardcoded_left
        * offset_hardcoded_left
        * EF.from_base(Fp(_POSEIDON_HARDCODED_LEFT_4_OFFSET_SHIFT))
    )

    one_minus_flag_hardcoded_left = one - flag_hardcoded_left
    index_a = effective_index_left_second - one_minus_flag_hardcoded_left * EF.from_base(
        Fp(_HALF_DIGEST_LEN)
    )

    # Constraint 1: bus
    folder.assert_zero_ef(
        _eval_virtual_bus_column(
            extra_data, flag_active, [precompile_data_reconstructed, index_a, index_b, index_res]
        )
    )

    # Constraints 2-4: bool flags
    folder.assert_bool(flag_active)
    folder.assert_bool(flag_half_output)
    folder.assert_bool(flag_hardcoded_left)

    # Constraints 5-6: hardcoded-left consistency
    folder.assert_zero(
        flag_hardcoded_left * (offset_hardcoded_left - effective_index_left_first)
    )
    folder.assert_zero(
        one_minus_flag_hardcoded_left * (index_a - effective_index_left_first)
    )

    _eval_poseidon1_16(
        folder,
        {
            "inputs": list(inputs),
            "beginning_full_rounds": [list(r) for r in beginning_full_rounds],
            "partial_rounds": list(partial_cols),
            "ending_full_rounds": [list(r) for r in ending_full_rounds],
            "outputs": list(outputs),
            "flag_half_output": flag_half_output,
        },
        extra_data,
    )


# ---------------------------------------------------------------------------
# AIR-stage orchestration in verify_execution
# ---------------------------------------------------------------------------


@dataclass
class AirStageResult:
    """Outputs of the AIR sumcheck stage, fed into the WHIR finale."""

    sumcheck_air_point: list[EF]
    bus_beta: EF
    air_alpha: EF
    eta: EF
    committed_statements: dict[str, list[tuple[list[EF], dict[int, EF], dict[int, EF]]]]
    public_memory_random_point: list[EF]
    public_memory_eval: EF


def _max_air_constraints(tables: dict[str, TableMeta]) -> int:
    # Hardcoded mirrors of `<Table as Air>::n_constraints` for each table.
    NC = {"execution": 13, "extension_op": 16, "poseidon16_compress": 81}
    return max(NC[t] for t in tables)


def _table_degree_air(table_name: str) -> int:
    # Hardcoded mirrors of `<Table as Air>::degree_air`.
    return {"execution": 5, "extension_op": 4, "poseidon16_compress": 10}[table_name]


def _table_down_column_indexes(table_name: str) -> list[int]:
    """Hardcoded mirrors of `<Table as Air>::down_column_indexes`."""
    if table_name == "execution":
        # COL_PC=0, COL_FP=1
        return [0, 1]
    if table_name == "extension_op":
        # COL_START, COL_IS_BE, COL_LEN, COL_FLAG_ADD, COL_FLAG_MUL,
        # COL_FLAG_POLY_EQ, COL_IDX_A, COL_IDX_B, COL_COMP+0..5
        return [1, 0, 5, 2, 3, 4, 6, 7, 24, 25, 26, 27, 28]
    if table_name == "poseidon16_compress":
        return []
    raise KeyError(table_name)


def _table_n_down_columns(table_name: str) -> int:
    return len(_table_down_column_indexes(table_name))


def verify_air_stage(
    state: VerifierState,
    logup: GenericLogupStatements,
    logup_c: EF,
    logup_alphas_eq_poly: list[EF],
    table_log_heights: dict[str, int],
    tables: dict[str, TableMeta],
    public_input: Sequence[Fp],
    log_memory: int,
) -> AirStageResult:
    """Port of the AIR-sumcheck block in `verify_execution.rs` (lines 100–179).

    Returns the per-table committed statements (point + eq_values + next_values)
    and the public-memory random point + its evaluation.
    """
    bus_beta = state.sample()
    air_alpha = state.sample()

    max_air_constraints = _max_air_constraints(tables)
    alpha_powers: list[EF] = []
    cur = EF.one()
    for _ in range(max_air_constraints + 1):
        alpha_powers.append(cur)
        cur = cur * air_alpha

    eta = state.sample()

    tables_sorted = sort_tables_by_height(table_log_heights)

    # Build initial_sum.
    initial_sum = EF.zero()
    eta_powers: list[EF] = []
    cur = EF.one()
    for name, _ in tables_sorted:
        bus_num = logup.bus_numerators_values[name]
        bus_den = logup.bus_denominators_values[name]
        flag = (
            EF.zero() - EF.one()
            if tables[name].bus.direction == "Pull"
            else EF.one()
        )
        bus_final_value = bus_num * flag + bus_beta * (bus_den - logup_c)
        initial_sum = initial_sum + cur * bus_final_value
        eta_powers.append(cur)
        cur = cur * eta

    max_full_degree = max(_table_degree_air(name) + 1 for name, _ in tables_sorted)
    n_max = tables_sorted[0][1]

    sumcheck_result = sumcheck_verify(state, n_max, max_full_degree, initial_sum, None)
    sumcheck_air_point = sumcheck_result.point
    claimed_air_final_value = sumcheck_result.value

    # Per-table loop: read col_evals, evaluate AIR, accumulate, build claims.
    my_air_final_value = EF.zero()

    # Seed committed_statements with the logup entry per table, mirroring the
    # init loop in `verify_execution.rs` (lines 88-98).
    committed: dict[str, list[tuple[list[EF], dict[int, EF], dict[int, EF]]]] = {}
    for name in tables:
        log_n = table_log_heights[name]
        logup_point = from_end(logup.gkr_point, log_n)
        committed[name] = [
            (list(logup_point), dict(logup.columns_values[name]), {}),
        ]
    extra_data = {
        "logup_alphas_eq_poly": logup_alphas_eq_poly,
        "bus_beta": bus_beta,
        "c": logup_c,
    }
    for (name, log_n_rows), eta_pow in zip(tables_sorted, eta_powers):
        meta = tables[name]
        n_down = _table_n_down_columns(name)
        n_cols_total = meta.n_columns + n_down
        col_evals = state.next_extension_scalars_vec(n_cols_total)

        alpha_powers_table = alpha_powers  # same list — folder reads constraint_index
        constraint_eval = air_constraint_eval(meta, col_evals, alpha_powers_table, extra_data)

        bus_point = from_end(logup.gkr_point, log_n_rows)
        natural_pt = natural_ordering_point_for_session(sumcheck_air_point, log_n_rows)
        my_air_final_value = my_air_final_value + back_loaded_table_contribution(
            bus_point, sumcheck_air_point, natural_pt, constraint_eval, eta_pow
        )

        point, eq_values, next_values = columns_evals_up_and_down(
            meta.n_columns,
            _table_down_column_indexes(name),
            col_evals,
            natural_pt,
        )
        committed[name].append((point, eq_values, next_values))

    if my_air_final_value != claimed_air_final_value:
        raise ProofError("AIR sumcheck: my_air_final_value != claimed_air_final_value")

    # Public memory evaluation (length is next power of two of public_input).
    public_memory = padd_with_zero_to_next_power_of_two(public_input)
    log_pm = log2_strict_usize(len(public_memory))
    public_memory_random_point = state.sample_vec(log_pm)
    public_memory_eval = eval_multilinear_evals(
        [EF.from_base(f) for f in public_memory], public_memory_random_point
    )

    return AirStageResult(
        sumcheck_air_point=list(sumcheck_air_point),
        bus_beta=bus_beta,
        air_alpha=air_alpha,
        eta=eta,
        committed_statements=committed,
        public_memory_random_point=list(public_memory_random_point),
        public_memory_eval=public_memory_eval,
    )


# ---------------------------------------------------------------------------
# Top-level verifier
# ---------------------------------------------------------------------------


@dataclass
class ProofVerificationDetails:
    bytecode_evaluation: object  # Evaluation<EF> — TODO


@dataclass(frozen=True)
class TableInfo:
    """Minimal table metadata the verifier needs (bus + lookups + n_columns).

    Built from the Rust-dumped table metadata via `tables_from_json`.
    """

    name: str
    n_columns: int
    bus: Bus
    lookups: tuple[Lookup, ...]

    def to_meta(self) -> TableMeta:
        return TableMeta(self.name, self.n_columns, self.bus, self.lookups)


@dataclass
class VerifyExecutionPartial:
    """What we can produce so far — extended as we port more sub-protocols."""

    log_inv_rate: int
    log_memory: int
    public_input_len: int
    table_log_heights: dict[str, int]
    stacked_n_vars: int
    parsed_commitment: ParsedCommitment
    logup_statements: GenericLogupStatements
    air_stage: AirStageResult | None = None


def verify_execution(
    bytecode: Bytecode,
    public_input: Sequence[Fp],
    proof: Proof,
    tables: Sequence[TableInfo],
    constants: dict,
    bytecode_multilinear: list[Fp],
) -> VerifyExecutionPartial:
    """Port of `verify_execution` (lean_prover/src/verify_execution.rs).

    Runs the prologue, parses the stacked-PCS WHIR commitment, samples the
    logup challenges, and verifies the generic logup argument.  AIR sumcheck +
    WHIR final-eval are still TODO.

    `tables` must be in canonical Rust order (`ALL_TABLES`) — `execution`
    first, then `extension_op`, `poseidon16` — because the verifier reads
    per-table `log_n_rows` in that same order from the transcript.

    `constants` and `bytecode_multilinear` come from the Rust dump.
    """

    state = VerifierState(proof)
    state.observe_scalars(list(public_input))
    state.observe_scalars(poseidon16_compress_pair(bytecode.hash, SNARK_DOMAIN_SEP))

    n_tables = len(tables)
    dims = [int(x.value) for x in state.next_base_scalars_vec(3 + n_tables)]
    log_inv_rate, log_memory, public_input_len = dims[0], dims[1], dims[2]
    table_log_n_rows = dims[3 : 3 + n_tables]

    if public_input_len != len(public_input):
        raise ProofError("InvalidProof: public_input length mismatch")

    if not (MIN_WHIR_LOG_INV_RATE <= log_inv_rate <= MAX_WHIR_LOG_INV_RATE):
        raise ProofError("InvalidRate")

    for log_n_rows in table_log_n_rows:
        if log_n_rows < MIN_LOG_N_ROWS_PER_TABLE:
            raise ProofError("InvalidProof: table too small")

    max_table_log = max(table_log_n_rows) if table_log_n_rows else 0
    if log_memory < max(max_table_log, bytecode.log_size):
        raise ProofError("InvalidProof: memory smaller than tables/bytecode")

    if not (MIN_LOG_MEMORY_SIZE <= log_memory <= MAX_LOG_MEMORY_SIZE):
        raise ProofError("InvalidProof: log_memory out of range")

    if bytecode.log_size < MIN_BYTECODE_LOG_SIZE:
        raise ProofError("InvalidProof: bytecode too small")

    table_log_heights = {t.name: log_n_rows for t, log_n_rows in zip(tables, table_log_n_rows)}
    table_n_columns = {t.name: t.n_columns for t in tables}
    tables_by_name = {t.name: t.to_meta() for t in tables}

    parsed_commitment = stacked_pcs_parse_commitment(
        state,
        log_inv_rate=log_inv_rate,
        log_memory=log_memory,
        log_bytecode=bytecode.log_size,
        table_log_heights=table_log_heights,
        table_n_columns=table_n_columns,
    )

    # Logup challenges.
    logup_c = state.sample()
    max_bus_width = 1 + max(
        constants["max_precompile_bus_width"], constants["n_instruction_columns"]
    )
    logup_alphas = state.sample_vec(log2_ceil_usize(max_bus_width))
    logup_alphas_eq_poly = eval_eq(logup_alphas)

    logup_statements = verify_generic_logup(
        state,
        logup_c,
        logup_alphas,
        logup_alphas_eq_poly,
        log_memory,
        bytecode_multilinear,
        table_log_heights,
        tables_by_name,
        constants,
    )

    air_stage = verify_air_stage(
        state,
        logup_statements,
        logup_c,
        logup_alphas_eq_poly,
        table_log_heights,
        tables_by_name,
        public_input,
        log_memory,
    )

    # Build the global WHIR statement list and run the final WHIR verify.
    stacked_n_vars = parsed_commitment.num_variables
    previous_statements = [
        SparseStatement(
            total_num_variables=stacked_n_vars,
            point=list(logup_statements.memory_and_acc_point),
            values=[
                SparseValue(0, logup_statements.value_memory),
                SparseValue(1, logup_statements.value_memory_acc),
            ],
            is_next=False,
        ),
        SparseStatement(
            total_num_variables=stacked_n_vars,
            point=list(air_stage.public_memory_random_point),
            values=[SparseValue(0, air_stage.public_memory_eval)],
            is_next=False,
        ),
        SparseStatement(
            total_num_variables=stacked_n_vars,
            point=list(logup_statements.bytecode_and_acc_point),
            values=[
                SparseValue(
                    (2 << log_memory) >> bytecode.log_size,
                    logup_statements.value_bytecode_acc,
                ),
            ],
            is_next=False,
        ),
    ]

    global_statements = stacked_pcs_global_statements(
        stacked_n_vars,
        log_memory,
        bytecode.log_size,
        previous_statements,
        table_log_heights,
        air_stage.committed_statements,
        tables_by_name,
        constants,
    )

    whir_cfg = whir_config(log_inv_rate, stacked_n_vars)
    whir_verify(state, whir_cfg, parsed_commitment, global_statements)

    return VerifyExecutionPartial(
        log_inv_rate=log_inv_rate,
        log_memory=log_memory,
        public_input_len=public_input_len,
        table_log_heights=table_log_heights,
        stacked_n_vars=parsed_commitment.num_variables,
        parsed_commitment=parsed_commitment,
        logup_statements=logup_statements,
        air_stage=air_stage,
    )


# ---------------------------------------------------------------------------
# Self-test: foundations only
# ---------------------------------------------------------------------------


def _smoke() -> None:
    print(f"KoalaBear P = {P}")

    # EF sanity: (X) * (X^4 + X) should reduce since X^5 = 1 - X^2.
    X = EF([Fp(0), Fp(1), Fp(0), Fp(0), Fp(0)])
    X4 = X.pow(4)
    X5 = X * X4
    expected = EF.one() - EF([Fp(0), Fp(0), Fp(1), Fp(0), Fp(0)])  # 1 - X^2
    assert X5 == expected, (X5, expected)
    one = EF.one()
    a = EF([Fp(3), Fp(1), Fp(4), Fp(1), Fp(5)])
    assert a * a.inv() == one
    print("EF arithmetic OK")

    # Challenger / sponge sanity: deterministic outputs.
    ch1 = Challenger()
    ch1.observe_many([Fp(1), Fp(2), Fp(3)])
    s1 = ch1.sample_ef()
    ch2 = Challenger()
    ch2.observe_many([Fp(1), Fp(2), Fp(3)])
    s2 = ch2.sample_ef()
    assert s1 == s2, "Challenger not deterministic"
    print(f"Challenger sample (deterministic) = {s1}")

    # WHIR config table: sample lookup.
    cfg = whir_config(log_inv_rate=1, num_variables=20)
    print(
        f"WHIR cfg(log_inv_rate=1, num_vars=20): rounds={len(cfg.rounds)}, "
        f"final_queries={cfg.final_queries}, final_query_pow_bits={cfg.final_query_pow_bits}"
    )
    if cfg.rounds:
        r0 = cfg.rounds[0]
        print(
            f"  round[0]: num_queries={r0.num_queries}, ood_samples={r0.ood_samples}, "
            f"query_pow_bits={r0.query_pow_bits}, folding_pow_bits={r0.folding_pow_bits}"
        )

    # VerifierState read/sample round-trip.
    proof = Proof(transcript=[Fp(i) for i in range(20)])
    st = VerifierState(proof)
    st.observe_scalars([Fp(7)])
    base = st.next_base_scalars_vec(3)
    print(f"VerifierState read 3 base scalars: {base}")
    chal = st.sample()
    print(f"VerifierState sample = {chal}")

    # verify_execution: dummy proof should hit a bound check, not crash.
    bc = Bytecode(hash=[Fp(0)] * 8, log_size=10)
    bad_proof = Proof(transcript=[Fp(0)] * 64)
    try:
        verify_execution(
            bc,
            [Fp(0)] * 4,
            bad_proof,
            tables=[],
            constants={
                "n_instruction_columns": 12,
                "n_runtime_columns": 8,
                "col_pc": 0,
                "logup_memory_domainsep": 0,
                "logup_precompile_domainsep": 1,
                "logup_bytecode_domainsep": 2,
                "max_precompile_bus_width": 4,
            },
            bytecode_multilinear=[Fp(0)] * 16,
        )
    except ProofError as e:
        print(f"verify_execution failed bound check (expected with dummy proof): {e}")


if __name__ == "__main__":
    _smoke()
