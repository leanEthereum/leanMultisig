#!/bin/bash
set -e

echo "=== Checking default (native) ==="
cargo check
echo ""

echo "=== Checking no SIMD (-neon) ==="
RUSTFLAGS="-C target-feature=-neon" cargo check
echo ""

echo "=== Checking x86_64 AVX2 ==="
RUSTFLAGS="-C target-feature=+avx2" cargo check --target x86_64-apple-darwin
echo ""

echo "=== Checking x86_64 AVX512 ==="
RUSTFLAGS="-C target-feature=+avx512f" cargo check --target x86_64-apple-darwin
echo ""

echo "All checks passed!"
