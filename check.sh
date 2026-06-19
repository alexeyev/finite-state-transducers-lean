#!/bin/sh
# Build and type-check the whole library, then report.
# Requires `elan` on PATH (the pinned toolchain is fetched automatically).
set -e
cd "$(dirname "$0")"
lake build
echo "=== build succeeded: all proofs check, axiom audit printed above ==="
