#!/usr/bin/env bash
#
# all.sh — one-shot CI gate for leanx.
#
# Runs every trust-preserving check in the order they should
# surface failures:
#
#   1. axiom-audit.sh — zero sorry in trusted trees, every axiom
#      in the allowlist.  If this fails the kernel has regressed
#      on trust invariants and downstream work is unsafe.
#   2. lake build — compiles every FX module.  Default target
#      covers the library + the fxi executable.
#   3. lake build Tests — compiles the test umbrella.  Catches
#      stale test references that the `Tests.Main` executable
#      root doesn't transitively cover.
#   4. lake exe fxi-tests — runs every runtime test suite.
#   5. fxi-smoke.sh — end-to-end CLI smoke test; catches CLI
#      wiring regressions the Lean tests miss (flag parsing,
#      stdout vs stderr routing, exit-code structure).
#   6. conformance.sh — runs `fxi test tests/conformance/` over
#      the corpus of Phase-2 `.fx` files.  Catches surface-
#      feature regressions (primitive types, pattern matching,
#      effect rows) the Lean tests cover at the AST layer but
#      don't re-exercise through the lex+parse+elab+check
#      pipeline.
#
# Exits at the first failure with the sub-command's exit code.
# Intended for pre-commit and CI usage.  Run manually:
#
#   cd /path/to/leanx && bash scripts/all.sh
#
# The script deliberately does NOT invoke `lake update`, `lake
# clean`, or any destructive command — it only observes.

set -e
set -o pipefail

HERE="$(cd "$(dirname "$0")/.." && pwd)"
cd "$HERE"

# Make elan's lake visible in CI or restricted shells.
if [ -d "$HOME/.elan/bin" ]; then
    export PATH="$HOME/.elan/bin:$PATH"
fi

echo "=== [1/6] axiom-audit ==="
bash scripts/axiom-audit.sh

echo
echo "=== [2/6] lake build ==="
lake build

echo
echo "=== [3/6] lake build Tests ==="
lake build Tests

echo
echo "=== [4/6] lake exe fxi-tests ==="
lake exe fxi-tests

echo
echo "=== [5/6] fxi-smoke ==="
bash scripts/fxi-smoke.sh

echo
echo "=== [6/6] conformance ==="
bash scripts/conformance.sh

echo
echo "all.sh: OK — every gate passed."
