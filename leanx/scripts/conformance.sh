#!/usr/bin/env bash
# Conformance-suite driver (G5).
#
# Runs `fxi test tests/conformance/` after a fresh build and
# enforces the expected invariant: every file in the conformance
# directory type-checks cleanly.  Any regression breaks the
# build gate here, preventing surface-feature breakage from
# sneaking in via green Lean tests that don't exercise the
# end-to-end pipeline.
#
# Usage: bash scripts/conformance.sh
# Exit: 0 on green suite; non-zero on any failure.
#
# Complements:
#   * scripts/axiom-audit.sh — zero-sorry, axiom-allowlist gate
#   * scripts/fxi-smoke.sh   — cross-subcommand smoke test
#   * scripts/all.sh         — meta-CI that runs all three

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
project_root="$(cd "${script_dir}/.." && pwd)"
cd "${project_root}"

fxi_binary=".lake/build/bin/fxi"
conformance_dir="tests/conformance"

if [[ ! -x "${fxi_binary}" ]]; then
  echo "conformance: '${fxi_binary}' not found — run \`lake build\` first." >&2
  exit 1
fi

if [[ ! -d "${conformance_dir}" ]]; then
  echo "conformance: directory '${conformance_dir}' missing." >&2
  exit 1
fi

echo "conformance: running ${fxi_binary} test ${conformance_dir}"

if "${fxi_binary}" test "${conformance_dir}"; then
  echo
  echo "conformance: OK"
  exit 0
else
  exit_code="$?"
  echo
  echo "conformance: FAIL — at least one file broke (exit ${exit_code})"
  echo "conformance: edit tests/conformance/*.fx to address the regressions,"
  echo "conformance: or rebase if the compiler surface changed intentionally."
  exit "${exit_code}"
fi
