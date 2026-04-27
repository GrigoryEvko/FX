#!/usr/bin/env bash
#
# axiom-audit.sh — enforce the trust invariants for leanx.
#
# Invariants checked (see leanx/AXIOMS.md and fx_design.md Appendix H):
#   1. Zero `sorry` in FX/Kernel/** and FX/Metatheory/**
#      (outside of comments — block comments `/- ... -/` and line
#      comments `-- ...` are stripped before scanning).
#   2. Every `axiom` declaration in FX/Kernel/** matches a row in
#      AXIOMS.md (the allowlist).
#   3. No `axiom` declarations anywhere outside FX/Kernel/**.
#
# Summary output includes:
#   * Total Lean lines scanned, split by tree (Kernel, Metatheory,
#     Syntax, other, Tests).
#   * Axiom count split by tree (Kernel vs. elsewhere, should be 0
#     elsewhere).
#   * Sorry count split by tree.
#
# Exit code:
#   0 — all invariants hold.
#   1 — at least one invariant is violated.
#
# Flags:
#   --json     emit the summary block as JSON (for CI).  Lexical
#              errors (unmatched sorry, unknown axiom) still print
#              to stderr as plain text because CI grep patterns
#              depend on it.
#   --quiet    suppress the progress lines; only the final PASS/FAIL
#              verdict is printed.  Errors still go to stderr.
#   --help     show this header and exit 0.

set -eu  # deliberately NOT pipefail — we tolerate empty grep results

cd "$(dirname "$0")/.."

# --- Flag parsing -----------------------------------------------------

JSON=0
QUIET=0

for arg in "$@"; do
  case "$arg" in
    --json)  JSON=1 ;;
    --quiet) QUIET=1 ;;
    --help)
      sed -n '2,/^$/p' "$0" | sed 's/^# \{0,1\}//'
      exit 0
      ;;
    *)
      echo "axiom-audit: unknown flag '$arg'" >&2
      echo "Try: $0 --help" >&2
      exit 2
      ;;
  esac
done

# Progress lines go to stderr in --json mode so stdout stays
# parseable, and are silenced entirely in --quiet mode.
say() {
  if [[ $QUIET -eq 1 ]]; then
    :
  elif [[ $JSON -eq 1 ]]; then
    echo "$@" >&2
  else
    echo "$@"
  fi
}

FAIL=0

# --- Helpers ----------------------------------------------------------

# Strip BOTH Lean block comments (/- ... -/, including /-! ... -/ and
# /-- ... -/) AND single-line comments (-- ...).  Block comments are
# non-greedy; Lean does not nest block comments in practice.
strip_comments() {
  perl -0777 -pe 's{/-.*?-/}{}gs' "$1" | sed -E 's|--.*$||'
}

# Count non-blank, non-pure-whitespace lines in the argument files
# after stripping comments.  We want a rough "meaningful LOC" number
# rather than a pure wc -l count, because comment-heavy files would
# otherwise dominate the summary.
loc_in() {
  local total=0
  for f in "$@"; do
    [[ -f "$f" ]] || continue
    local n
    n=$(strip_comments "$f" | grep -cE '^[[:space:]]*[^[:space:]]' || true)
    total=$(( total + n ))
  done
  echo "$total"
}

# List all .lean files under a tree.  Returns zero files silently if
# the tree does not exist yet.
files_in() {
  local dir="$1"
  if [[ -d "$dir" ]]; then
    find "$dir" -name '*.lean' 2>/dev/null || true
  fi
}

# --- 1. Zero sorry in trusted trees ----------------------------------

say "=> Checking for sorry in FX/Kernel/** and FX/Metatheory/**"

KERNEL_SORRY=0
METATHEORY_SORRY=0

for f in $(files_in FX/Kernel); do
  if strip_comments "$f" | grep -qE '\bsorry\b'; then
    echo "FAIL: non-comment sorry in $f" >&2
    KERNEL_SORRY=$(( KERNEL_SORRY + 1 ))
    FAIL=1
  fi
done

for f in $(files_in FX/Metatheory); do
  if strip_comments "$f" | grep -qE '\bsorry\b'; then
    echo "FAIL: non-comment sorry in $f" >&2
    METATHEORY_SORRY=$(( METATHEORY_SORRY + 1 ))
    FAIL=1
  fi
done

# --- 2. Axiom allowlist ----------------------------------------------

say "=> Checking axiom declarations against AXIOMS.md"

DECLARED_AXIOMS=$(mktemp)
ALLOWED_AXIOMS=$(mktemp)
trap 'rm -f "$DECLARED_AXIOMS" "$ALLOWED_AXIOMS"' EXIT

for f in $(files_in FX/Kernel); do
  strip_comments "$f" \
    | grep -oE '^[[:space:]]*axiom[[:space:]]+[A-Za-z_][A-Za-z0-9_]*' \
    | sed -E 's/^[[:space:]]*axiom[[:space:]]+//' \
    || true
done | sort -u > "$DECLARED_AXIOMS"

# Collect allowed axiom names from AXIOMS.md table rows of the form
#   | `name` | ...
grep -E '^\|\s*`[^`]+`' AXIOMS.md 2>/dev/null \
  | sed -E 's/^\|\s*`([^`]+)`.*/\1/' \
  | sort -u > "$ALLOWED_AXIOMS" || true

KERNEL_AXIOMS=$(wc -l < "$DECLARED_AXIOMS")

if [[ $KERNEL_AXIOMS -gt 0 ]]; then
  UNKNOWN=$(comm -23 "$DECLARED_AXIOMS" "$ALLOWED_AXIOMS")
  if [[ -n "$UNKNOWN" ]]; then
    echo "FAIL: axiom(s) not in AXIOMS.md:" >&2
    echo "$UNKNOWN" >&2
    echo "Add them to AXIOMS.md with justification, or remove the declaration." >&2
    FAIL=1
  fi
fi

# --- 3. No axioms outside Kernel/ ------------------------------------

say "=> Checking that no axioms exist outside FX/Kernel/**"

OUTSIDE_AXIOMS=0
for f in $(find FX -name '*.lean' 2>/dev/null | grep -v '^FX/Kernel/' || true); do
  if strip_comments "$f" | grep -qE '^[[:space:]]*axiom[[:space:]]+'; then
    echo "FAIL: axiom(s) in $f — axioms belong only in FX/Kernel/**" >&2
    OUTSIDE_AXIOMS=$(( OUTSIDE_AXIOMS + 1 ))
    FAIL=1
  fi
done

# --- Summary ---------------------------------------------------------

# Meaningful LOC per tree.  `find`-based so trees that don't exist
# yet contribute 0.
KERNEL_LOC=$(loc_in $(files_in FX/Kernel))
METATHEORY_LOC=$(loc_in $(files_in FX/Metatheory))
SYNTAX_LOC=$(loc_in $(files_in FX/Syntax))
UTIL_LOC=$(loc_in $(files_in FX/Util))
CLI_LOC=$(loc_in $(files_in FX/Cli))
TESTS_LOC=$(loc_in $(find tests -name '*.lean' 2>/dev/null || true))

if [[ $JSON -eq 1 ]]; then
  cat <<EOF
{
  "verdict": "$( [[ $FAIL -eq 0 ]] && echo PASS || echo FAIL )",
  "axioms": {
    "declared_in_kernel": $KERNEL_AXIOMS,
    "declared_outside_kernel": $OUTSIDE_AXIOMS,
    "allowlist_size": $(wc -l < "$ALLOWED_AXIOMS")
  },
  "sorry": {
    "kernel": $KERNEL_SORRY,
    "metatheory": $METATHEORY_SORRY
  },
  "loc": {
    "kernel": $KERNEL_LOC,
    "metatheory": $METATHEORY_LOC,
    "syntax": $SYNTAX_LOC,
    "util": $UTIL_LOC,
    "cli": $CLI_LOC,
    "tests": $TESTS_LOC
  }
}
EOF
elif [[ $QUIET -eq 0 ]]; then
  echo ""
  echo "Summary:"
  printf "  %-20s %6d axiom(s) declared / %d allow-listed\n" \
    "FX/Kernel/**:"        "$KERNEL_AXIOMS" "$(wc -l < "$ALLOWED_AXIOMS")"
  printf "  %-20s %6d axiom(s)\n" \
    "elsewhere:"           "$OUTSIDE_AXIOMS"
  printf "  %-20s %6d sorry\n" \
    "FX/Kernel/**:"        "$KERNEL_SORRY"
  printf "  %-20s %6d sorry\n" \
    "FX/Metatheory/**:"    "$METATHEORY_SORRY"
  echo ""
  echo "Lines of Lean (meaningful; comments stripped):"
  printf "  %-20s %6d\n" "FX/Kernel/**:"     "$KERNEL_LOC"
  printf "  %-20s %6d\n" "FX/Metatheory/**:" "$METATHEORY_LOC"
  printf "  %-20s %6d\n" "FX/Syntax/**:"     "$SYNTAX_LOC"
  printf "  %-20s %6d\n" "FX/Util/**:"       "$UTIL_LOC"
  printf "  %-20s %6d\n" "FX/Cli/**:"        "$CLI_LOC"
  printf "  %-20s %6d\n" "tests/**:"         "$TESTS_LOC"
  echo ""
fi

# --- Verdict ---------------------------------------------------------

if [[ $FAIL -eq 0 ]]; then
  [[ $JSON -eq 1 ]] || echo "PASS: $KERNEL_AXIOMS axiom(s) declared, all in AXIOMS.md; zero sorry in trusted trees."
  exit 0
else
  [[ $JSON -eq 1 ]] || echo "FAILED: axiom-audit found violations." >&2
  exit 1
fi
