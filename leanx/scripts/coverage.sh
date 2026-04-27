#!/usr/bin/env bash
#
# coverage.sh — compute the verified/implemented ratio.
#
# implemented: conformance tests tagged `// @phase N`
# verified:    additionally tagged `// @verified-by <theorem-name>`
#
# The load-bearing invariant is `verified / implemented == 1`:
# features don't merge ahead of their proofs.  This script exists so
# CI can enforce the invariant mechanically; the invariant itself is
# social policy documented in SPEC.md §4.
#
# Flags:
#   --json     emit the summary as JSON (stdout).  Progress goes to
#              stderr in this mode.
#   --help     show this header and exit 0.
#
# Exit code:
#   0 — ratio is 1.0 (or no tests tagged yet).
#   1 — ratio is below 1.0.
#   2 — unknown flag or other usage error.

set -eu  # no pipefail — empty greps are expected in early phases

cd "$(dirname "$0")/.."

# --- Flag parsing -----------------------------------------------------

JSON=0

for arg in "$@"; do
  case "$arg" in
    --json) JSON=1 ;;
    --help)
      sed -n '2,/^$/p' "$0" | sed 's/^# \{0,1\}//'
      exit 0
      ;;
    *)
      echo "coverage: unknown flag '$arg'" >&2
      echo "Try: $0 --help" >&2
      exit 2
      ;;
  esac
done

say() {
  if [[ $JSON -eq 1 ]]; then echo "$@" >&2; else echo "$@"; fi
}

# --- Tag counting ----------------------------------------------------

# Count files under DIR that contain at least one line matching TAG.
# Files, not matches — one file tagged with `@phase N @phase M` still
# counts once.  This matches the convention that each conformance
# test is one file.
count_tagged() {
  local tag="$1"
  local dir="$2"
  if [[ -d "$dir" ]]; then
    grep -rl -- "$tag" "$dir" 2>/dev/null | wc -l | tr -d ' '
  else
    echo 0
  fi
}

# Where conformance tests live.  SPEC.md §5 lists `test/Conformance/`
# as the canonical path; fall back to `tests/Conformance/` in case a
# future reshuffle lands there first.
CONFORMANCE_DIR="test/Conformance"
if [[ ! -d "$CONFORMANCE_DIR" && -d "tests/Conformance" ]]; then
  CONFORMANCE_DIR="tests/Conformance"
fi

IMPLEMENTED=$(count_tagged '@phase' "$CONFORMANCE_DIR")
VERIFIED=$(count_tagged '@verified-by' "$CONFORMANCE_DIR")

# Optional: per-section coverage, if tags like `@section 3.3` are used.
# Counted in aggregate (not per-section) for the top-line number; the
# per-section breakdown is exported in JSON mode.
SECTIONS_TAGGED=$(count_tagged '@section' "$CONFORMANCE_DIR")

# --- Output ---------------------------------------------------------

if [[ "$IMPLEMENTED" -eq 0 ]]; then
  if [[ $JSON -eq 1 ]]; then
    cat <<EOF
{
  "verdict": "PASS",
  "dir": "$CONFORMANCE_DIR",
  "implemented": 0,
  "verified": 0,
  "sections_tagged": $SECTIONS_TAGGED,
  "ratio": null,
  "note": "no conformance tests tagged yet"
}
EOF
  else
    echo "implemented:     0"
    echo "verified:        0"
    echo "sections tagged: $SECTIONS_TAGGED"
    echo "ratio:           — (no tests tagged yet)"
  fi
  exit 0
fi

PCT=$(( (VERIFIED * 100) / IMPLEMENTED ))
UNVERIFIED=$(( IMPLEMENTED - VERIFIED ))

if [[ $JSON -eq 1 ]]; then
  VERDICT="FAIL"
  [[ "$VERIFIED" -ge "$IMPLEMENTED" ]] && VERDICT="PASS"
  cat <<EOF
{
  "verdict": "$VERDICT",
  "dir": "$CONFORMANCE_DIR",
  "implemented": $IMPLEMENTED,
  "verified": $VERIFIED,
  "unverified": $UNVERIFIED,
  "sections_tagged": $SECTIONS_TAGGED,
  "ratio_percent": $PCT
}
EOF
else
  echo "conformance dir: $CONFORMANCE_DIR"
  echo "implemented:     $IMPLEMENTED"
  echo "verified:        $VERIFIED"
  echo "sections tagged: $SECTIONS_TAGGED"
  echo "ratio:           ${PCT}% ($VERIFIED / $IMPLEMENTED)"
fi

if [[ "$VERIFIED" -lt "$IMPLEMENTED" ]]; then
  echo "WARNING: $UNVERIFIED implemented feature(s) lack @verified-by tag." >&2
  exit 1
fi
exit 0
