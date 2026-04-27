#!/usr/bin/env bash
#
# fxi-smoke.sh — end-to-end smoke test for the `fxi` binary.
#
# Exercises every currently-wired subcommand against a canonical
# two-decl program to catch wiring regressions that the unit-
# test suite misses (flag parsing, stdout/stderr routing,
# exit-code structure).  The Lean tests verify kernel /
# elaborator / evaluator correctness from inside Lean; this
# script verifies `fxi` itself honors its CLI contract.
#
# Usage:
#   cd leanx
#   bash scripts/fxi-smoke.sh
#
# Exits 0 iff every subcommand produces the expected exit code
# and a non-empty stdout on success paths.  Failures print the
# failing command + captured output so CI output is actionable.
#
# Intended subset:
#   fxi version [--json]
#   fxi help
#   fxi help dump
#   fxi self-test
#   fxi tokenize FILE.fx
#   fxi parse    FILE.fx
#   fxi dump --tokens  FILE.fx
#   fxi dump --ast     FILE.fx
#   fxi dump --axioms
#   fxi dump --kernel  FILE.fx
#   fxi check          FILE.fx
#   fxi run            FILE.fx
#
# Run after `lake build` — the binary lives at
# `.lake/build/bin/fxi`.

set -u
set -o pipefail

HERE="$(cd "$(dirname "$0")/.." && pwd)"
cd "$HERE"

if [ -d "$HOME/.elan/bin" ]; then
    export PATH="$HOME/.elan/bin:$PATH"
fi

FXI=".lake/build/bin/fxi"
if [ ! -x "$FXI" ]; then
    echo "fxi-smoke: fxi binary not found at $FXI — run 'lake build' first" >&2
    exit 2
fi

FAILED=0
TMPDIR="$(mktemp -d -t fxi-smoke.XXXXXX)"
trap 'rm -rf "$TMPDIR"' EXIT

# Canonical multi-decl sample program.  Exercises the surface
# features that have landed through the end of B12/B13 partial:
# type params, const decls, match + self-recursion, if-else,
# named-arg reordering.  A broken regression in any of these
# fails the `run` output check below.
SAMPLE="$TMPDIR/hello.fx"
cat > "$SAMPLE" <<'FX'
fn id(a: type, x: a) : a = x;
fn two() : Nat = Nat.Succ(Nat.Succ(Nat.Zero));

const myOne : Nat = Nat.Succ(Nat.Zero);

fn double(n: Nat) : Nat = match n;
  Zero => Nat.Zero;
  Succ(k) => Nat.Succ(Nat.Succ(double(k)));
end match;

fn choose(a: Nat, b: Nat) : Nat = a;

fn demo() : Nat =
  double(choose(b: myOne, a: Nat.Succ(myOne)));
FX

# --- Helpers ------------------------------------------------------

# Run the binary and check exit code + stdout non-emptiness.
# Args: LABEL EXPECTED_EXIT REQUIRE_STDOUT CMD...
check_run () {
    local label="$1"; shift
    local expected_exit="$1"; shift
    local require_stdout="$1"; shift
    local out; local err; local rc
    out=$("$FXI" "$@" 2>"$TMPDIR/err") && rc=$? || rc=$?
    err=$(cat "$TMPDIR/err")

    if [ "$rc" != "$expected_exit" ]; then
        echo "FAIL [$label] exit=$rc expected=$expected_exit" >&2
        echo "  cmd: fxi $*"                                   >&2
        echo "  stdout: $out"                                  >&2
        echo "  stderr: $err"                                  >&2
        FAILED=$((FAILED + 1))
        return
    fi
    if [ "$require_stdout" = "yes" ] && [ -z "$out" ]; then
        echo "FAIL [$label] empty stdout on success path" >&2
        echo "  cmd: fxi $*"                              >&2
        FAILED=$((FAILED + 1))
        return
    fi
    echo "ok   [$label]"
}

# Run the binary and check stdout matches a substring.
# Args: LABEL EXPECTED_EXIT SUBSTRING CMD...
# FAILs if the substring is NOT present (regression ratchet for
# output-format changes).
check_contains () {
    local label="$1"; shift
    local expected_exit="$1"; shift
    local needle="$1"; shift
    local out; local rc
    out=$("$FXI" "$@" 2>/dev/null) && rc=$? || rc=$?
    if [ "$rc" != "$expected_exit" ]; then
        echo "FAIL [$label] exit=$rc expected=$expected_exit" >&2
        echo "  cmd: fxi $*"                                   >&2
        FAILED=$((FAILED + 1))
        return
    fi
    if ! echo "$out" | grep -Fq -- "$needle"; then
        echo "FAIL [$label] stdout missing substring: $needle" >&2
        echo "  cmd: fxi $*"                                     >&2
        echo "  stdout: $out"                                    >&2
        FAILED=$((FAILED + 1))
        return
    fi
    echo "ok   [$label]"
}

# Run the binary and check stdout does NOT match a substring.
# FAILs if the needle IS present — useful for regression ratchets
# against unwanted output formats (e.g., `FX.Kernel.Term.pi`
# appearing after the compact pretty-printer landed).
check_excludes () {
    local label="$1"; shift
    local expected_exit="$1"; shift
    local needle="$1"; shift
    local out; local rc
    out=$("$FXI" "$@" 2>/dev/null) && rc=$? || rc=$?
    if [ "$rc" != "$expected_exit" ]; then
        echo "FAIL [$label] exit=$rc expected=$expected_exit" >&2
        echo "  cmd: fxi $*"                                   >&2
        FAILED=$((FAILED + 1))
        return
    fi
    if echo "$out" | grep -Fq -- "$needle"; then
        echo "FAIL [$label] stdout contains forbidden: $needle" >&2
        echo "  cmd: fxi $*"                                     >&2
        echo "  stdout: $out"                                    >&2
        FAILED=$((FAILED + 1))
        return
    fi
    echo "ok   [$label]"
}

# --- Subcommands --------------------------------------------------

echo "=== fxi-smoke ==="

check_run "version plain"  0 yes version
check_run "version --json" 0 yes version --json
check_run "-V"             0 yes -V
check_run "help"           0 yes --help
check_run "help dump"      0 yes help dump
check_run "self-test"      0 yes self-test

check_run "tokenize"           0 yes tokenize   "$SAMPLE"
check_run "parse"              0 yes parse      "$SAMPLE"
check_run "dump --tokens"      0 yes dump --tokens "$SAMPLE"
check_run "dump --ast"         0 yes dump --ast    "$SAMPLE"
check_run "dump --axioms"      0 yes dump --axioms
check_run "dump --kernel"      0 yes dump --kernel "$SAMPLE"
check_run "check"              0 yes check      "$SAMPLE"
check_run "show-axioms"        0 yes show-axioms two "$SAMPLE"
check_run "run"                0 yes run        "$SAMPLE"

# Regression ratchets for output format — catch silent changes
# that would otherwise slip past the lake-build gate.

# `dump --kernel` uses the compact termPretty (cli/main.lean's
# `termPretty` walker).  If a regression reverted to raw `repr`,
# the output would contain fully-qualified Lean constructor
# names.  Exclude a few to catch that.
check_excludes "dump --kernel: no raw Term repr" 0 \
    "FX.Kernel.Term.pi" dump --kernel "$SAMPLE"
check_excludes "dump --kernel: no raw Grade repr" 0 \
    "FX.Kernel.Usage.one" dump --kernel "$SAMPLE"

# `dump --kernel` should use the compact Π/λ glyphs produced by
# the pretty-printer.  A regression that emitted `Pi(...)` text
# style instead would fail this.
check_contains "dump --kernel: compact Π glyph" 0 \
    "Π(" dump --kernel "$SAMPLE"

# `run` on the sample computes several outputs:
#   two = 2       — plain Succ chain
#   myOne = 1     — const decl eval
#   demo = 4      — double(choose(myOne, Succ(myOne))) with named
#                   args reordered → double(Succ(myOne)) →
#                   double(Succ(Succ(Zero))) = Succ^4(Zero) = 4
# A regression in const lookup, named-arg reorder, match + self-
# recursion, or the Nat pretty-printer would miss at least one
# of these.
check_contains "run: two = 2"     0 "two = 2"      run "$SAMPLE"
check_contains "run: myOne = 1"   0 "myOne = 1"    run "$SAMPLE"
check_contains "run: demo = 4"    0 "demo = 4"     run "$SAMPLE"

# `check` prints an `ok` status line per decl.
check_contains "check: ok status line" 0 "ok        two" check "$SAMPLE"
check_contains "check: multi-decl all ok" 0 "ok        demo" check "$SAMPLE"

# ### B9 — user ADT end-to-end smoke
#
# Pin that `fxi run` on a user-declared ADT program exercises the
# full parse → elab → typing → eval pipeline.  A regression in
# userSpecs threading would drop one of these values.
ADT_SAMPLE="$TMPDIR/adt.fx"
cat >"$ADT_SAMPLE" <<'ADTEOF'
type color
  Red;
  Green;
  Blue;
end type;

type tree
  Leaf;
  Node(Nat, tree, tree);
end type;

fn size(t: tree) : Nat = match t;
  Leaf => Nat.Zero;
  Node(k, l, r) => Nat.Succ(size(l));
end match;

fn describe(c: color) : Nat = match c;
  Red => Nat.Zero;
  Green => Nat.Succ(Nat.Zero);
  Blue => Nat.Succ(Nat.Succ(Nat.Zero));
end match;

fn main_color() : Nat = describe(Blue);
fn main_tree() : Nat = size(Node(Nat.Zero, Node(Nat.Zero, Leaf, Leaf), Leaf));
fn ctor_print() : color = Blue;

type point {
  x: Nat;
  y: Nat;
};
fn main_field() : Nat = Point(Nat.Succ(Nat.Succ(Nat.Zero)), Nat.Zero).x;
ADTEOF
check_contains "run: adt color Blue = 2"      0 "main_color = 2"       run "$ADT_SAMPLE"
check_contains "run: adt tree depth = 2"      0 "main_tree = 2"        run "$ADT_SAMPLE"
check_contains "run: adt pretty ctor name"    0 "ctor_print = color.Blue"  run "$ADT_SAMPLE"
check_contains "run: record field access"    0 "main_field = 2"        run "$ADT_SAMPLE"
check_contains "check: adt size ok"           0 "ok        size"       check "$ADT_SAMPLE"

# ### F2 — fxi repl end-to-end smoke
#
# Pipe a scripted session into `fxi repl` and check it survives:
#   * prints the greeting
#   * accepts a one-line decl
#   * `:decls` lists the registered decl
#   * evaluates a second reference to the prior decl (cross-line
#     state — this is the REPL's load-bearing property)
#   * `:quit` exits cleanly with code 0
REPL_OUT="$TMPDIR/repl.out"
# Session covers: one-liner decl, multi-line block-form decl
# (5 lines, processes once `end fn;` closes the balance), and
# a cross-line reference (two calls one) — the REPL's
# load-bearing feature.
printf 'fn one() : Nat = Nat.Succ(Nat.Zero);\nfn compute(n: Nat) : Nat\nbegin fn\n  let m = Nat.Succ(n);\n  return m;\nend fn;\nfn two() : Nat = Nat.Succ(one());\n:decls\n:quit\n' \
  | "$FXI" repl > "$REPL_OUT" 2>&1
REPL_RC=$?
if [ "$REPL_RC" -ne 0 ]; then
    echo "FAIL [repl: exit code] rc=$REPL_RC expected=0" >&2
    echo "  output: $(cat "$REPL_OUT")"                  >&2
    FAILED=$((FAILED + 1))
else
    echo "ok   [repl: exit code]"
fi
for needle in \
    "fxi repl — type :help" \
    "one = 1" \
    "two = 2" \
    "compute = <closure>" \
    "  one : Π(_:Unit" \
    "  two : Π(_:Unit" \
    "  compute : Π(_:Nat"
do
    if ! grep -Fq -- "$needle" "$REPL_OUT"; then
        echo "FAIL [repl: missing output '$needle']"     >&2
        echo "  output:"                                  >&2
        sed 's/^/    /' "$REPL_OUT"                       >&2
        FAILED=$((FAILED + 1))
    else
        echo "ok   [repl: has '$needle']"
    fi
done

# Negative paths — each must exit 1 (user error), not 0 or 3.
BADPATH="$TMPDIR/nonexistent.fx"
check_run "missing file"      1 no check "$BADPATH"
check_run "bad subcmd"        1 no not-a-real-subcommand

echo
if [ "$FAILED" -ne 0 ]; then
    echo "fxi-smoke: $FAILED check(s) FAILED" >&2
    exit 1
fi
echo "fxi-smoke: OK — every subcommand behaved as expected."
