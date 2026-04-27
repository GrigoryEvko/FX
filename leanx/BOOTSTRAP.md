# Bootstrapping `fxc` via `leanx`

This document describes how to build the native FX compiler (`fxc`)
on a machine that has no prior FX binary.  `leanx` serves as the
one-time bootstrap host.

## Current status (Phase 2.2 — bootstrap not yet executable)

The full chain below requires an FX-source compiler at
`../compiler/` which does not exist yet.  What works today:

  * **Step 1 (build `fxi`)** — works.  `lake build` produces a
    Lean-hosted FX interpreter that accepts Bool + Nat + `Ind`
    programs per the Phase 2.2 surface (see SPEC.md §7 current-
    status snapshot).
  * `fxi tokenize`, `fxi parse`, `fxi check`, `fxi run` all work
    against programs within the Phase 2.2 surface.  See
    `docs/error-codes.md` for the diagnostic registry.
  * **Steps 2-4 (produce and self-host `fxc`)** — blocked on
    `../compiler/` existing.  The interpreter can't bootstrap
    a compiler that hasn't been written yet.

The rest of this document is the design for the bootstrap
pipeline once `../compiler/` lands.  Treat it as a roadmap, not
a set of runnable commands.  The `lake build` + `lake exe
fxi-tests` + `scripts/axiom-audit.sh` triad IS the day-to-day
build; `bash scripts/all.sh` runs all three as the single
CI gate.

## Overview

```
Lean 4 toolchain            ┐
                            │
leanx source                ├──► lake build ──► fxi binary
(FX/**/*.lean)              │                   (Lean-hosted FX interpreter)
                            │
                            │
fxc source (in FX)          ├──► fxi run ──► fxc-seed binary
(../compiler/**/*.fx)       │                (natively-compiled FX compiler,
                            │                 produced by interpreting fxc
                            │                 source under fxi)
                            │
                            │
fxc source (in FX)          ├──► fxc-seed ──► fxc (production binary)
                            ┘
```

After the bootstrap, only the `fxc` binary is on the critical path.
`leanx` is available for cross-checking and for re-bootstrap from
source in isolated environments.

## Prerequisites

1. Lean 4 matching `leanx/lean-toolchain`.  Install via elan:
   ```
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   cd leanx
   elan toolchain install $(cat lean-toolchain | sed 's|.*:||')
   ```

2. A C toolchain (GCC or Clang) for Lean's C backend and for linking
   the resulting `fxc` binary.

3. Z3 (system package or download) if the FX programs being bootstrapped
   use refinements.  `leanx` dispatches SMT queries via subprocess.

## Step 1 — Build `fxi`

```
cd leanx
lake build
```

This produces `build/bin/fxi` — the Lean-hosted FX interpreter.

Verify:
```
./build/bin/fxi --version
./build/bin/fxi test test/Conformance
```

Both should succeed.  If the conformance suite fails, stop — the
bootstrap will not produce a correct compiler.

## Step 2 — Produce `fxc-seed`

Once `../compiler/` exists (the FX compiler source written in FX),
run:

```
cd leanx
./build/bin/fxi run ../compiler/main.fx -- build ../compiler --output=fxc-seed
```

This interprets the FX compiler source under `fxi`.  The compiler's
codegen pass emits native machine code for the same compiler source,
producing `fxc-seed`.

This step is **slow** — potentially hours on a large compiler.  Done
once per bootstrap.  Progress is printed to stderr.

Verify:
```
./fxc-seed --version
```

## Step 3 — Self-host via `fxc-seed`

Use `fxc-seed` to rebuild the compiler natively (fast):

```
./fxc-seed build ../compiler --output=fxc
```

This produces the production `fxc` binary.  From here on, `fxc` is
self-sufficient for day-to-day use.

## Step 4 — Fixpoint check (recommended)

Recompile `fxc` using `fxc`, and verify byte-equality.  This is the
Thompson 1984 mitigation.

```
./fxc build ../compiler --output=fxc2
diff fxc fxc2
```

If `diff` reports no output, the bootstrap has converged.  If the two
binaries differ, there is a non-determinism or Thompson-style
inconsistency to investigate.

Common causes of non-determinism (legitimate):
* Build timestamps embedded in the binary.  Strip with
  `SOURCE_DATE_EPOCH` per reproducible-builds convention.
* Randomness in hash-map iteration or name mangling.  Salt from a
  fixed seed derived from the source content.

The production `fxc` is built with `SOURCE_DATE_EPOCH` pinned and
deterministic salts so fixpoint is byte-equal, not just
semantically-equal.

## Diverse Double-Compiling (optional hardening)

Once `fxc` works, the `fx-self-interp` project (separate repo — see
`SPEC.md` §13) provides a second implementation of FX in FX itself.

```
# In a separate checkout:
git clone https://github.com/fx-lang/fx-self-interp
cd fx-self-interp
../FX/fxc build . --output=fx-self-interp

# Produce fxc via both paths:
../FX/leanx/build/bin/fxi run ../compiler/main.fx -- build ../compiler -o fxc-A
./fx-self-interp run ../compiler/main.fx -- build ../compiler -o fxc-B

# Byte-compare:
diff fxc-A fxc-B
```

If `fxc-A` and `fxc-B` are byte-identical, the compiler is validated
against two independent host implementations (Lean 4 and FX itself).
This is the FX analog of Diverse Double-Compiling (Wheeler 2009),
providing protection against Thompson-style attacks that would have
to succeed against both hosts simultaneously.

## Re-bootstrapping from scratch

If you have no network access and no prior FX binary, the full path
is:

1. Install Lean 4 via elan.
2. Clone this repo.
3. `cd leanx && lake build`.
4. Run Steps 2–4 above.

No network is required after the initial Lean 4 install and repo
clone.

## Troubleshooting

**"fxi exits with 'not yet implemented' error on my FX program."**
Check `leanx`'s phase status in `SPEC.md` §7.  Features outside the
current phase raise a clean error.  For full feature coverage, wait
for later phases or use `fxc` (which has fuller surface coverage once
bootstrapped).

**"lake build fails with Lean version mismatch."**
Run `elan toolchain install` with the version from `lean-toolchain`.
`leanx` pins Lean version deliberately; upgrades happen quarterly.

**"Z3 not found."**
Install Z3 (`apt install z3`, `brew install z3`, or download from
the Z3 GitHub releases).  `leanx` needs Z3 only for FX programs that
use refinements; pure programs bootstrap without it.

**"Bootstrap is slow."**
Expected.  `fxi` is a tree-walking interpreter and the FX compiler is
a non-trivial program.  Bootstrap is a one-time cost; `fxc-seed` and
`fxc` are native and fast.

**"Fixpoint check shows diff."**
See the "Common causes" note under Step 4.  If none apply,
investigate: this indicates a non-determinism in the compiler that
must be fixed.
