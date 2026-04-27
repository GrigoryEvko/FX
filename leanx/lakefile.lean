import Lake
open Lake DSL

-- leanx: Lean 4 reference interpreter for FX.
--
-- Build:
--   lake build            -- compile library and executable
--   lake exe fxi          -- run the fxi CLI
--   lake test             -- run the test suite (configured below)
--
-- See SPEC.md for the full design.

package fxinterp where
  -- Standard defaults.
  leanOptions := #[
    -- Hard-fail on unused variables.  Keeps untrusted layers tight.
    ⟨`linter.unusedVariables, true⟩,
    -- We intentionally structure large files; don't warn.
    ⟨`maxHeartbeats, 400000⟩
  ]

-- The library — all FX-related Lean code lives under FX/.
-- `globs` picks up every .lean file under the FX namespace so the
-- module skeleton files (Kernel/*, Metatheory/*, Elab/*, …) compile
-- alongside FX.Core.
@[default_target]
lean_lib FX where
  srcDir := "."
  roots := #[`FX]
  globs := #[.andSubmodules `FX]

-- The fxi binary — CLI entry point.
@[default_target]
lean_exe fxi where
  root := `FX.Cli.Main
  supportInterpreter := true

-- Test library — all `.lean` files under tests/Tests are
-- compiled together and any compile-time `example : P := by
-- decide` tests are verified at build time.  Runtime tests
-- (lexer/parser IO-based checks) are aggregated into the
-- fxi-tests executable below.
lean_lib Tests where
  srcDir := "tests"
  roots := #[`Tests]
  globs := #[.andSubmodules `Tests]

-- Test runner executable.  `lake exe fxi-tests` runs all
-- runtime-test suites; exit code is zero iff every check
-- passed.  Compile-time proof tests are already verified by
-- the `Tests` library build; this executable adds the runtime
-- checks on top.
lean_exe «fxi-tests» where
  root := `Tests.Main
  srcDir := "tests"

-- Scripts — referenced by CI.  The actual shell scripts live in
-- leanx/scripts/ and are invoked directly; Lake lists them here so
-- `lake script help` mentions them.
script axiomAudit (_args) do
  IO.println "Run scripts/axiom-audit.sh directly."
  return 0

script coverage (_args) do
  IO.println "Run scripts/coverage.sh directly."
  return 0

-- `lake script tests` — full build + run.
--
-- The two-step build is deliberate.  `lake build` compiles the
-- default `FX` library + the `fxi-tests` executable root, but
-- `Tests.Main`'s transitive imports don't always cover every
-- file under `tests/Tests/**` (umbrella files that import each
-- test file live in `Tests`, not in `Tests.Main`).  An explicit
-- `lake build Tests` forces compilation of every test module,
-- which is the only way stale references like a rename-broken
-- `Ctx.empty` get caught at CI time rather than surfacing only
-- when the runtime runner happens to import the offending file.
script tests (_args) do
  let buildOut ← IO.Process.output { cmd := "lake", args := #["build"] }
  if buildOut.exitCode != 0 then
    IO.eprintln buildOut.stderr
    return UInt32.ofNat buildOut.exitCode.toNat
  let buildTestsOut ← IO.Process.output
    { cmd := "lake", args := #["build", "Tests"] }
  if buildTestsOut.exitCode != 0 then
    IO.eprintln buildTestsOut.stderr
    return UInt32.ofNat buildTestsOut.exitCode.toNat
  let runOut ← IO.Process.output { cmd := "lake", args := #["exe", "fxi-tests"] }
  IO.print runOut.stdout
  IO.eprint runOut.stderr
  return UInt32.ofNat runOut.exitCode.toNat
