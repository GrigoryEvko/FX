-- Single umbrella import — `Tests.lean` pulls in every compile-time
-- and runtime test module.  Adding a new suite requires editing
-- `Tests.lean` (for the build-time check) and appending one line
-- to `registered` below (for the runtime runner); the import list
-- here stays fixed.
import Tests

/-!
# Test runner

Aggregates runtime test suites into a single executable.

The compile-time proof suites (every `example : P := by decide`
in `Tests/Kernel/**` and `Tests/Syntax/**`) are checked when the
`Tests` library is built; this runner adds the runtime checks on
top and returns a non-zero exit code if any `check` failed or if
any suite body threw.

## Usage

```
  fxi-tests                  # run every suite, human output
  fxi-tests --verbose        # print each passing check too
  fxi-tests --suite Lexer    # only suites whose title contains "Lexer"
  fxi-tests --format=tap     # TAP v13 output for CI scrapers
  fxi-tests --format=json    # one JSON object per suite + totals
  fxi-tests --list           # print registered suite titles and exit
  fxi-tests --help           # show this help
```

## Adding a suite

 1. Write `def run : IO Unit := Tests.suite "Title" do ...` in a
    new file under `tests/Tests/…`.
 2. Import that module above.
 3. Append a `SuiteEntry` to `registered` below.

Auto-registration via typeclass is a Phase 2 refinement; with
~10 suites, the manual list is still obviously correct.
-/

open Tests

/-- Every runtime test suite, declared in the order they should
    run.  Adding a new suite is a one-line edit here plus the
    corresponding `import` above. -/
def registered : Array SuiteEntry := #[
  { title := "Tests.Util.BasicTests"
  , run   := Tests.Util.BasicTests.run },
  { title := "Tests.Syntax.SpanTests"
  , run   := Tests.Syntax.SpanTests.run },
  { title := "Tests.Syntax.TokenTests"
  , run   := Tests.Syntax.TokenTests.run },
  { title := "Tests.Syntax.LexerTests"
  , run   := Tests.Syntax.LexerTests.run },
  { title := "Tests.Syntax.ParserTests"
  , run   := Tests.Syntax.ParserTests.run },
  { title := "Tests.Syntax.SessionParserTests"
  , run   := Tests.Syntax.SessionParserTests.run },
  { title := "Tests.Syntax.TryParserTests"
  , run   := Tests.Syntax.TryParserTests.run },
  { title := "Tests.Syntax.EffectParserTests"
  , run   := Tests.Syntax.EffectParserTests.run },
  { title := "Tests.Syntax.HandleParserTests"
  , run   := Tests.Syntax.HandleParserTests.run },
  { title := "Tests.Syntax.TokenStreamTests"
  , run   := Tests.Syntax.TokenStreamTests.run },
  { title := "Tests.Syntax.ParserRobustnessTests"
  , run   := Tests.Syntax.ParserRobustnessTests.run },
  { title := "Tests.Elab.SessionElabTests"
  , run   := Tests.Elab.SessionElabTests.run },
  { title := "Tests.Elab.ScopeTests"
  , run   := Tests.Elab.ScopeTests.run },
  { title := "Tests.Elab.ElaborateTests"
  , run   := Tests.Elab.ElaborateTests.run },
  { title := "Tests.Elab.RefGradeEndToEndTests"
  , run   := Tests.Elab.RefGradeEndToEndTests.run },
  { title := "Tests.Elab.CopyGradeEndToEndTests"
  , run   := Tests.Elab.CopyGradeEndToEndTests.run },
  { title := "Tests.Elab.CopySoundnessTests"
  , run   := Tests.Elab.CopySoundnessTests.run },
  { title := "Tests.Kernel.InductiveTests"
  , run   := Tests.Kernel.InductiveTests.run },
  { title := "Tests.Kernel.CoinductiveTests"
  , run   := Tests.Kernel.CoinductiveTests.run },
  { title := "Tests.Kernel.IntegrationTests"
  , run   := Tests.Kernel.IntegrationTests.run },
  { title := "Tests.Kernel.EnvTests"
  , run   := Tests.Kernel.EnvTests.run },
  { title := "Tests.Elab.CrossDeclTests"
  , run   := Tests.Elab.CrossDeclTests.run },
  { title := "Tests.Elab.PreludeTests"
  , run   := Tests.Elab.PreludeTests.run },
  { title := "Tests.Elab.IfExprTests"
  , run   := Tests.Elab.IfExprTests.run },
  { title := "Tests.Elab.MatchExprTests"
  , run   := Tests.Elab.MatchExprTests.run },
  { title := "Tests.Elab.SurfaceSugarTests"
  , run   := Tests.Elab.SurfaceSugarTests.run },
  { title := "Tests.Elab.TypeParamsTests"
  , run   := Tests.Elab.TypeParamsTests.run },
  { title := "Tests.Elab.RecursionTests"
  , run   := Tests.Elab.RecursionTests.run },
  { title := "Tests.Eval.InterpTests"
  , run   := Tests.Eval.InterpTests.run },
  { title := "Tests.Eval.InterpAdvancedTests"
  , run   := Tests.Eval.InterpAdvancedTests.run },
  { title := "Tests.FrameworkTests"
  , run   := Tests.FrameworkTests.run },
  -- SMT-LIB2 encoder runtime tests (V8.1 / E1).
  { title := "Tests.Smt.EncodeTests"
  , run   := Tests.Smt.EncodeTests.run },
  -- Mode-indexed Term inductive runtime tests (V1.3 / R1.4).
  { title := "Tests.KernelMTT.TermTests"
  , run   := Tests.KernelMTT.TermTests.run },
  -- Typed shift + substitution runtime tests (W3).
  { title := "Tests.KernelMTT.SubstitutionTests"
  , run   := Tests.KernelMTT.SubstitutionTests.run },
  -- Reduction (β / ι / ν / modElim-ι / idJ-ι / coerceCell-strip
  -- + whnf) runtime tests (V1.15).
  { title := "Tests.KernelMTT.ReductionTests"
  , run   := Tests.KernelMTT.ReductionTests.run },
  -- Convertibility (definitional equality + η on Lam) runtime
  -- tests (V1.5 first installment).
  { title := "Tests.KernelMTT.ConversionTests"
  , run   := Tests.KernelMTT.ConversionTests.run },
  -- Subtyping (T-sub: U-cumul + Pi/Sigma variance + effect
  -- subsumption + forallLevel + convEq fast path) runtime
  -- tests (V1.5 second installment).
  { title := "Tests.KernelMTT.SubtypingTests"
  , run   := Tests.KernelMTT.SubtypingTests.run }
]

def main (args : List String) : IO UInt32 := do
  match Tests.Runner.parseArgs args with
  | .error msg => do
    IO.eprintln msg
    IO.eprintln Tests.Runner.helpText
    return 2
  | .ok Tests.Runner.Action.help => do
    IO.println Tests.Runner.helpText
    return 0
  | .ok Tests.Runner.Action.list => do
    for e in registered do IO.println e.title
    return 0
  | .ok (Tests.Runner.Action.run runConfig) => do
    if runConfig.format = .human then
      IO.println "fxi-tests — runtime test suite"
      IO.println ""
    -- tap/json formats want only their structured output on
    -- stdout.  We silence per-suite headers (the "--- Title ---"
    -- lines) for those modes; failures still go to stderr because
    -- CI scrapers typically capture stdout only.
    let results ←
      if runConfig.format = .human then
        runSuites runConfig registered
      else
        Tests.withSilent (runSuites runConfig registered)
    if runConfig.format = .human then IO.println ""
    let allPassed ← printSummary runConfig results
    return (if allPassed then 0 else 1)
