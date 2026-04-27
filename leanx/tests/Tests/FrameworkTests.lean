import Tests.Framework
import Tests.Runner

/-!
# Framework self-tests

Meta-tests that verify the `Tests.Framework` harness itself.
These run inside `fxi-tests` like any other suite — a broken
framework would be visible as its own test failures.

Scope:

  * `check` increments the suite's pass counter on match and the
    fail counter on mismatch.
  * `checkWith` uses the supplied comparator.  In particular, a
    comparator that ignores some field lets users compare
    structures modulo that field.
  * A crashing suite surfaces as a `crashed := some _` record and
    does NOT abort sibling suites.
  * The `--suite` filter's substring match behaves as documented.
  * The CLI argument parser accepts known flags and rejects
    unknown ones.
  * `Repr` of the values being compared is **not** invoked on
    match — we witness this via a `Repr` instance that throws if
    called.

The meta-tests drive the framework's internals through public
entry points only.  They use `Tests.resetTotals` to avoid
polluting the real session counters.
-/

namespace Tests.FrameworkTests

open Tests

/-- Opaque wrapper whose `Repr` instance panics if invoked.  Used
    to verify that `check` on a passing case never touches
    `repr`. -/
structure BombRepr where
  x : Nat
  deriving DecidableEq

instance : Repr BombRepr where
  reprPrec := fun _ _ =>
    panic! "BombRepr.repr was invoked — should never happen on a passing check"

/-- Run a sub-suite `name` in isolation and return its result.
    We do a miniature `runSuites` so we can introspect counts
    without disturbing the live session state the outer runner
    depends on.  Saves/restores the current accumulator.

    Wrapped in `withSilent` — the inner suite deliberately produces
    failures to verify the failure path, but we don't want those
    FAIL lines polluting the real terminal output. -/
private def runIsolated (title : String) (body : IO Unit) : IO SuiteResult :=
  withSilent do
    let entries : Array SuiteEntry := #[{ title := title, run := body }]
    let results ← runSuites { filter := none, format := .human } entries
    return results[0]!

def run : IO Unit := Tests.suite "Tests.FrameworkTests" do
  /- check / checkTrue / checkFalse succeed on match -/
  let runResult ← runIsolated "meta-pass" do
    check "eq Nat"          (3 : Nat)  (1 + 2)
    check "eq String"       "abc"      ("a" ++ "bc")
    checkTrue  "true"       true
    checkFalse "not false"  false
  check "meta-pass passes=4" 4 runResult.passes
  check "meta-pass fails=0"  0 runResult.fails
  check "meta-pass no crash" (none : Option String) runResult.crashed

  /- check fails on mismatch and records failure details -/
  let runResult ← runIsolated "meta-fail" do
    check "bad"  (1 : Nat) 2
    checkTrue "t"  false
  check "meta-fail passes=0" 0 runResult.passes
  check "meta-fail fails=2"  2 runResult.fails
  check "meta-fail failure 0 name" "bad"
    (runResult.failures[0]? |>.map (·.name) |>.getD "<missing>")
  check "meta-fail failure 1 name" "t"
    (runResult.failures[1]? |>.map (·.name) |>.getD "<missing>")

  /- checkWith lets the caller pass a custom comparator.  Here we
     compare pairs ignoring the second component. -/
  let runResult ← runIsolated "meta-checkWith" do
    let fstEqComparator : Nat × String → Nat × String → Bool :=
      fun (leftFst, _) (rightFst, _) => decide (leftFst = rightFst)
    checkWith "fst eq" fstEqComparator (1, "foo") (1, "bar")
    checkWith "fst ne" fstEqComparator (1, "x")   (2, "x")
  check "meta-checkWith passes=1" 1 runResult.passes
  check "meta-checkWith fails=1"  1 runResult.fails

  /- Repr is NOT called on match.  The BombRepr instance panics
     if invoked; the `check` call below must therefore not throw. -/
  let runResult ← runIsolated "meta-lazy-repr" do
    check "bomb eq" { x := 7 : BombRepr } { x := 7 }
  check "meta-lazy-repr passes=1" 1 runResult.passes
  check "meta-lazy-repr fails=0"  0 runResult.fails

  /- A crashing suite surfaces as `crashed := some _` and is
     counted as a single failure.  Sibling suites still run. -/
  let runResult ← runIsolated "meta-crash" do
    throw (IO.userError "boom")
  check "meta-crash has crash message"
    true runResult.crashed.isSome
  check "meta-crash fails >= 1"
    true (runResult.fails ≥ 1)

  /- failWith records an unconditional failure. -/
  let runResult ← runIsolated "meta-failWith" do
    failWith "explicit" "the reason"
  check "meta-failWith fails=1"       1 runResult.fails
  check "meta-failWith has 1 failure" 1 runResult.failures.size

  /- SuiteEntry.matches substring filter. -/
  let suiteEntry : SuiteEntry := { title := "Tests.Syntax.LexerTests", run := pure () }
  checkTrue  "filter none matches"
    (suiteEntry.matchesFilter { filter := none })
  checkTrue  "filter substring hit"
    (suiteEntry.matchesFilter { filter := some "Lexer" })
  checkFalse "filter substring miss"
    (suiteEntry.matchesFilter { filter := some "Parser" })
  checkTrue  "filter full title hit"
    (suiteEntry.matchesFilter { filter := some "Tests.Syntax.LexerTests" })

  /- CLI argument parser happy paths. -/
  let parse := Tests.Runner.parseArgs
  match parse [] with
  | .ok (.run runConfig) =>
    check "empty argv → run with defaults (filter)"
      (none : Option String) runConfig.filter
    check "empty argv → run with defaults (verbose)"
      false runConfig.verbose
    check "empty argv → run with defaults (format)"
      OutputFormat.human runConfig.format
  | _ => failWith "parseArgs []" "expected .ok (.run {})"

  match parse ["--help"] with
  | .ok .help => check "--help ok" true true
  | _         => failWith "parseArgs [--help]" "expected .ok .help"

  match parse ["--list"] with
  | .ok .list => check "--list ok" true true
  | _         => failWith "parseArgs [--list]" "expected .ok .list"

  match parse ["--verbose"] with
  | .ok (.run runConfig) => check "--verbose sets flag" true runConfig.verbose
  | _              => failWith "--verbose" "expected .ok (.run _)"

  match parse ["--suite", "Lexer"] with
  | .ok (.run runConfig) => check "--suite sets filter" (some "Lexer") runConfig.filter
  | _              => failWith "--suite" "expected .ok (.run _)"

  match parse ["--suite=Parser"] with
  | .ok (.run runConfig) => check "--suite= sets filter" (some "Parser") runConfig.filter
  | _              => failWith "--suite=" "expected .ok (.run _)"

  match parse ["--format", "json"] with
  | .ok (.run runConfig) => check "--format json" OutputFormat.json runConfig.format
  | _              => failWith "--format json" "expected .ok (.run _)"

  match parse ["--format=tap"] with
  | .ok (.run runConfig) => check "--format=tap" OutputFormat.tap runConfig.format
  | _              => failWith "--format=tap" "expected .ok (.run _)"

  /- CLI argument parser sad paths. -/
  match parse ["--nope"] with
  | .error _ => check "unknown flag rejected" true true
  | _        => failWith "unknown flag" "expected .error"

  match parse ["--suite"] with
  | .error _ => check "--suite without arg rejected" true true
  | _        => failWith "--suite bare" "expected .error"

  match parse ["--format", "xml"] with
  | .error _ => check "bad --format value rejected" true true
  | _        => failWith "--format xml" "expected .error"

  /- Renderers produce the expected shape.  We can't byte-compare
     (timings vary) so we smoke-test by substring containment. -/
  let sample : Array SuiteResult := #[
    { title := "Alpha", passes := 3, fails := 0, failures := #[]
    , elapsedNs := 1000, crashed := none },
    { title := "Beta",  passes := 1, fails := 1
    , failures := #[{ name := "x", expected := "1", actual := "2" }]
    , elapsedNs := 2000, crashed := none }]
  -- Helper: does `haystack` contain `needle` at least once?
  let contains : String → String → Bool :=
    fun haystack needle => decide ((haystack.splitOn needle).length > 1)
  let humanOutput := renderHuman sample
  checkTrue "human renders Alpha"      (contains humanOutput "Alpha")
  checkTrue "human renders Beta"       (contains humanOutput "Beta")
  checkTrue "human renders totals"     (contains humanOutput "totals")
  checkTrue "human tags passing 'ok'"  (contains humanOutput "[ok] Alpha")
  checkTrue "human tags failing 'FAIL'" (contains humanOutput "[FAIL] Beta")

  let tapOutput := renderTap sample
  checkTrue "tap has plan"       (contains tapOutput "1..2")
  checkTrue "tap has ok 1"       (contains tapOutput "ok 1 - Alpha")
  checkTrue "tap has not ok 2"   (contains tapOutput "not ok 2 - Beta")

  let jsonOutput := renderJson sample
  checkTrue "json has Alpha"     (contains jsonOutput "\"title\":\"Alpha\"")
  checkTrue "json has Beta"      (contains jsonOutput "\"title\":\"Beta\"")
  checkTrue "json has totals"    (contains jsonOutput "\"type\":\"totals\"")

  /- renderJson escapes special characters. -/
  let tricky : Array SuiteResult := #[
    { title := "quote\"and\\back", passes := 0, fails := 1
    , failures := #[{ name := "n", expected := "line1\nline2"
                    , actual := "tab\there" }]
    , elapsedNs := 0, crashed := some "bye\"now" }]
  let j2 := renderJson tricky
  checkTrue "json escapes \\\"" (contains j2 "quote\\\"and\\\\back")
  checkTrue "json escapes \\n"  (contains j2 "line1\\nline2")
  checkTrue "json escapes \\t"  (contains j2 "tab\\there")

  /- Bench scaffold records timing without asserting. -/
  -- Drain any residue first so we measure only our bench call.
  let _ ← drainBenches
  bench "meta-bench" do
    let mut rollingSum := 0
    for i in [0:100] do rollingSum := rollingSum + i
    let _ := rollingSum
    pure ()
  let benchResults ← drainBenches
  check "bench recorded 1 result" 1 benchResults.size
  check "bench result has correct name" "meta-bench"
    (benchResults[0]? |>.map (·.name) |>.getD "<missing>")

end Tests.FrameworkTests
