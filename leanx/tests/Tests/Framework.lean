/-!
# Test framework

Runtime assertion harness used by the IO-test suites (Lexer,
Parser, Token, Span, Util).  The grade-dimension and
kernel-algebra suites prefer compile-time proofs via
`example : P := by decide` and do not need this harness at all —
their "tests" are theorems checked by `lake build`.

## `decide` vs `native_decide`

The suites in this tree use both deciders; the choice is
mechanical, not stylistic:

  * `by decide` — when the property reduces to `true` under the
    Lean kernel's definitional reduction.  Use for Nat/Bool
    arithmetic, grade-semiring lookups on concrete three-element
    carriers, and any `DecidableEq` goal over plain data.
  * `by native_decide` — when the goal requires evaluating a
    `partial def` (Term.structEq, Reduction.whnf, Elaborate.
    checkFile, Interp.eval) or otherwise crosses a boundary the
    kernel's reducer can't unfold.  Compiles the decision
    procedure to native code; necessary whenever `by decide`
    would leave the goal stuck on an unreducible application.

Rule of thumb: if the goal mentions `Term`, `Value`, or anything
going through elab/eval, it needs `native_decide`.  Pure
grade/semiring/universe-level goals take `decide`.  Mixing the
two in one `example` is fine — the choice is per-proof.

## Harness contract

  * `check name expected actual` — if `expected == actual`,
    increment the current suite's pass counter; otherwise format
    a structured failure and increment the fail counter.  The
    `Repr` instance on the arguments is invoked **only on
    failure** — this matters for large values (whole token
    streams, ASTs) that cost real time to format.
  * `checkWith name cmp expected actual` — same as `check` but
    uses a user-supplied comparator `valueType → valueType → Bool` instead of
    `DecidableEq`.  Useful for comparing ASTs modulo spans.
  * `checkTrue name b` / `checkFalse name b` — boolean shortcuts
    for cases where `DecidableEq` is heavy but a predicate is
    cheap.
  * `suite title body` — groups a sequence of `check` calls.
    Records suite name + starts per-suite pass/fail counters;
    isolates exceptions so a crash inside one suite does not
    contaminate sibling suites.
  * `bench name body` — §23.5 scaffold.  Runs `body` once,
    measures wall time, records as a `benchResult`; does **not**
    assert anything.  Rigorous statistical benching (median/p95)
    is Phase 2.
  * `RunConfig` / `runSuites` / `printSummary` — the runner API
    consumed by `Tests.Main`.

## Mutability

Pass/fail counts + suite results live in a few `IO.Ref` cells.
This keeps the test body readable — no threading state through
every check.  The trade is thread-safety, which we do not need
for a sequential test runner.  If we ever parallelize we rewrap
these in `IO.Mutex`.

## Output formats

Three exit formats are supported by `printSummary`:

  * `.human` — pretty, colorless, for terminals.
  * `.tap`   — Test Anything Protocol v12, for CI scrapers.
  * `.json`  — one JSON object per line + a final summary object,
               for the §24 agent daemon.

All three are generated from the same in-memory `SuiteResult`
records; no duplicated formatting logic.
-/

namespace Tests

/-! ## In-memory test results -/

/-- Result of a single failed `check`.  Successful checks are
    counted but not individually stored — suites typically have
    tens of checks each. -/
structure CheckFailure where
  /-- Human-readable name passed to `check`. -/
  name     : String
  /-- `repr expected`, materialised at failure time. -/
  expected : String
  /-- `repr actual`, materialised at failure time. -/
  actual   : String
  deriving Inhabited, Repr

/-- Per-suite aggregate result. -/
structure SuiteResult where
  /-- Suite title passed to `suite`. -/
  title    : String
  /-- Count of `check` calls that matched. -/
  passes   : Nat
  /-- Count of `check` calls that mismatched. -/
  fails    : Nat
  /-- Structured failure details (one per mismatch). -/
  failures : Array CheckFailure
  /-- Wall-clock nanoseconds elapsed inside `suite`. -/
  elapsedNs : Nat
  /-- Set when the suite body threw.  Crashed suites are counted
      as one additional failure, the message rendered as the
      failure's `actual`. -/
  crashed  : Option String
  deriving Inhabited, Repr

/-- Aggregate result of a single benchmark invocation.  Phase 1
    records only a single sample; Phase 2 will extend to
    median/p95/p99. -/
structure BenchResult where
  name      : String
  elapsedNs : Nat
  deriving Inhabited, Repr

/-! ## Shared state

    Two cells are live during a `runSuites` call:
      * `currentSuiteRef` — the accumulator for the suite we're
        currently inside (`none` before any `suite` call starts).
      * `benchesRef`      — flat list of benchmark results.

    A pair of test-only cells (`totalPassesRef`, `totalFailsRef`)
    is kept for backwards-compat with callers using `Tests.totals`
    directly.  New code should consume `runSuites`' return value.
-/

private structure SuiteAccum where
  title    : String
  passes   : Nat
  fails    : Nat
  failures : Array CheckFailure

private initialize currentSuiteRef : IO.Ref (Option SuiteAccum) ←
  IO.mkRef none

private initialize benchesRef : IO.Ref (Array BenchResult) ←
  IO.mkRef #[]

/-- Monotone global counters, preserved for backwards-compat.
    The authoritative per-suite totals come from `SuiteResult`. -/
private initialize totalPassesRef : IO.Ref Nat ← IO.mkRef 0
private initialize totalFailsRef  : IO.Ref Nat ← IO.mkRef 0

/-- Verbose mode — when true, each passing check prints a line.
    Off by default to keep CI logs readable. -/
private initialize verboseRef : IO.Ref Bool ← IO.mkRef false

/-- Silent mode — suppresses stderr prints for `FAIL`, `CRASH`,
    and suite headers.  Used by the framework self-tests so the
    expected-failure demonstrations don't pollute the user's
    terminal. -/
private initialize silentRef : IO.Ref Bool ← IO.mkRef false

/-- Emit a "passed X" trace line for every successful check. -/
def setVerbose (enabled : Bool) : IO Unit := verboseRef.set enabled

/-- Scope `body` in silent mode: suite headers and FAIL/CRASH
    lines are suppressed.  Counts and structured results are
    preserved.  Restores the previous value on exit. -/
def withSilent (body : IO valueType) : IO valueType := do
  let prev ← silentRef.get
  silentRef.set true
  try
    body
  finally
    silentRef.set prev

/-- Record a pass against the current suite (or globally if no
    suite is active — that shouldn't happen in normal usage but
    we're defensive).  Silent mode still updates the per-suite
    accumulator (callers want the counts) but skips the global
    legacy counter and the verbose trace. -/
private def recordPass (name : String) : IO Unit := do
  let silent ← silentRef.get
  if not silent then totalPassesRef.modify (· + 1)
  if let some s ← currentSuiteRef.get then
    currentSuiteRef.set (some { s with passes := s.passes + 1 })
  if (← verboseRef.get) ∧ not silent then
    IO.println s!"  pass {name}"

/-- Record a structured failure against the current suite. -/
private def recordFailure (failure : CheckFailure) : IO Unit := do
  let silent ← silentRef.get
  if not silent then totalFailsRef.modify (· + 1)
  if let some s ← currentSuiteRef.get then
    currentSuiteRef.set
      (some { s with fails := s.fails + 1
                   , failures := s.failures.push failure })
  if not silent then
    IO.eprintln s!"  FAIL {failure.name}"
    IO.eprintln s!"    expected: {failure.expected}"
    IO.eprintln s!"    actual:   {failure.actual}"

/-! ## Primitive check combinators -/

/--
Compare two values with a user-supplied comparator and `Repr`.
On match, increment passes; on mismatch, record a structured
failure.  `repr expected` / `repr actual` are materialised
**only** on failure — this matters for heavy-to-print values.
-/
def checkWith {valueType : Type} [Repr valueType]
    (name : String) (comparator : valueType → valueType → Bool)
    (expected actual : valueType) : IO Unit := do
  if comparator expected actual then
    recordPass name
  else
    recordFailure
      { name     := name
      , expected := s!"{repr expected}"
      , actual   := s!"{repr actual}" }

/--
Compare two values with `DecidableEq` and `Repr`.  Defined in
terms of `checkWith` so improvements to failure formatting apply
uniformly.
-/
@[inline]
def check {valueType : Type} [DecidableEq valueType] [Repr valueType]
    (name : String) (expected actual : valueType) : IO Unit :=
  checkWith name (fun leftValue rightValue => decide (leftValue = rightValue))
    expected actual

/-- Boolean assertion — useful when `DecidableEq` on the value
    is heavy but a predicate can be checked. -/
def checkTrue (name : String) (actualBool : Bool) : IO Unit :=
  check name true actualBool

/-- Negated boolean assertion. -/
def checkFalse (name : String) (actualBool : Bool) : IO Unit :=
  check name false actualBool

/--
Fail the current suite unconditionally.  Useful inside
`match`/`if` arms where the surrounding structure means the
programmer reached an unexpected state.  Records a failure with
the given `name` and `note` as the `actual` string.
-/
def failWith (name : String) (note : String) : IO Unit :=
  recordFailure
    { name := name, expected := "<no mismatch>", actual := note }

/-! ## Suite combinator -/

/-- Record a benchmark result.  The body runs once; wall time is
    measured via `IO.monoNanosNow`.  Produces no pass/fail signal
    — benchmarks are observations, not assertions. -/
def bench (name : String) (body : IO Unit) : IO Unit := do
  let t0 ← IO.monoNanosNow
  try
    body
  catch e =>
    IO.eprintln s!"  bench {name} crashed: {e}"
  let t1 ← IO.monoNanosNow
  benchesRef.modify (·.push { name := name, elapsedNs := t1 - t0 })

/-- Read and clear accumulated benchmark results. -/
def drainBenches : IO (Array BenchResult) := do
  let benchResults ← benchesRef.get
  benchesRef.set #[]
  return benchResults

/--
Group a sequence of `check` calls under a named heading.  A fresh
per-suite accumulator is installed for the duration of `body`;
exceptions thrown inside are caught and surfaced as a crash
record so one bad suite cannot kill the whole runner.

If a suite is already active (i.e., `body` transitively calls
another `suite`), the nested call **reuses the existing
accumulator** rather than shadowing it.  Without this, the test
files' pattern — `def run : IO Unit := Tests.suite "Title" do …`
called from a runner-level `runSuite` wrapper — would lose every
check into a nested accumulator that gets discarded.  The nested
call still prints its header so CI logs read the same.
-/
def runSuite (title : String) (body : IO Unit) : IO SuiteResult := do
  let prev ← currentSuiteRef.get
  let nested := prev.isSome
  let silent ← silentRef.get
  if not nested then
    currentSuiteRef.set
      (some { title := title, passes := 0, fails := 0, failures := #[] })
  if not silent then
    IO.println s!"--- {title} ---"
  let t0 ← IO.monoNanosNow
  let crashMsg ← try
      body
      pure (none : Option String)
    catch caughtException =>
      let crashMessage := toString caughtException
      if not silent then
        IO.eprintln s!"  CRASH: suite body raised: {crashMessage}"
      -- Count the crash as one failure so exit code is nonzero.
      if not silent then totalFailsRef.modify (· + 1)
      if let some s ← currentSuiteRef.get then
        currentSuiteRef.set (some { s with fails := s.fails + 1 })
      pure (some crashMessage)
  let t1 ← IO.monoNanosNow
  -- Snapshot the accumulator before either restoring or leaving
  -- it in place.  In the top-level case we then clear it; in the
  -- nested case we leave it so the outer frame sees all counts.
  let accumulator ← currentSuiteRef.get
  if not nested then currentSuiteRef.set none
  let (p, f, fs) :=
    match accumulator with
    | some a => (a.passes, a.fails, a.failures)
    | none   => (0,        (if crashMsg.isSome then 1 else 0), #[])
  let result : SuiteResult :=
    { title     := title
    , passes    := p
    , fails     := f
    , failures  := fs
    , elapsedNs := t1 - t0
    , crashed   := crashMsg }
  return result

/--
Legacy entry point preserved so existing test files that call
`Tests.suite "..." do ...` keep compiling.  The result is
thrown away; use `runSuite` when the aggregated `SuiteResult`
is needed (e.g., from the runner).
-/
def suite (title : String) (body : IO Unit) : IO Unit := do
  let _ ← runSuite title body

/-! ## Totals — legacy API -/

/-- Read the session-wide pass/fail totals.  Preserved for
    `Tests.Main` and any external caller that pre-dated the
    per-suite API. -/
def totals : IO (Nat × Nat) := do
  let passCount ← totalPassesRef.get
  let failCount ← totalFailsRef.get
  return (passCount, failCount)

/-- Reset global counters.  Used by the meta-tests for the
    framework itself; production code must not call this. -/
def resetTotals : IO Unit := do
  totalPassesRef.set 0
  totalFailsRef.set 0
  benchesRef.set #[]
  currentSuiteRef.set none

/-! ## Runner + output formats -/

/-- Output format for the final summary. -/
inductive OutputFormat
  | human
  | tap
  | json
  deriving Inhabited, DecidableEq, Repr

/-- Runner configuration.  Populated from CLI args in
    `Tests.Main`. -/
structure RunConfig where
  /-- Restrict to suites whose title contains this substring.
      `none` means "run everything". -/
  filter  : Option String := none
  /-- Print a line per passing check. -/
  verbose : Bool := false
  /-- How to format the final summary.  Per-suite headers always
      print in human form because test bodies already `println`
      them. -/
  format  : OutputFormat := .human
  deriving Inhabited, Repr

/-- A suite wrapped for scheduling.  The runner needs both the
    title (for filtering) and the thunk (so filtered-out suites
    never even get executed). -/
structure SuiteEntry where
  title : String
  /-- The suite body.  The entry type intentionally does NOT
      include a `Tests.suite` wrapper — the thunk should call
      `Tests.suite` itself (or be pre-registered). -/
  run   : IO Unit
  deriving Inhabited

/-- Does the suite match the config filter?  The filter is a
    substring test: the suite runs iff its title contains the
    substring (or the filter is `none`, meaning "everything"). -/
def SuiteEntry.matchesFilter (entry : SuiteEntry) (runConfig : RunConfig) : Bool :=
  match runConfig.filter with
  | none              => true
  | some substring => decide ((entry.title.splitOn substring).length > 1)

/-- Run all entries matching the filter, returning one
    `SuiteResult` per suite that executed.

    Test files are expected to call `Tests.suite` internally, which
    maps to `runSuite` and prints its own header.  The runner
    wraps each entry in an outer accumulator frame so it can read
    per-entry pass/fail counts even though `Tests.suite` itself
    discards its `SuiteResult`.  The outer frame does not print —
    the inner `suite` already did — nor does it count the title
    twice: nested `runSuite` reuses the outer accumulator. -/
def runSuites (runConfig : RunConfig) (entries : Array SuiteEntry)
    : IO (Array SuiteResult) := do
  setVerbose runConfig.verbose
  let mut results : Array SuiteResult := #[]
  for e in entries do
    if e.matchesFilter runConfig then
      -- Install an outer accumulator silently, run the body (which
      -- invokes `Tests.suite` → `runSuite` with `nested := true`
      -- and reuses our accumulator), then harvest.
      let prev ← currentSuiteRef.get
      currentSuiteRef.set
        (some { title := e.title, passes := 0, fails := 0
              , failures := #[] })
      let t0 ← IO.monoNanosNow
      let crashMsg ← try
          e.run
          pure (none : Option String)
        catch caughtException =>
          let crashMessage := toString caughtException
          let silent ← silentRef.get
          if not silent then
            IO.eprintln s!"  CRASH: suite {e.title} raised: {crashMessage}"
          if not silent then totalFailsRef.modify (· + 1)
          if let some s ← currentSuiteRef.get then
            currentSuiteRef.set (some { s with fails := s.fails + 1 })
          pure (some crashMessage)
      let t1 ← IO.monoNanosNow
      let accumulator ← currentSuiteRef.get
      currentSuiteRef.set prev
      let (p, f, fs) := match accumulator with
        | some a => (a.passes, a.fails, a.failures)
        | none   => (0, (if crashMsg.isSome then 1 else 0), #[])
      results := results.push
        { title     := e.title
        , passes    := p
        , fails     := f
        , failures  := fs
        , elapsedNs := t1 - t0
        , crashed   := crashMsg }
  return results

/-! ## Summary formatters -/

private def fmtNs (nanoseconds : Nat) : String :=
  let microseconds := nanoseconds / 1000
  if microseconds < 1000 then s!"{microseconds}µs"
  else
    let milliseconds := microseconds / 1000
    if milliseconds < 10000 then s!"{milliseconds}ms"
    else s!"{milliseconds / 1000}s"

/-- JSON-escape a string.  Handles the minimal set (`"`, `\\`,
    control chars 0-31).  Not a general JSON library — enough for
    test names and repr strings. -/
private def jsonEscape (inputString : String) : String :=
  let escapedBody := inputString.foldl (init := "\"")
      fun outputSoFar nextChar =>
    match nextChar with
    | '"'  => outputSoFar ++ "\\\""
    | '\\' => outputSoFar ++ "\\\\"
    | '\n' => outputSoFar ++ "\\n"
    | '\r' => outputSoFar ++ "\\r"
    | '\t' => outputSoFar ++ "\\t"
    | literalChar    =>
      if literalChar.toNat < 32 then
        let hexDigits := String.ofList (Nat.toDigits 16 literalChar.toNat)
        let zeroPadded :=
          String.ofList (List.replicate (4 - hexDigits.length) '0') ++ hexDigits
        outputSoFar ++ "\\u" ++ zeroPadded
      else outputSoFar.push literalChar
  escapedBody ++ "\""

/-- Render the aggregate as human-readable text. -/
def renderHuman (results : Array SuiteResult) : String := Id.run do
  let mut output : String := ""
  let mut totalPasses : Nat := 0
  let mut totalFails : Nat := 0
  let mut totalElapsedNs : Nat := 0
  for suiteResult in results do
    totalPasses := totalPasses + suiteResult.passes
    totalFails := totalFails + suiteResult.fails
    totalElapsedNs := totalElapsedNs + suiteResult.elapsedNs
    let statusTag :=
      if suiteResult.fails = 0 ∧ suiteResult.crashed.isNone then "ok"
      else if suiteResult.crashed.isSome then "CRASH"
      else "FAIL"
    output := output ++
      s!"  [{statusTag}] {suiteResult.title} — {suiteResult.passes} passed, {suiteResult.fails} failed ({fmtNs suiteResult.elapsedNs})\n"
  output := output ++
    s!"=== totals: {totalPasses} passed, {totalFails} failed in {fmtNs totalElapsedNs} ===\n"
  return output

/-- Render as TAP v12.  Each suite becomes one TAP test; failures
    are listed in the YAML block beneath it. -/
def renderTap (results : Array SuiteResult) : String := Id.run do
  let mut output : String := s!"TAP version 13\n1..{results.size}\n"
  let mut testNumber : Nat := 0
  for suiteResult in results do
    testNumber := testNumber + 1
    let status :=
      if suiteResult.fails = 0 ∧ suiteResult.crashed.isNone then "ok"
      else "not ok"
    output := output ++ s!"{status} {testNumber} - {suiteResult.title}\n"
    if suiteResult.fails > 0 ∨ suiteResult.crashed.isSome then
      output := output ++ "  ---\n"
      output := output ++ s!"  passes: {suiteResult.passes}\n"
      output := output ++ s!"  fails:  {suiteResult.fails}\n"
      output := output ++ s!"  elapsed_ns: {suiteResult.elapsedNs}\n"
      if let some crashMessage := suiteResult.crashed then
        output := output ++ s!"  crash: \"{crashMessage}\"\n"
      if suiteResult.failures.size > 0 then
        output := output ++ "  failures:\n"
        for failure in suiteResult.failures do
          output := output ++ s!"    - name: \"{failure.name}\"\n"
      output := output ++ "  ...\n"
  return output

/-- Render as one JSON object per suite followed by a totals
    object on its own line.  Designed for the agent daemon
    (§24) — line-delimited JSON is trivial to stream-parse. -/
def renderJson (results : Array SuiteResult) : String := Id.run do
  let mut output : String := ""
  let mut totalPasses : Nat := 0
  let mut totalFails : Nat := 0
  let mut totalElapsedNs : Nat := 0
  for suiteResult in results do
    totalPasses := totalPasses + suiteResult.passes
    totalFails := totalFails + suiteResult.fails
    totalElapsedNs := totalElapsedNs + suiteResult.elapsedNs
    let mut failuresJson : String := "["
    let mut isFirstFailure : Bool := true
    for failure in suiteResult.failures do
      if not isFirstFailure then failuresJson := failuresJson ++ ","
      isFirstFailure := false
      failuresJson := failuresJson ++
        "{\"name\":" ++ jsonEscape failure.name ++
        ",\"expected\":" ++ jsonEscape failure.expected ++
        ",\"actual\":" ++ jsonEscape failure.actual ++ "}"
    failuresJson := failuresJson ++ "]"
    let crashJson := match suiteResult.crashed with
      | none               => "null"
      | some crashMessage  => jsonEscape crashMessage
    output := output ++
      "{\"type\":\"suite\"," ++
      "\"title\":" ++ jsonEscape suiteResult.title ++ "," ++
      s!"\"passes\":{suiteResult.passes},\"fails\":{suiteResult.fails}," ++
      s!"\"elapsed_ns\":{suiteResult.elapsedNs}," ++
      "\"crashed\":" ++ crashJson ++ "," ++
      "\"failures\":" ++ failuresJson ++
      "}\n"
  output := output ++
    "{\"type\":\"totals\"," ++
    s!"\"passes\":{totalPasses},\"fails\":{totalFails}," ++
    s!"\"elapsed_ns\":{totalElapsedNs},\"suites\":{results.size}" ++
    "}\n"
  return output

/-- Print the final summary in the configured format.  Returns
    `true` iff every suite passed (used for exit code). -/
def printSummary (runConfig : RunConfig) (results : Array SuiteResult)
    : IO Bool := do
  let renderedText := match runConfig.format with
    | .human => renderHuman results
    | .tap   => renderTap   results
    | .json  => renderJson  results
  IO.print renderedText
  let mut everyPassed := true
  for suiteResult in results do
    if suiteResult.fails > 0 ∨ suiteResult.crashed.isSome then
      everyPassed := false
  return everyPassed

end Tests
