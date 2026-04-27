import FX.Syntax.TokenStream
import Tests.Framework

/-!
# TokenStream combinator tests (task Q51)

Regression coverage for `manyWithProgress` and its derivatives
(`manyUntil`, `manyUntilKw`).  The combinator is the structural
fix for the EOF-infinite-loop trap that kernel-panicked the
workstation on 2026-04-24 during S10 testing — see
`project_parser_eof_trap.md` for the incident postmortem.

Three regression scenarios are pinned here.  Any future change
to the combinator that breaks one of these must add a ledger
entry explaining why the new behavior is preferable.

  * **EOF stop** — sub-parser advances forever, but combinator
    halts at the EOF terminator (lexer guarantee per
    `fx_lexer.md` §11).
  * **Predicate stop** — combinator halts when the supplied
    `shouldStop` matches the current token, leaving the cursor
    AT the terminator (caller consumes).
  * **No-progress bailout** — sub-parser reaches a state where
    it records errors but doesn't advance.  Combinator must
    halt instead of looping forever / accumulating an unbounded
    array.

A fourth scenario pins the keyword-terminator wrapper.
-/

namespace Tests.Syntax.TokenStreamTests

open Tests FX.Syntax FX.Util

/-- Wrap a token list (no spans, all `Span.zero`) into a
    `ParserState` ready for combinator testing.  Tests don't
    care about token positions — they care about cursor
    behavior and accumulator size. -/
def stateFromTokens (tokens : List Token) : ParserState :=
  let located : Array LocatedToken := tokens.toArray.map fun token =>
    { token := token, span := Span.zero }
  -- Lexer guarantees EOF; mirror that here so `peek` past the
  -- end behaves identically to a real stream.
  let withEof := located.push { token := Token.eof, span := Span.zero }
  { tokens := withEof }

/-- A toy sub-parser: consume one token and return its
    `repr`-format name.  This is the canonical "well-behaved"
    sub-parser — every call advances the cursor. -/
def parseOneAdvancing : ParserM String := do
  let consumed ← advance
  return s!"{repr consumed.token}"

/-- A toy sub-parser that does NOT advance.  Reproduces the
    bug pattern: error-recovery path emits a diagnostic via
    `recordError` and returns a placeholder without consuming.
    Any accumulating loop that calls this without a
    progress-check spins forever. -/
def parseOneStuck : ParserM String := do
  recordError "P099" "stuck sub-parser (regression witness)"
  return "<stuck>"

def run : IO Unit := Tests.suite "Tests.Syntax.TokenStreamTests" do

  /- ## Scenario 1 — EOF stop with default predicate.
     Stream of three idents.  `parseOneAdvancing` always
     consumes one token.  Loop should accumulate exactly 3
     elements and halt at EOF. -/
  let stream1 := stateFromTokens [
    Token.ident "alpha",
    Token.ident "beta",
    Token.ident "gamma"
  ]
  let (result1, finalState1) := (manyWithProgress parseOneAdvancing).run stream1
  check "scenario 1: accumulator size at EOF" 3 result1.size
  check "scenario 1: cursor at EOF token after loop"
    Token.eof finalState1.peek.token
  check "scenario 1: zero parse errors recorded" 0 finalState1.errors.size

  /- ## Scenario 2 — predicate stop on a specific token.
     Stream is `ident ident ; ident`.  Stop predicate matches
     `Token.semi`.  Loop should accumulate 2 elements and stop
     AT (not past) the `;`.  Caller must consume `;` itself —
     that's the documented contract. -/
  let stream2 := stateFromTokens [
    Token.ident "first",
    Token.ident "second",
    Token.semi,
    Token.ident "after_semi"
  ]
  let (result2, finalState2) :=
    (manyUntil Token.semi parseOneAdvancing).run stream2
  check "scenario 2: accumulator size before terminator" 2 result2.size
  check "scenario 2: cursor sits AT the terminator (not past)"
    Token.semi finalState2.peek.token

  /- ## Scenario 3 — no-progress bailout (THE regression).
     Stream of three idents.  Sub-parser doesn't advance.
     Without the progress check this loop would spin forever
     and grow the accumulator without bound (kernel panic from
     2026-04-24 reproduces here).  The combinator must halt
     after exactly zero pushed results — the no-progress
     element is not pushed because it represents a degenerate
     error AST. -/
  let stream3 := stateFromTokens [
    Token.ident "irrelevant1",
    Token.ident "irrelevant2",
    Token.ident "irrelevant3"
  ]
  let (result3, finalState3) :=
    (manyWithProgress parseOneStuck).run stream3
  check "scenario 3: bailout produces empty accumulator"
    0 result3.size
  check "scenario 3: cursor stays at the stuck position"
    (Token.ident "irrelevant1") finalState3.peek.token
  check "scenario 3: stuck sub-parser recorded its diagnostic"
    1 finalState3.errors.size

  /- ## Scenario 4 — `manyUntilKw` keyword-terminator wrapper.
     Stream is `ident ident "end" ident`.  Stop on the `end`
     keyword.  Verifies the keyword-aware variant matches the
     same shape as `manyUntil` for plain tokens. -/
  let stream4 := stateFromTokens [
    Token.ident "before",
    Token.ident "more_before",
    Token.kw Keyword.endKw,
    Token.ident "after_end"
  ]
  let (result4, finalState4) :=
    (manyUntilKw Keyword.endKw parseOneAdvancing).run stream4
  check "scenario 4: accumulator size before 'end' keyword"
    2 result4.size
  check "scenario 4: cursor sits AT the 'end' keyword"
    (Token.kw Keyword.endKw) finalState4.peek.token

  /- ## Scenario 5 — empty stream.
     Edge case: starting at EOF, the combinator must return an
     empty accumulator without even calling parseElement.  If
     parseElement were called, the stuck sub-parser would
     record an error — verify zero errors. -/
  let stream5 := stateFromTokens []
  let (result5, finalState5) :=
    (manyWithProgress parseOneStuck).run stream5
  check "scenario 5: empty stream produces empty accumulator"
    0 result5.size
  check "scenario 5: empty stream records no errors"
    0 finalState5.errors.size
  check "scenario 5: cursor at EOF in empty stream"
    Token.eof finalState5.peek.token

  /- ## Scenario 6 — mixed-progress with predicate stop.
     Compose advancing + stopping behaviors: stream is `ident
     ident ; ident`, stop on `;`, sub-parser advances.  The
     loop accumulates 2 elements and stops at `;` — same as
     scenario 2 but using the explicit `manyWithProgress` form
     to verify the surface API matches. -/
  let stream6 := stateFromTokens [
    Token.ident "explicit_first",
    Token.ident "explicit_second",
    Token.semi
  ]
  let (result6, _) :=
    (manyWithProgress parseOneAdvancing (· == Token.semi)).run stream6
  check "scenario 6: explicit form matches manyUntil"
    2 result6.size

end Tests.Syntax.TokenStreamTests
