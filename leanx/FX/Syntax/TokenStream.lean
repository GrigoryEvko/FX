import FX.Syntax.Token
import FX.Syntax.Ast
import FX.Util.Basic

/-!
# Token stream and parser monad

Cursor over `Array LocatedToken` with the operations a
recursive-descent parser needs:

  * **peek / next** — 1-token lookahead
  * **expect** — assert the next token is a specific kind
  * **error / recover** — structured error emission with
    panic-mode resynchronization
  * **mark / restore** — saved positions for backtracking
    (not used in the main grammar, available for contextual
    keyword disambiguation)

## Design

The parser is a `StateM` over `ParserState`, with errors
collected inline and partial ASTs returned even on failure.
No exceptions.  This matches the §24 compiler-agent protocol —
an agent wants *all* errors in one request, not one at a time.

The cursor position is a `Nat` index into the token array.
`peek` returns the current token without advancing; `next`
returns it and advances.  `isAtEnd` returns true when the
cursor is at or past the EOF token — the lexer guarantees an
EOF terminator so the cursor never reads past the end.

## Panic-mode recovery

On a syntax error, `resyncTo` scans forward until it finds one
of the supplied "synchronizing" tokens (typically `;` or a
decl-starter keyword) and leaves the cursor *at* that token (not
past it — the caller decides whether to consume).  This lets
the parser keep going after an error so later errors surface
in the same run.
-/

namespace FX.Syntax

open FX.Util

/-- Parser state: cursor position, the token array, and
    accumulated errors. -/
structure ParserState where
  tokens : Array LocatedToken
  pos    : Nat               := 0
  errors : Array Error       := #[]

namespace ParserState

/-- Current token.  Returns a synthetic `eof` token when past
    the end — the lexer already appends an `eof` terminator, so
    this path is only hit if the caller reads beyond it. -/
def peek (state : ParserState) : LocatedToken :=
  if hLt : state.pos < state.tokens.size then
    state.tokens[state.pos]
  else
    { token := Token.eof, span := Span.zero }

/-- Token `offset` positions ahead. -/
def peekAt (state : ParserState) (offset : Nat) : LocatedToken :=
  if hLt : state.pos + offset < state.tokens.size then
    state.tokens[state.pos + offset]
  else
    { token := Token.eof, span := Span.zero }

/-- True iff the cursor is at or past the EOF token. -/
def isAtEnd (state : ParserState) : Bool :=
  match state.peek.token with
  | Token.eof => true
  | _         => false

end ParserState

/-- The parser monad.  All parsing functions are `ParserM valueType`
    where `valueType` is the AST fragment they produce.  Failure is
    *not* exceptional — functions return a best-effort `valueType`
    value (often `Decl.unimplemented` / `Expr.unimplemented` /
    `Pattern.wildcard`) and record an error in the state. -/
abbrev ParserM := StateM ParserState

/-! ## Primitive cursor operations -/

/-- Advance past the current token and return it. -/
def advance : ParserM LocatedToken := do
  let state ← get
  let currentToken := state.peek
  if state.pos < state.tokens.size then
    set { state with pos := state.pos + 1 }
  return currentToken

/-- Peek without advancing. -/
def peek : ParserM Token := do
  let state ← get
  return state.peek.token

/-- Peek `offset` ahead without advancing. -/
def peekAt (offset : Nat) : ParserM Token := do
  let state ← get
  return (state.peekAt offset).token

/-- The span of the current token. -/
def peekSpan : ParserM Span := do
  let state ← get
  return state.peek.span

/-- Emit an error diagnostic rooted at the current token's span. -/
def recordError (code message : String) : ParserM Unit := do
  let state ← get
  let currentSpan := state.peek.span
  let errorRecord : Error :=
    { code := code
    , message := message
    , source := some ("<parse>", currentSpan.start.line, currentSpan.start.column) }
  set { state with errors := state.errors.push errorRecord }

/-- Check if the current token matches the given token pattern
    exactly.  Works for terminals and keyword kinds; for
    parameterized tokens (`ident`, `literal`, …) prefer the
    pattern-specific helpers below. -/
def peekIs (expected : Token) : ParserM Bool := do
  let current ← peek
  return (current == expected)

/-- Check if the current token is a specific keyword. -/
def peekIsKw (expected : Keyword) : ParserM Bool := do
  let current ← peek
  match current with
  | Token.kw found => return expected == found
  | _              => return false

/-- Consume the current token if it matches and return true;
    otherwise leave the cursor and return false. -/
def consume (expected : Token) : ParserM Bool := do
  if (← peekIs expected) then
    let _ ← advance
    return true
  else
    return false

/-- Consume a specific keyword. -/
def consumeKw (expected : Keyword) : ParserM Bool := do
  if (← peekIsKw expected) then
    let _ ← advance
    return true
  else
    return false

/--
Expect a specific token at the cursor.  On match: advance and
return the matched token.  On mismatch: record an error, do
*not* advance, and return the synthetic placeholder so the
caller can still build a best-effort AST.
-/
def expect (expected : Token) (context : String) : ParserM LocatedToken := do
  let state ← get
  let current := state.peek
  if current.token == expected then
    let _ ← advance
    return current
  else
    recordError "P001"
      s!"{context}: expected '{repr expected}', found '{repr current.token}'"
    return current

/-- Expect a specific keyword. -/
def expectKw (expected : Keyword) (context : String) : ParserM LocatedToken := do
  let state ← get
  let current := state.peek
  match current.token with
  | Token.kw found =>
    if expected == found then
      let _ ← advance
      return current
    else
      recordError "P001"
        s!"{context}: expected keyword '{expected.toString}', found keyword '{found.toString}'"
      return current
  | _ =>
    recordError "P001"
      s!"{context}: expected keyword '{expected.toString}', found '{repr current.token}'"
    return current

/-- Expect an `ident` token.  Returns the identifier string and
    its span; on mismatch, records an error and returns an
    empty-name placeholder. -/
def expectIdent (context : String) : ParserM (String × Span) := do
  let state ← get
  let current := state.peek
  match current.token with
  | Token.ident identName =>
    let _ ← advance
    return (identName, current.span)
  | _ =>
    recordError "P002"
      s!"{context}: expected identifier, found '{repr current.token}'"
    return ("_error", current.span)

/-- Expect a `uident` token (PascalCase).  Returns name + span. -/
def expectUIdent (context : String) : ParserM (String × Span) := do
  let state ← get
  let current := state.peek
  match current.token with
  | Token.uident identName =>
    let _ ← advance
    return (identName, current.span)
  | _ =>
    recordError "P002"
      s!"{context}: expected uppercase identifier, found '{repr current.token}'"
    return ("_Error", current.span)

/-! ## Panic-mode recovery -/

/-- Skip tokens until reaching one of the supplied terminals or
    EOF.  Leaves the cursor *at* the matched terminal (does not
    consume it) so the enclosing production can decide what to
    do.  Returns the number of tokens skipped. -/
partial def resyncTo (syncSet : Token → Bool) : ParserM Nat := do
  let rec loop (skipped : Nat) : ParserM Nat := do
    let current ← peek
    if current == Token.eof then return skipped
    if syncSet current then return skipped
    let _ ← advance
    loop (skipped + 1)
  loop 0

/-- Common sync set: statement/declaration terminators and the
    opening keywords of top-level declarations.  Returned as a
    function for use with `resyncTo`. -/
def topLevelSync : Token → Bool
  | Token.semi => true
  | Token.kw keyword =>
    match keyword with
    | Keyword.pubKw | Keyword.fnKw | Keyword.letKw | Keyword.constKw
    | Keyword.typeKw | Keyword.moduleKw | Keyword.openKw | Keyword.includeKw
    | Keyword.classKw | Keyword.instanceKw | Keyword.implKw
    | Keyword.effectKw | Keyword.machineKw | Keyword.contractKw
    | Keyword.testKw  | Keyword.benchKw
    | Keyword.axiomKw | Keyword.exceptionKw | Keyword.externKw
    | Keyword.valKw | Keyword.lemmaKw | Keyword.codataKw
    | Keyword.sessionKw | Keyword.quotientKw | Keyword.layoutKw
    | Keyword.dimensionKw | Keyword.taintClassKw
    | Keyword.refinementKw | Keyword.bisimulationKw
    | Keyword.decoratorKw => true
    | _ => false
  | _ => false

/-! ## Progress-checked accumulating loops (Q51)

Recursive-descent parsers that accumulate results into a list
have a foundational soundness obligation: they must terminate.
The `advance` primitive is a no-op at EOF (it returns the
current token but does NOT move the cursor), so any loop of
the shape

```
loop accumulator :=
  let element := parseSubThing
  if peek == terminator then return accumulator
  loop (accumulator.push element)
```

spins forever when `parseSubThing` reaches EOF inside an
error-recovery path that records an error WITHOUT advancing.
The unbounded `accumulator` array drives the process to OOM —
on 2026-04-24 this manifested as a kernel panic when the S10
session-decl parser hit a malformed conformance file.  See
`project_parser_eof_trap.md` for the incident postmortem.

`manyWithProgress` bakes both guards into a reusable
combinator: explicit EOF stop plus a position-progress check
on every iteration.  Use it for every accumulating loop that
calls a sub-parser; legacy inline loops should migrate per
task Q52.

`fx_design.md` §27 (`fx_reframing.md` §1.5 makes the
agent-readability case) requires every parser surface to be
robust against malformed input from agentic LLMs.  The
combinator turns "must remember to add EOF + progress checks"
from a per-loop discipline into a once-and-done structural
guarantee. -/

/-- General accumulating loop with a monadic stop predicate.
    Halts on EOF, on `shouldStopM` returning `true`, OR when
    `parseElement` returns without advancing the cursor (the
    no-progress bailout — sub-parser already recorded its own
    diagnostic via `recordError`, so we don't push the
    degenerate result).

    The monadic predicate has full ParserM access — it can
    call `peek`, `peekAt`, or any other cursor query, which is
    what loops with multi-token disambiguation need (e.g.,
    distinguishing `end ;` from `end session ;`).

    The non-monadic `manyWithProgress` is a wrapper around this
    for the common single-token-predicate case. -/
partial def manyWithProgressM {valueType : Type}
    (parseElement : ParserM valueType)
    (shouldStopM : ParserM Bool)
    : ParserM (Array valueType) := do
  let rec loop (collected : Array valueType) : ParserM (Array valueType) := do
    if (← peek) == Token.eof then
      return collected
    if (← shouldStopM) then
      return collected
    let posBeforeParse := (← get).pos
    let parsedElement ← parseElement
    let posAfterParse := (← get).pos
    if posAfterParse == posBeforeParse then
      -- No-progress bailout (see module docstring).
      return collected
    loop (collected.push parsedElement)
  loop #[]

/-- Accumulate results from `parseElement` until either:

    * the current token equals `Token.eof` (the lexer always
      appends EOF, so this is the terminal case), OR
    * `shouldStop` returns `true` for the current token, OR
    * `parseElement` returns without advancing the cursor (the
      no-progress bailout — `parseElement` already recorded its
      own diagnostic via `recordError`, so we don't push a
      degenerate result).

    Default `shouldStop` is "never stop on a token" — combine
    with EOF stop for "consume the rest of the stream".  For
    multi-token disambiguation use `manyWithProgressM` with a
    monadic predicate that calls `peekAt`. -/
partial def manyWithProgress {valueType : Type}
    (parseElement : ParserM valueType)
    (shouldStop : Token → Bool := fun _ => false)
    : ParserM (Array valueType) :=
  manyWithProgressM parseElement do
    return shouldStop (← peek)

/-- Common case: accumulate until a specific terminator token
    is reached.  Equivalent to
    `manyWithProgress parseElement (· == terminator)`.  Does
    NOT consume the terminator — the caller is responsible
    (typically via `expect`). -/
partial def manyUntil {valueType : Type}
    (terminator : Token) (parseElement : ParserM valueType)
    : ParserM (Array valueType) :=
  manyWithProgress parseElement (· == terminator)

/-- Accumulate until a specific keyword is reached.  See
    `manyWithProgress` / `manyUntil`. -/
partial def manyUntilKw {valueType : Type}
    (terminator : Keyword) (parseElement : ParserM valueType)
    : ParserM (Array valueType) :=
  manyWithProgress parseElement fun token =>
    match token with
    | Token.kw keyword => keyword == terminator
    | _                => false

end FX.Syntax
