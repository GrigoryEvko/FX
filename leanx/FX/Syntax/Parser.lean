import FX.Syntax.TokenStream

/-!
# Parser — recursive descent over `Array LocatedToken`

Implements `fx_grammar.md` §4–§6 at the Phase-1 subset.  Entry
point: `parseFile : Array LocatedToken → Ast.File × Array Error`.

## What parses

**Declarations** (§5):
  * `module qualident ;`
  * `open qualident (as Upper)? ;`
  * `include qualident ;`
  * `const NAME : type = expr ;`
  * `[pub] fn name (params) : ret = expr ;`
  * `[pub] fn name (params) : ret begin fn stmt* return expr ; end fn ;`
  * `sorry ;`

All other decl forms listed in §5 are *recognized* by their
opening keyword and swallowed to the next top-level token,
emitting a `Decl.unimplemented` placeholder with a note.

**Expressions**: atomic (var, qualident, literal, unit,
paren-grouping, block, if, lambda, sorry), postfix
(application, field, index).  Precedence chain for binary
operators is a Phase-1.1 follow-up — Phase 1 stops at postfix.

**Patterns**: wildcard, var, ctor, literal, tuple.

## Error policy

All errors are recorded in the `ParserState.errors` array via
`recordError` and the parser keeps going via panic-mode resync.
No exceptions.

## Error-code reference

The parser emits the following codes.  All are in the `Pxxx`
parser-diagnostic range of the `fx_design.md` §10.10 taxonomy,
with one exception: `T050` is a `Txxx` type-level diagnostic
(chained comparison is a type-grammar rule in `fx_grammar.md`
§3 and surfaces as a type error rather than a parse error).

* `P001` — `expect`/`expectKw` mismatch (wrong token / wrong
  keyword at an expected position).  Emitted by `expect`,
  `expectKw`; see `FX/Syntax/TokenStream.lean`.
* `P002` — `expectIdent` / `expectUIdent` mismatch.  Emitted by
  `expectIdent`, `expectUIdent`.
* `P003` — qualident lookup expected a bare identifier after a
  `Module.` prefix and saw something else.  Emitted by
  `parseQualIdent`.
* `P005` — `const` name is missing / not an identifier.
* `P010` — `parseAtom` saw a non-expression-starting token.
* `P020` — `parseLamParam` saw an unsupported lambda-parameter
  form (Phase-1 limitation).
* `P030` — `parsePattern` saw a non-pattern-starting token.
* `P035` — type-parameter list separator expected `,` or `>`, saw
  something else.  Emitted by `typeParamsLoop`.
* `P036` — type-parameter kind expected (`type` or identifier),
  saw something else.  Emitted by `parseTypeParamKind`.
* `P040` — `parseFnBody` saw neither `=` nor `begin fn`.
* `P100` — `parseDecl` saw a token that starts no declaration.
* `T050` — chained comparison (`a < b < c`).  Surfaced here
  rather than at elaboration because the parser already has the
  full expression context and the grammar rule is syntactic.

## Error-recovery policy

Two helpers advance the parser state on a mismatched token:

  * `expect` / `expectKw` / `expectIdent` / `expectUIdent` — used
    for **required** tokens where failure means the structural
    shape was missed.  These record `P001`/`P002` and continue
    without consuming — subsequent productions may re-emit errors
    at the same position.  Use this whenever a grammar rule says
    "this specific token MUST appear here."
  * `recordError` followed by `advance` — used for **informational**
    diagnostics where the parser still has a sensible continuation
    (e.g., `parseAtom` saw a non-expression token; skip it and
    try the next one).  Emits `P010`/`P020`/`P030`/`P035`/`P036`/
    `P100` depending on the site.  Use this whenever the rule is
    open-ended enough that advancing makes progress toward a
    valid parse of the REST of the file.

Never mix the two at a single site — pick based on whether the
rule is "this token must be X" (use `expect`) or "this token
should be one of {A, B, C}" (use `recordError + advance` after
exhausting matches).

Panic-mode resync via `swallowToSync` is used at the top-level
decl boundary: when `parseDecl` records `P100`, subsequent
tokens are swallowed until a recognizable decl-start keyword
appears.  Bounded blast radius — one malformed decl shouldn't
prevent the rest of the file from parsing.  Tested in
`Tests/Syntax/ParserTests`.

## Accumulating-loop safety audit (task Q52)

The EOF infinite-loop trap (memory entry
`project_parser_eof_trap.md`) kernel-panicked the workstation
on 2026-04-24 during S10 testing.  Root cause: `advance` is a
no-op at EOF, so any recursive accumulating loop whose sub-
parser has a "record error, no advance" catch-all path grows
its accumulator unboundedly → OOM.  Q51 landed the
`manyWithProgress` / `manyWithProgressM` combinators in
`FX/Syntax/TokenStream.lean` to bake the EOF+progress guards
into one reusable helper.

This block audits every accumulating loop in Parser.lean and
classifies its safety story.  Three shapes appear:

### A. Precedence-climbing (trivially safe — NOT accumulators)

`additiveLoop`, `multiplicativeLoop`, `postfixLoop`.  Each is
left-recursive on a single `lhs` / `currentHead`, NOT building
an unbounded array.  Recursion requires a specific operator
token; no operator → stop immediately.  No OOM path exists.

### B. Separator-terminated accumulators (safe via sub-parser advance)

`callArgsLoop`, `parseRecordLiteralFieldsLoop`,
`ctorPatternArgsLoop`, `tuplePatternLoop`, `lamParamsLoop`,
`attrExprsLoop`, `fnParamsLoop`, `typeParamsLoop`,
`ctorFieldsLoop`, `recordFieldsLoop`, `blockFnStmtsLoop`,
`parseStmtsThenTailLoop`, `parseLocalFnParamsLoop`,
`parseAttrsLoop`.

Shape: loop calls sub-parser, pushes result, recurses iff the
next token is the expected separator (`,` / `;`).  Termination
argument: the separator is consumed inside the loop, and the
sub-parser ALWAYS advances — every sub-parser called from these
loops has a catch-all arm that calls `advance` to make progress
(see `parseAtom` line ~370, `parsePattern` line ~815,
`parseCtorField` line ~1405, `parseFnParam`, `parseOneTypeParam`).
A missing separator ends the loop cleanly (the `| _ => pure acc`
arm).  Reaching EOF inside the loop causes the peek to return
`Token.eof`, which doesn't match the separator, and the loop
returns.

**Maintenance obligation**: every sub-parser called inside one
of these loops MUST advance the cursor on every code path,
including error-recovery catch-alls.  Violating this breaks the
implicit termination proof.  Future edits that add a sub-parser
whose catch-all records an error without advancing will OOM the
enclosing loop on malformed input.  See §C for the explicit
guards pattern if you need to add such a sub-parser.

### C. End-terminated accumulators (safe via sub-parser advance + `end` stop)

`parseMatchArms`, `variantCtorsLoop`, `implMembersLoop`.

Shape: loop calls sub-parser, recurses unconditionally, stops
when peeked token is `Token.kw Keyword.endKw`.  No explicit EOF
check — relies on sub-parser to never be called at EOF because
the enclosing `match ... end match` grammar forces the `end`
keyword to appear.  Sub-parser advance discipline same as §B.

**Known concern**: if the lexer emits EOF before `end` (e.g.,
truncated input from an agent), these loops depend on the
sub-parser's catch-all to advance past EOF — but advance at EOF
is a no-op.  In practice parseMatchArm / parseVariantCtor /
parseImplMember each start with either `expectIdent`/
`expectKw` (which doesn't advance on mismatch but records
P002/P001) or with a catch-all parseExpr (which DOES advance).
Truncated-at-EOF input still terminates via grade-error
cascade, but the audit trail is fragile; adding an explicit
`Token.eof => pure acc` arm to each of these would harden them.

### D. Explicit EOF+progress guards (S10 retrofit; already safe)

`stepsLoop`, `parseSessionBranchArms`.  Both have the full
three-guard pattern inlined: EOF stop, stop-predicate, position-
progress check.  These are the canonical templates for any new
accumulating loop.  Q51's `manyWithProgress` encodes the same
discipline as a reusable combinator for future loops.

### E. Top-level decl loop

`declsLoop`: terminates on `parserState.isAtEnd` (Token.eof).
`parseDecl`'s catch-all calls `swallowToSync` which skips to a
decl-start or EOF — guaranteed progress.  Safe.

### Why existing Q51 combinator migration was deferred

Attempting to rewrite `parseSessionSteps` / `parseSessionBranchArms`
to call `manyWithProgressM` / `manyUntilKw` with `parseSessionStep`
/ `parseSessionBranchArm` as arguments broke Lean 4's mutual-
block compilation — passing a sibling `partial def` as a first-
class value to a higher-order combinator confuses the recursive
compilation.  The S10 inline form is retained here; future
migrations to the Q51 combinator require either (a) all
candidates to live in the same module as `manyWithProgress`
(not the case here — combinators are in `TokenStream.lean`,
parsers in `Parser.lean`) or (b) a non-`partial` refactor
strategy.  For now: inline-plus-document is the policy.

## Regression test

`Tests/Syntax/ParserRobustnessTests.lean` runs a suite of
deliberately-malformed inputs through `parseFile` and verifies
every call terminates.  Specifically: truncated session decls,
truncated ADT decls, truncated match blocks, truncated impl
blocks, unterminated strings, and a "garbage everywhere" fuzz
that mixes every category.  A Lean `partial def` cannot hang
deterministically, but the test provides a bounded expectation
of errors — any future edit that lets a loop run forever would
produce a test-runner timeout rather than an OOM.
-/

namespace FX.Syntax.Parser

open FX.Syntax
open FX.Syntax.Ast

/-! ## Helpers -/

/-- Parse a qualified identifier: zero-or-more `UIDENT .` prefix
    then one final `ident` or `UIDENT`.  On empty/malformed input,
    records an error and returns a `_error` stub. -/
partial def parseQualIdent : ParserM QualIdent := do
  let startSpan ← peekSpan
  let rec loop (parts : Array String) : ParserM (Array String × String × Span) := do
    let currentToken ← peek
    let span ← peekSpan
    match currentToken with
    | Token.uident name =>
      let _ ← advance
      let next ← peek
      match next with
      | Token.dot =>
        let _ ← advance
        loop (parts.push name)
      | _ => pure (parts, name, span)
    | Token.ident name =>
      let _ ← advance
      pure (parts, name, span)
    | _ =>
      recordError "P003" s!"expected identifier, found '{repr currentToken}'"
      pure (parts, "_error", span)
  let (parts, final, finalSpan) ← loop #[]
  pure { parts := parts, final := final
       , span := Span.merge startSpan finalSpan }

/-- Swallow tokens until a top-level sync point, consuming the
    terminating `;` if present. -/
partial def swallowToSync : ParserM Span := do
  let startSpan ← peekSpan
  let _ ← resyncTo topLevelSync
  let stopSpan ← peekSpan
  let _ ← consume Token.semi
  pure (Span.merge startSpan stopSpan)

/-! ## Expressions, patterns, statements (mutual) -/

mutual

/--
Parse a complete expression.  Phase-1 subset of
`fx_grammar.md` §3: implements

  * `<==>` iff (Q67, outermost, non-chained)
  * `==>` implies (Q67, below iff, right-associative)
  * `|>` pipe (Q62, below implies, left-associative)
  * `->` function type arrow (level 1, right-associative)
  * `or` (Q63, below arrow, left-associative)
  * `and` (Q63, below or, left-associative)
  * comparison (level 8)
  * `is` (Q66, below compare, non-chained)
  * additive (level 15), multiplicative (level 16)
  * prefix `-` / `~` / `not` (Q63, first-class AST node)
  * postfix application / field / index

Deferred: bitwise, shift, range.  Adding those is a phase-2
refinement since they're rare in Phase-1-targeted programs.
-/
partial def parseExpr : ParserM Expr :=
  parseIff

/-- §2.6 propositional iff `<==>`.  Non-chained — `a <==> b
    <==> c` has no standard reading (iff is associative
    under extensional equality but users writing it chained
    usually mean a typo).  We accept exactly one `<==>`
    per expression and emit P042 on a second occurrence.
    Lowest precedence in the expression grammar so the
    whole sides compose cleanly.  Q67. -/
partial def parseIff : ParserM Expr := do
  let startSpan ← peekSpan
  let lhs ← parseImplies
  let currentToken ← peek
  match currentToken with
  | Token.iff =>
    let _ ← advance
    let rhs ← parseImplies
    let afterRhs ← peek
    match afterRhs with
    | Token.iff =>
      recordError "P042"
        "chained `<==>` operator — parenthesize explicitly: `(a <==> b) <==> c`"
    | _ => pure ()
    let stopSpan ← peekSpan
    pure (Expr.logicalIff lhs rhs (Span.merge startSpan stopSpan))
  | _ => pure lhs

/-- §2.6 propositional implies `==>`.  Right-associative —
    `a ==> b ==> c` parses as `a ==> (b ==> c)` matching the
    classical convention.  Binds tighter than `<==>` and
    looser than `|>`.  Q67. -/
partial def parseImplies : ParserM Expr := do
  let startSpan ← peekSpan
  let lhs ← parsePipe
  let currentToken ← peek
  match currentToken with
  | Token.implies =>
    let _ ← advance
    -- Right-recursion for right-associativity: the rhs is
    -- itself an `implies` expression, not `parsePipe`.
    let rhs ← parseImplies
    let stopSpan ← peekSpan
    pure (Expr.logicalImplies lhs rhs (Span.merge startSpan stopSpan))
  | _ => pure lhs

/--
Pipe `|>` — §4.2.  Left-associative, LOWER precedence than
arrow: `a |> f -> Nat` parses as `a |> (f -> Nat)`, and
`a |> b |> c` parses as `(a |> b) |> c`.

Emits the dedicated `Expr.pipe` AST node.  The lhs→positional
rewrite happens in `Elab/Elaborate.lean` so that:

  * diagnostics can cite the pipe position by name (e.g.
    "pipe RHS must be a callable expression") instead of
    surfacing the bare-application error a synthesized
    `Expr.app` would trigger;
  * pretty-printers and future tooling can round-trip the
    `|>` keyword rather than reconstructing it from a
    reordered-positional call.

Q62. -/
partial def parsePipe : ParserM Expr := do
  let startSpan ← peekSpan
  let lhs ← parseArrow
  pipeLoop startSpan lhs

/-- Accumulating left-associative loop for pipe. -/
partial def pipeLoop (startSpan : Span) (lhs : Expr) : ParserM Expr := do
  let currentToken ← peek
  match currentToken with
  | Token.pipeRight =>
    let _ ← advance
    let rhs ← parseArrow
    let stopSpan ← peekSpan
    let fullSpan := Span.merge startSpan stopSpan
    pipeLoop startSpan (Expr.pipe lhs rhs fullSpan)
  | _ => pure lhs

/--
Level 1 function-type arrow `T -> U`, right-associative.
Appears in both type positions (`fn(x: T) : U -> V = …`) and
value positions (constructing function types as values).
Since types and expressions share grammar, we handle it here.

Q63: arrow's LHS routes through `parseOr` so logical
operators bind tighter than `->` — `a or b -> c` parses as
`(a or b) -> c`. -/
partial def parseArrow : ParserM Expr := do
  let startSpan ← peekSpan
  let lhs ← parseOr
  let currentToken ← peek
  match currentToken with
  | Token.arrow =>
    let _ ← advance
    let rhs ← parseArrow    -- right-recursion for right-assoc
    let stopSpan ← peekSpan
    pure (Expr.arrow lhs rhs (Span.merge startSpan stopSpan))
  | _ => pure lhs

/-- §2.6 logical `or`, left-associative.  Emits the dedicated
    `Expr.logicalOr` AST node; elaboration happens in
    `FX/Elab/Elaborate.lean`.  Source structure is preserved
    through to tooling + diagnostics rather than being lost to
    parse-time `if-then-else` desugaring.  Q63. -/
partial def parseOr : ParserM Expr := do
  let startSpan ← peekSpan
  let lhs ← parseAnd
  orLoop startSpan lhs

/-- Accumulating left-assoc loop for `or`. -/
partial def orLoop (startSpan : Span) (lhs : Expr) : ParserM Expr := do
  let currentToken ← peek
  match currentToken with
  | Token.kw Keyword.orKw =>
    let _ ← advance
    let rhs ← parseAnd
    let stopSpan ← peekSpan
    let combinedSpan := Span.merge startSpan stopSpan
    orLoop startSpan (Expr.logicalOr lhs rhs combinedSpan)
  | _ => pure lhs

/-- §2.6 logical `and`, left-associative.  Binds tighter than
    `or` so `a and b or c` parses as `(a and b) or c`.  Emits
    `Expr.logicalAnd`.  Q63. -/
partial def parseAnd : ParserM Expr := do
  let startSpan ← peekSpan
  let lhs ← parseCompare
  andLoop startSpan lhs

/-- Accumulating left-assoc loop for `and`. -/
partial def andLoop (startSpan : Span) (lhs : Expr) : ParserM Expr := do
  let currentToken ← peek
  match currentToken with
  | Token.kw Keyword.andKw =>
    let _ ← advance
    let rhs ← parseCompare
    let stopSpan ← peekSpan
    let combinedSpan := Span.merge startSpan stopSpan
    andLoop startSpan (Expr.logicalAnd lhs rhs combinedSpan)
  | _ => pure lhs

/--
Level 8 comparison.  Per `fx_grammar.md` §3, comparison is
NON-CHAINING: `0 < x < 10` is rejected.  We enforce this by
trying a comparison at most once.
-/
partial def parseCompare : ParserM Expr := do
  let startSpan ← peekSpan
  let lhs ← parseIsCheck
  let currentToken ← peek
  match currentToken with
  | Token.eqEq | Token.neq | Token.lt | Token.gt | Token.leq | Token.geq =>
    let operator := currentToken
    let _ ← advance
    let rhs ← parseIsCheck
    -- Check for chained comparison (T050 per fx_grammar.md §3).
    let next ← peek
    match next with
    | Token.eqEq | Token.neq | Token.lt | Token.gt | Token.leq | Token.geq =>
      recordError "T050"
        "chained comparison — write 'a < b and b < c' instead"
    | _ => pure ()
    let stopSpan ← peekSpan
    pure (Expr.binop operator lhs rhs (Span.merge startSpan stopSpan))
  | _ => pure lhs

/-- §2.6 constructor-test `EXPR is CTOR_REF`.  Binds tighter
    than `==`/`!=`/`<`/`>`/`<=`/`>=` and looser than `+`/`-`,
    so `x + 1 is Succ` parses as `(x + 1) is Succ` and
    `x is Some == true` parses as `(x is Some) == true`.
    Non-chained — `x is A is B` is a spec-absurd form (the
    result of the first `is` is Bool, and `is B` would
    require B to be a Bool constructor, producing the same
    Bool either way), so we emit a P-code when it appears.
    Q66. -/
partial def parseIsCheck : ParserM Expr := do
  let startSpan ← peekSpan
  let lhs ← parseAdditive
  let currentToken ← peek
  match currentToken with
  | Token.kw Keyword.isKw =>
    let _ ← advance
    let ctorRef ← parseQualIdent
    let stopSpan ← peekSpan
    -- Reject a second chained `is` with the same rationale
    -- as T050 on comparison: the double-test has no sensible
    -- reading and is almost certainly a typo.
    let afterCtor ← peek
    match afterCtor with
    | Token.kw Keyword.isKw =>
      recordError "P041"
        "chained `is` operator — `x is A is B` has no defined meaning; split into `and`-combined tests"
    | _ => pure ()
    pure (Expr.isCheck lhs ctorRef (Span.merge startSpan stopSpan))
  | _ => pure lhs

/-- Level 15 additive: `+` / `-`, left-associative. -/
partial def parseAdditive : ParserM Expr := do
  let lhs ← parseMultiplicative
  additiveLoop lhs

/-- Accumulating left-associative loop for additive. -/
partial def additiveLoop (lhs : Expr) : ParserM Expr := do
  let currentToken ← peek
  match currentToken with
  | Token.plus | Token.minus =>
    let startSpan ← peekSpan
    let operator := currentToken
    let _ ← advance
    let rhs ← parseMultiplicative
    let stopSpan ← peekSpan
    additiveLoop (Expr.binop operator lhs rhs (Span.merge startSpan stopSpan))
  | _ => pure lhs

/-- Level 16 multiplicative: `*` / `/` / `%`, left-associative. -/
partial def parseMultiplicative : ParserM Expr := do
  let lhs ← parsePrefix
  multiplicativeLoop lhs

/-- Accumulating loop for multiplicative. -/
partial def multiplicativeLoop (lhs : Expr) : ParserM Expr := do
  let currentToken ← peek
  match currentToken with
  | Token.star | Token.slash | Token.percent =>
    let startSpan ← peekSpan
    let operator := currentToken
    let _ ← advance
    let rhs ← parsePrefix
    let stopSpan ← peekSpan
    multiplicativeLoop (Expr.binop operator lhs rhs (Span.merge startSpan stopSpan))
  | _ => pure lhs

/-- Prefix operators: `-` arithmetic negate, `~` bitwise NOT,
    and `try` control-flow-effect propagator (§4.9, task E-3).

    `try` binds at the prefix level so `try f(x)` parses as
    `(try f(x))` and `try f(x) + 1` parses as `(try f(x)) + 1`.
    Semantically that's fine: the caller marks the propagation
    point at the Fail-effecting call, and arithmetic on the
    result is downstream of it.

    Right-associative — `--x` parses as `-(- x)`, `try try f()`
    parses as `try (try f())` (semantically redundant, but
    legal grammar). -/
partial def parsePrefix : ParserM Expr := do
  let currentToken ← peek
  match currentToken with
  | Token.minus | Token.tilde =>
    let startSpan ← peekSpan
    let operator := currentToken
    let _ ← advance
    let rhs ← parsePrefix
    let stopSpan ← peekSpan
    pure (Expr.prefix_ operator rhs (Span.merge startSpan stopSpan))
  | Token.kw Keyword.tryKw =>
    let startSpan ← peekSpan
    let _ ← advance
    let body ← parsePrefix
    let stopSpan ← peekSpan
    pure (Expr.tryPrefix body (Span.merge startSpan stopSpan))
  | Token.kw Keyword.notKw =>
    -- §2.6 logical negation.  Emits the dedicated
    -- `Expr.logicalNot` AST node so source structure survives
    -- through to elab (and future tooling / diagnostics that
    -- want to refer to the `not` keyword directly).  Q63.
    let startSpan ← peekSpan
    let _ ← advance
    let body ← parsePrefix
    let stopSpan ← peekSpan
    let combinedSpan := Span.merge startSpan stopSpan
    pure (Expr.logicalNot body combinedSpan)
  | _ => parsePostfix

/-- Postfix chain: application `e(args)`, field access `e.name`,
    indexing `e[i]`.  Built on top of `parseAtom`. -/
partial def parsePostfix : ParserM Expr := do
  let head ← parseAtom
  postfixLoop head

/-- Continuation of the postfix chain. -/
partial def postfixLoop (currentHead : Expr) : ParserM Expr := do
  let currentToken ← peek
  match currentToken with
  | Token.lparen =>
    let startSpan ← peekSpan
    let _ ← advance
    let args ← parseCallArgs
    let _ ← expect Token.rparen "call arguments"
    let stopSpan ← peekSpan
    postfixLoop (Expr.app currentHead args (Span.merge startSpan stopSpan))
  | Token.dotProj =>
    let _ ← advance
    let (name, nameSpan) ← expectIdent "field access"
    postfixLoop (Expr.field currentHead name nameSpan)
  | Token.lbrack =>
    let startSpan ← peekSpan
    let _ ← advance
    let indexExpr ← parseExpr
    let _ ← expect Token.rbrack "index"
    let stopSpan ← peekSpan
    postfixLoop (Expr.index currentHead indexExpr (Span.merge startSpan stopSpan))
  | Token.lbrace =>
    -- B8 record literal sugar: `TypeName { field: v, field: v, }`
    -- desugars to `TypeName(field: v, field: v)` — a ctor call
    -- with all-named args.  The elaborator reorders by the ctor's
    -- declared `argNames` (Inductive.IndCtor.argNames) to
    -- positional form.  Enabled only after an atomic expression
    -- (so `begin ... { ... } ... end` in code position isn't
    -- misinterpreted as a record literal).
    let startSpan ← peekSpan
    let _ ← advance
    let fields ← parseRecordLiteralFields
    let _ ← expect Token.rbrace "record literal closer"
    let stopSpan ← peekSpan
    postfixLoop (Expr.app currentHead fields (Span.merge startSpan stopSpan))
  | _ => pure currentHead

/-- Parse a record-literal's field-init list `field: v, field: v`.
    Each field is a `.named CallArg` so the elaborator's ctor
    named-arg reordering (§B8) maps them to positional slots. -/
partial def parseRecordLiteralFields : ParserM (Array CallArg) := do
  let currentToken ← peek
  match currentToken with
  | Token.rbrace => pure #[]
  | _ => parseRecordLiteralFieldsLoop #[]

partial def parseRecordLiteralFieldsLoop (acc : Array CallArg)
    : ParserM (Array CallArg) := do
  let (fieldName, _) ← expectIdent "record literal field name"
  let _ ← expect Token.colon "record literal field type separator"
  let fieldValue ← parseExpr
  let acc := acc.push (CallArg.named fieldName fieldValue)
  let followingToken ← peek
  match followingToken with
  | Token.comma => do
    let _ ← advance
    -- Trailing comma tolerated — if `}` follows the comma, stop.
    let afterCommaToken ← peek
    match afterCommaToken with
    | Token.rbrace => pure acc
    | _            => parseRecordLiteralFieldsLoop acc
  | _ => pure acc

/-- Parse a list-literal body `a, b, c` (caller has consumed
    the opening `[`).  Returns when the next token is `]`.
    Trailing comma tolerated.  Q71. -/
partial def listLiteralItems : ParserM (Array Expr) := do
  let currentToken ← peek
  match currentToken with
  | Token.rbrack => pure #[]
  | _ => listLiteralItemsLoop #[]

partial def listLiteralItemsLoop (acc : Array Expr) : ParserM (Array Expr) := do
  let itemExpr ← parseExpr
  let acc := acc.push itemExpr
  let followingToken ← peek
  match followingToken with
  | Token.comma => do
    let _ ← advance
    let afterCommaToken ← peek
    match afterCommaToken with
    | Token.rbrack => pure acc
    | _            => listLiteralItemsLoop acc
  | _ => pure acc

/-- Parse an atomic expression: variable, literal, grouping,
    block, if, lambda, sorry, unit.

    Literal tokens are dispatched through `Token.isLiteralAtom`
    — see that predicate for the full literal inventory and the
    rationale for a single named test over a ~14-arm pattern
    alternation.  `type` lives in the literal set because FX's
    unified expression/type grammar treats it as the universe-
    literal atom elaborating to `Term.type .zero`. -/
partial def parseAtom : ParserM Expr := do
  let currentToken ← peek
  let span ← peekSpan
  if currentToken.isLiteralAtom then
    let _ ← advance
    return Expr.literal currentToken span
  match currentToken with
  | Token.ident _ | Token.uident _ =>
    let qualIdent ← parseQualIdent
    pure (Expr.var qualIdent)
  | Token.lparen =>
    let _ ← advance
    let next ← peek
    match next with
    | Token.rparen =>
      let _ ← advance
      pure (Expr.unit span)
    | _ =>
      let innerExpr ← parseExpr
      let _ ← expect Token.rparen "parenthesized expression"
      pure innerExpr
  | Token.kw Keyword.sorryKw =>
    let _ ← advance
    pure (Expr.sorryExpr span)
  | Token.kw Keyword.ifKw =>
    parseIfExpr
  | Token.kw Keyword.matchKw =>
    parseMatchExpr
  | Token.kw Keyword.handleKw =>
    parseHandleExpr
  | Token.kw Keyword.beginKw =>
    parseBlockExpr
  | Token.kw Keyword.fnKw =>
    parseLambda
  | Token.kw Keyword.forKw =>
    parseForExpr
  | Token.kw Keyword.whileKw =>
    parseWhileExpr
  | Token.dotProj =>
    -- §4.2 dot-shorthand: `.field` without a receiver desugars
    -- to `fn(it) => it.field`.  The elaborator handles the
    -- semantic side (requires an expected Pi); parser just
    -- captures the field name and span.  Q61.
    let _ ← advance
    let (fieldName, fieldSpan) ← expectIdent "dot-shorthand field name"
    pure (Expr.dotShorthand fieldName (Span.merge span fieldSpan))
  | Token.lbrack =>
    -- §3.7 list literal `[a, b, c]`.  At atom position `[`
    -- introduces a list; postfix `[`→ index (parsePostfix).
    -- Trailing comma tolerated.  Q71.
    let _ ← advance
    let items ← listLiteralItems
    let _ ← expect Token.rbrack "list literal closer"
    let stopSpan ← peekSpan
    pure (Expr.listLit items (Span.merge span stopSpan))
  | _ =>
    recordError "P010" s!"expected expression, found '{repr currentToken}'"
    let _ ← advance   -- skip to make progress
    pure (Expr.unimplemented s!"unexpected {repr currentToken}" span)

/-- Parse a call-argument list starting at the first argument
    (caller has already consumed the opening `(`).  Returns when
    the next token is `)`. -/
partial def parseCallArgs : ParserM (Array CallArg) := do
  let currentToken ← peek
  match currentToken with
  | Token.rparen => pure #[]
  | _ => callArgsLoop #[]

/-- Accumulating loop for `parseCallArgs`. -/
partial def callArgsLoop (argsSoFar : Array CallArg)
    : ParserM (Array CallArg) := do
  let nextCallArg ← parseOneCallArg
  let argsSoFar := argsSoFar.push nextCallArg
  let followingToken ← peek
  match followingToken with
  | Token.comma =>
    let _ ← advance
    callArgsLoop argsSoFar
  | _ => pure argsSoFar

/-- Parse one call argument: positional, `name: val`, or `#val`. -/
partial def parseOneCallArg : ParserM CallArg := do
  let currentToken ← peek
  match currentToken with
  | Token.hash =>
    let _ ← advance
    let implicitArg ← parseExpr
    pure (CallArg.implicit implicitArg)
  | Token.ident name =>
    let followingToken ← peekAt 1
    match followingToken with
    | Token.colon =>
      let _ ← advance    -- consume name
      let _ ← advance    -- consume :
      let namedArg ← parseExpr
      pure (CallArg.named name namedArg)
    | _ =>
      let positionalArg ← parseExpr
      pure (CallArg.pos positionalArg)
  | _ =>
    let positionalArg ← parseExpr
    pure (CallArg.pos positionalArg)

/-- Parse `if cond; then_ (else if … ;)* (else body)? end if`. -/
partial def parseIfExpr : ParserM Expr := do
  let startSpan ← peekSpan
  let _ ← expectKw Keyword.ifKw "if expression"
  let cond ← parseExpr
  let _ ← expect Token.semi "if condition"
  let thenBranch ← parseExpr
  let (elseIfs, elseBranch) ← parseElseChain
  let _ ← expectKw Keyword.endKw "end of if"
  let _ ← expectKw Keyword.ifKw "end if closer"
  let stopSpan ← peekSpan
  pure (Expr.ifExpr cond thenBranch elseIfs elseBranch
    (Span.merge startSpan stopSpan))

/-- Accumulating helper for `parseIfExpr`'s else-chain. -/
partial def parseElseChain : ParserM (Array (Expr × Expr) × Option Expr) := do
  let currentToken ← peek
  match currentToken with
  | Token.elif =>
    let _ ← advance
    let elifCond ← parseExpr
    let _ ← expect Token.semi "else-if condition"
    let elifBranch ← parseExpr
    let (remainingElseIfs, finalElse) ← parseElseChain
    pure (#[(elifCond, elifBranch)] ++ remainingElseIfs, finalElse)
  | Token.kw Keyword.elseKw =>
    let _ ← advance
    let elseBranch ← parseExpr
    pure (#[], some elseBranch)
  | _ => pure (#[], none)

/-- Parse `match scrutinee ; arm+ end match` per `fx_grammar.md` §6.5.
    Each arm ends with `;`; the arm list ends at `end match`. -/
partial def parseMatchExpr : ParserM Expr := do
  let startSpan ← peekSpan
  let _ ← expectKw Keyword.matchKw "match expression"
  let scrutinee ← parseExpr
  let _ ← expect Token.semi "match scrutinee terminator"
  let arms ← parseMatchArms #[]
  let _ ← expectKw Keyword.endKw "end of match"
  let _ ← expectKw Keyword.matchKw "end match closer"
  let stopSpan ← peekSpan
  pure (Expr.match_ scrutinee arms (Span.merge startSpan stopSpan))

/-- Accumulating loop for match arms.  Peeks for `end` (closer) or
    EOF (truncation) to decide whether another arm is coming.  Every
    arm is terminated by its own `;`; the match as a whole is closed
    by `end match`.  Q52: includes explicit EOF stop AND a
    position-progress check — without the progress check, truncated
    input where `parseMatchArm` reaches EOF inside a sub-parser
    whose catch-all `advance` is a no-op would spin forever. -/
partial def parseMatchArms (armsSoFar : Array MatchArm)
    : ParserM (Array MatchArm) := do
  let currentToken ← peek
  match currentToken with
  | Token.kw Keyword.endKw => pure armsSoFar
  | Token.eof              => pure armsSoFar
  | _ =>
    let posBefore := (← get).pos
    let nextArm ← parseMatchArm
    let posAfter := (← get).pos
    if posAfter == posBefore then
      pure (armsSoFar.push nextArm)
    else
      parseMatchArms (armsSoFar.push nextArm)

/-- Parse one match arm: `pattern (if guard)? => body ;`. -/
partial def parseMatchArm : ParserM MatchArm := do
  let startSpan ← peekSpan
  let armPattern ← parsePattern
  let followingToken ← peek
  let armGuard ← match followingToken with
    | Token.kw Keyword.ifKw => do
      let _ ← advance
      let guardExpr ← parseExpr
      pure (some guardExpr)
    | _ => pure none
  let _ ← expect Token.fatArrow "match arm body"
  let armBody ← parseExpr
  let _ ← expect Token.semi "match arm terminator"
  let stopSpan ← peekSpan
  pure (MatchArm.mk armPattern armGuard armBody (Span.merge startSpan stopSpan))

/-- Parse `handle EXPR (return NAME => EXPR;)? op_arm+ end handle`
    per `fx_design.md` §9.6 (task E-5, parser half).

    The body expression is parsed first, then an optional
    `return NAME => EXPR;` clause, then one or more operation
    arms `OP_NAME(params) => EXPR;` until `end handle`.

    Reuses `parseLamParamsOrEmpty` for the per-arm parameter
    list — operation handlers bind plain or typed names for the
    operation's arguments plus a final continuation parameter by
    convention.  The parser does NOT enforce "at least one arm"
    syntactically; a zero-arm handler is a grammatical quirk the
    elaborator rejects (deferred to full E-5). -/
partial def parseHandleExpr : ParserM Expr := do
  let startSpan ← peekSpan
  let _ ← expectKw Keyword.handleKw "handle expression"
  let body ← parseExpr
  -- Optional `return NAME => EXPR ;` clause.  Peek for `return`
  -- after the body; if present, parse the identity-transform
  -- shape the handler uses to lift the body's result.
  let returnClauseOpt ← do
    let peekedTok ← peek
    match peekedTok with
    | Token.kw Keyword.returnKw => do
      let _ ← advance
      let (returnName, _) ← expectIdent "return-clause binder"
      let _ ← expect Token.fatArrow "return-clause arrow"
      let returnBody ← parseExpr
      let _ ← expect Token.semi "return-clause terminator"
      pure (some (returnName, returnBody))
    | _ => pure none
  let arms ← parseHandleOpArms #[]
  let _ ← expectKw Keyword.endKw "end of handle"
  let _ ← expectKw Keyword.handleKw "end handle closer"
  let stopSpan ← peekSpan
  pure (Expr.handleExpr body returnClauseOpt arms (Span.merge startSpan stopSpan))

/-- Accumulating loop for handler operation arms.  Same shape
    as `parseMatchArms` — peeks for `end` (closer) or EOF
    (truncation) and includes a position-progress check per
    Q52 to prevent spins on truncated input. -/
partial def parseHandleOpArms (armsSoFar : Array HandleOpArm)
    : ParserM (Array HandleOpArm) := do
  let currentToken ← peek
  match currentToken with
  | Token.kw Keyword.endKw => pure armsSoFar
  | Token.eof              => pure armsSoFar
  | _ =>
    let posBefore := (← get).pos
    let nextArm ← parseHandleOpArm
    let posAfter := (← get).pos
    if posAfter == posBefore then
      pure (armsSoFar.push nextArm)
    else
      parseHandleOpArms (armsSoFar.push nextArm)

/-- Parse one operation arm: `OP_NAME(params) => body ;`.  The
    parameter list reuses the lambda-parameter parser so plain,
    typed, and wildcard binders compose identically. -/
partial def parseHandleOpArm : ParserM HandleOpArm := do
  let startSpan ← peekSpan
  let (opName, _) ← expectIdent "handler operation name"
  let _ ← expect Token.lparen "handler operation parameters"
  let params ← parseLamParamsOrEmpty
  let _ ← expect Token.fatArrow "handler operation arrow"
  let armBody ← parseExpr
  let _ ← expect Token.semi "handler operation terminator"
  let stopSpan ← peekSpan
  pure (HandleOpArm.mk opName params armBody (Span.merge startSpan stopSpan))

/-- Parse a `begin … end begin` block expression. -/
partial def parseBlockExpr : ParserM Expr := do
  let startSpan ← peekSpan
  let _ ← expectKw Keyword.beginKw "block expression"
  let (stmts, tail) ← parseStmtsThenTail
  let _ ← expectKw Keyword.endKw "end of block"
  let _ ← expectKw Keyword.beginKw "end begin closer"
  let stopSpan ← peekSpan
  pure (Expr.block stmts tail (Span.merge startSpan stopSpan))

/-- B10 — parse `for LOOPVAR in LO..HI; BODY end for` per
    `fx_design.md` §4.5.  Exclusive-range only in this phase;
    `..=` (`rangeIncl`) will be added alongside non-zero `lo`
    support once Nat arithmetic is available at elab time.

    Grammar:

        for_expr := "for" IDENT "in" expr ".." expr ";" expr
                    "end" "for"

    The elaborator enforces `lo = 0` (literal) and `body : Unit`
    as v1 restrictions.  Parser just captures shape. -/
partial def parseForExpr : ParserM Expr := do
  let startSpan ← peekSpan
  let _ ← expectKw Keyword.forKw "for expression"
  let loopVar ← do
    let identToken ← peek
    match identToken with
    | Token.ident loopVarName =>
      let _ ← advance
      pure loopVarName
    | _ =>
      recordError "P011"
        s!"expected loop variable after 'for', found '{repr identToken}'"
      pure "_loopVar_recover"
  let _ ← expectKw Keyword.inKw "loop variable terminator"
  let loExpr ← parseExpr
  let rangeTok ← peek
  match rangeTok with
  | Token.range => do
    let _ ← advance
  | Token.rangeIncl =>
    recordError "P012"
      "inclusive range '..=' not yet supported in for-loops (use exclusive '..' with hi + 1)"
    let _ ← advance
  | _ =>
    recordError "P012"
      s!"expected range operator '..' after 'for' lower bound, found '{repr rangeTok}'"
  let hiExpr ← parseExpr
  let _ ← expect Token.semi "for-range header terminator"
  let bodyExpr ← parseExpr
  let _ ← expectKw Keyword.endKw "end of for"
  let _ ← expectKw Keyword.forKw "end for closer"
  let stopSpan ← peekSpan
  pure (Expr.forRange loopVar loExpr hiExpr bodyExpr
    (Span.merge startSpan stopSpan))

/-- B10 — parse `while COND; BODY end while` per `fx_design.md`
    §4.5.  Parse-only in this phase; the elaborator rejects with
    code E013 pending `with Div` + termination plumbing (tasks
    E-3, E-6).

    Grammar:

        while_expr := "while" expr ";" expr "end" "while"
-/
partial def parseWhileExpr : ParserM Expr := do
  let startSpan ← peekSpan
  let _ ← expectKw Keyword.whileKw "while expression"
  let condExpr ← parseExpr
  let _ ← expect Token.semi "while condition terminator"
  let bodyExpr ← parseExpr
  let _ ← expectKw Keyword.endKw "end of while"
  let _ ← expectKw Keyword.whileKw "end while closer"
  let stopSpan ← peekSpan
  pure (Expr.whileLoop condExpr bodyExpr
    (Span.merge startSpan stopSpan))

/-- Parse zero-or-more statements then a tail expression
    terminated by `;`.  Used by block expressions. -/
partial def parseStmtsThenTail : ParserM (Array Stmt × Expr) :=
  parseStmtsThenTailLoop #[]

/-- E-7 §4.7 rule 18 — parse one local fn declaration statement.
    The `fn` keyword has NOT yet been consumed when this is
    called — we peek for it, consume, then parse the subset of
    surface fn syntax permitted for local fns: `fn NAME(params):
    retType = expr;`.  Returns `some Stmt.fnStmt` on success,
    `none` when recovery skipped past the local fn (error
    already recorded via recordError).

    Phase-2 restrictions (enforced at parse time): no type
    parameters, no `with` effects, no spec clauses, one-liner
    body only.  Rule 18 is enforced SYNTACTICALLY — absent
    surface `with`, effect row is `Tot` and cannot inherit from
    the enclosing fn.  Users wanting effect-carrying helpers
    hoist to top-level fn decls where the full surface applies
    (including spec clauses, type params, block bodies).

    Parsed inline rather than via `parseFnDecl` because this
    stmt-parser lives in the first parser mutual block and
    `parseFnDecl` lives in the second — Lean 4's `partial def`
    doesn't support cross-mutual forward references. -/
partial def parseLocalFnStmt : ParserM (Option Stmt) := do
  let startSpan ← peekSpan
  let _ ← advance  -- consume `fn`
  let (fnName, _) ← expectIdent "local function name"
  let _ ← expect Token.lparen "local fn parameter list opener"
  let fnParams ← parseLocalFnParamsLoop #[]
  let _ ← expect Token.colon "local fn return-type colon"
  let fnRetType ← parseExpr
  -- Reject `with` / spec clauses with a clear hoist suggestion.
  let headTok ← peek
  match headTok with
  | Token.kw Keyword.withKw => do
    recordError "P050"
      "local fn cannot carry 'with' effects — hoist to a top-level fn (§4.7 rule 18)"
    let _ ← swallowToSync
    pure none
  | Token.kw Keyword.preKw | Token.kw Keyword.postKw
  | Token.kw Keyword.decreasesKw | Token.kw Keyword.whereKw => do
    recordError "P050"
      "local fn cannot carry pre/post/decreases/where — hoist to a top-level fn (§4.7 rule 18)"
    let _ ← swallowToSync
    pure none
  | _ => do
    let _ ← expect Token.equals "local fn one-liner body"
    let bodyExpr ← parseExpr
    let _ ← expect Token.semi "local fn statement terminator"
    let stopSpan ← peekSpan
    let fnBody := FnBody.oneLiner bodyExpr
    pure (some (Stmt.fnStmt fnName fnParams fnRetType #[] #[] fnBody
      (Span.merge startSpan stopSpan)))

/-- Minimal fn-param parser for local fns in block position
    (E-7).  Parses `(p: T, p: T)` — the closing `)` is consumed.
    Rejects mode prefixes (`own`/`ref`/`ref mut`/`affine`/`ghost`)
    with P051 so local fns stay textually simple — users needing
    mode-annotated parameters hoist to top-level fn decls where
    `parseFnParams` handles the full surface.  `parseFnParams`
    proper lives in the second parser mutual block and can't be
    forward-referenced from here (§4.7 rule 18 commentary in
    parseStmtsThenTailLoop). -/
partial def parseLocalFnParamsLoop (acc : Array FnParam)
    : ParserM (Array FnParam) := do
  let nextTok ← peek
  match nextTok with
  | Token.rparen =>
    let _ ← advance
    pure acc
  | Token.kw Keyword.ownKw | Token.kw Keyword.refKw
  | Token.kw Keyword.affineKw | Token.kw Keyword.ghostKw => do
    recordError "P051"
      "local fn parameter mode prefixes not supported — hoist to a top-level fn"
    let _ ← swallowToSync
    pure acc
  | _ => do
    let paramStart ← peekSpan
    let (paramName, _) ← expectIdent "local fn parameter name"
    let _ ← expect Token.colon "local fn parameter type colon"
    let paramType ← parseExpr
    let paramStop ← peekSpan
    let param := FnParam.mk ParamMode.default_ paramName paramType
      (Span.merge paramStart paramStop)
    let followTok ← peek
    match followTok with
    | Token.comma =>
      let _ ← advance
      parseLocalFnParamsLoop (acc.push param)
    | Token.rparen =>
      let _ ← advance
      pure (acc.push param)
    | _ => do
      recordError "P052"
        "local fn parameters: expected ',' or ')' after param"
      let _ ← swallowToSync
      pure (acc.push param)

/-- Accumulating helper for `parseStmtsThenTail`. -/
partial def parseStmtsThenTailLoop (stmtsSoFar : Array Stmt)
    : ParserM (Array Stmt × Expr) := do
  let currentToken ← peek
  match currentToken with
  | Token.kw Keyword.letKw =>
    let letStmt ← parseLetStmt
    parseStmtsThenTailLoop (stmtsSoFar.push letStmt)
  | Token.kw Keyword.fnKw => do
    let stmt? ← parseLocalFnStmt
    match stmt? with
    | some fnStmt => parseStmtsThenTailLoop (stmtsSoFar.push fnStmt)
    | none        => parseStmtsThenTailLoop stmtsSoFar
  | _ =>
    let tailExpr ← parseExpr
    let _ ← expect Token.semi "block tail expression terminator"
    pure (stmtsSoFar, tailExpr)

/-- Parse `let pat (: type)? = expr ;`. -/
partial def parseLetStmt : ParserM Stmt := do
  let startSpan ← peekSpan
  let _ ← expectKw Keyword.letKw "let statement"
  let boundPattern ← parsePattern
  let typeAnnotation ← parseOptionalAscription
  let _ ← expect Token.equals "let binding"
  let boundValue ← parseExpr
  let _ ← expect Token.semi "let statement terminator"
  let stopSpan ← peekSpan
  pure (Stmt.letStmt boundPattern typeAnnotation boundValue
    (Span.merge startSpan stopSpan))

/-- Parse an optional `: type` ascription.  Returns `none` if no
    colon is present. -/
partial def parseOptionalAscription : ParserM (Option Expr) := do
  let currentToken ← peek
  match currentToken with
  | Token.colon =>
    let _ ← advance
    let typeExpr ← parseExpr
    pure (some typeExpr)
  | _ => pure none

/-- Parse a lambda: `fn (p1, p2) => body`. -/
partial def parseLambda : ParserM Expr := do
  let startSpan ← peekSpan
  let _ ← expectKw Keyword.fnKw "lambda"
  let _ ← expect Token.lparen "lambda parameters"
  let params ← parseLamParamsOrEmpty
  let _ ← expect Token.fatArrow "lambda arrow"
  let body ← parseExpr
  let stopSpan ← peekSpan
  pure (Expr.lam params body (Span.merge startSpan stopSpan))

/-- Parse an optionally-empty lambda parameter list, consuming
    the closing `)`. -/
partial def parseLamParamsOrEmpty : ParserM (Array LamParam) := do
  let currentToken ← peek
  match currentToken with
  | Token.rparen =>
    let _ ← advance
    pure #[]
  | _ =>
    let lamParams ← lamParamsLoop #[]
    let _ ← expect Token.rparen "end of lambda parameters"
    pure lamParams

/-- Accumulating loop for lambda parameters. -/
partial def lamParamsLoop (paramsSoFar : Array LamParam)
    : ParserM (Array LamParam) := do
  let nextParam ← parseLamParam
  let paramsSoFar := paramsSoFar.push nextParam
  let followingToken ← peek
  match followingToken with
  | Token.comma =>
    let _ ← advance
    lamParamsLoop paramsSoFar
  | _ => pure paramsSoFar

/-- Parse one lambda parameter.  Supports four shapes per
    `fx_grammar.md` §6.5:
      * `lower_ident ":" type` — typed binder
      * `lower_ident`          — plain binder (needs expected Pi)
      * `"_"`                  — wildcard (needs expected Pi)
      * `"(" pattern ")"`      — destructuring (B11, §4.5)
    `_` is a plain identifier at the token level so we detect
    it by name before emitting the plain binder. -/
partial def parseLamParam : ParserM LamParam := do
  let currentToken ← peek
  match currentToken with
  | Token.ident name =>
    let _ ← advance
    if name == "_" then
      pure LamParam.wildcard
    else
      let followingToken ← peek
      match followingToken with
      | Token.colon =>
        let _ ← advance
        let typeExpr ← parseExpr
        pure (LamParam.typed name typeExpr)
      | _ => pure (LamParam.plain name)
  | Token.lparen =>
    -- Destructuring parameter: `"(" pattern ")"`.  Delegate to
    -- `parsePattern` which consumes the open paren itself and
    -- dispatches to `parseTupleOrGroupPattern` — that handles
    -- both tuple syntax `(a, b)` and grouped single patterns
    -- `(foo)` uniformly.  Not consuming the open paren here
    -- avoids a double-consume.
    let destructurePattern ← parsePattern
    pure (LamParam.destructure destructurePattern)
  | _ =>
    recordError "P020" s!"unsupported lambda-parameter form '{repr currentToken}'"
    let _ ← advance
    pure LamParam.wildcard

/-- Parse a pattern.  Per `fx_grammar.md` §8:

      Pattern   = OrPattern
      OrPattern = AsPattern ("|" AsPattern)*
      AsPattern = BasePattern ("as" IDENT)?

    Top-level parse: first an `AsPattern` (handled by
    `parsePatternAs`), then any number of `| AsPattern` alternatives
    wrapped into a single `Pattern.orPattern`.  A single-alternative
    pattern returns the inner pattern unwrapped — or-pattern nodes
    always carry 2+ alternatives.  Nested `parsePattern` calls (ctor
    args, tuple items, ascribed wrappers) inherit or-pattern support:
    `Succ(A | B)` parses as `Succ(orPattern [A, B])` ready for N5
    deep expansion. -/
partial def parsePattern : ParserM Pattern := do
  let firstAlt ← parsePatternAs
  let firstSpan ← peekSpan  -- end-of-first-alt approximation
  let alternatives ← orPatternLoop #[firstAlt]
  if alternatives.size == 1 then
    pure firstAlt
  else
    let endSpan ← peekSpan
    pure (Pattern.orPattern alternatives (Span.merge firstSpan endSpan))

/-- Accumulating loop for `parsePattern`'s or-branch collection.
    While the next token is `|`, consume it and parse another
    `parsePatternAs`, appending to the alternatives array.  Stops
    on any non-`|` token.  No EOF-progress trap (Q52): each
    iteration consumes exactly one `|` token plus at least one
    pattern-starting token via `parsePatternAs`. -/
partial def orPatternLoop (altsSoFar : Array Pattern) : ParserM (Array Pattern) := do
  let nextTok ← peek
  match nextTok with
  | Token.pipe =>
    let _ ← advance
    let nextAlt ← parsePatternAs
    orPatternLoop (altsSoFar.push nextAlt)
  | _ => pure altsSoFar

/-- Parse an as-pattern: a base pattern optionally followed by
    `as IDENT`.  Per `fx_grammar.md` §8 rule
    `AsPattern = BasePattern ("as" IDENT)?`.  `as` binds tighter
    than `|` — so `A | B as n` parses as `A | (B as n)`; to name
    the whole or-group, use `(A | B) as n` with explicit parens. -/
partial def parsePatternAs : ParserM Pattern := do
  let basePattern ← parsePatternBase
  let currentToken ← peek
  match currentToken with
  | Token.kw Keyword.asKw =>
    let _ ← advance
    let nextToken ← peek
    let span ← peekSpan
    match nextToken with
    | Token.ident asName =>
      let _ ← advance
      if asName == "_" then
        recordError "P031" "`as` binding name must be a plain identifier, not `_`"
        pure basePattern
      else
        pure (Pattern.asPattern basePattern asName (Span.merge span span))
    | _ =>
      recordError "P031" s!"expected identifier after `as`, found '{repr nextToken}'"
      pure basePattern
  | _ => pure basePattern

/-- Parse the base (non-`as`) form of a pattern.  Split out of
    `parsePattern` so the `as IDENT` postfix attaches at exactly
    one place — parse-level nesting into ctor args recurses via
    `parsePattern`, giving `as` support at every pattern level. -/
partial def parsePatternBase : ParserM Pattern := do
  let currentToken ← peek
  let span ← peekSpan
  match currentToken with
  | Token.ident name =>
    let _ ← advance
    if name == "_" then pure (Pattern.wildcard span)
    else pure (Pattern.var name span)
  | Token.uident _ =>
    let qualIdent ← parseQualIdent
    let next ← peek
    match next with
    | Token.lparen =>
      let _ ← advance
      let args ← parseCtorPatternArgs
      pure (Pattern.ctor qualIdent args (Span.merge span qualIdent.span))
    | _ =>
      pure (Pattern.ctor qualIdent #[] span)
  | Token.intLit _ _ | Token.typedInt _ _ _
  | Token.decimalLit _ | Token.stringLit _
  | Token.kw Keyword.trueKw | Token.kw Keyword.falseKw =>
    let _ ← advance
    pure (Pattern.literal currentToken span)
  | Token.lparen =>
    let _ ← advance
    parseTupleOrGroupPattern span
  | _ =>
    recordError "P030" s!"expected pattern, found '{repr currentToken}'"
    let _ ← advance
    pure (Pattern.wildcard span)

/-- Parse constructor-application arguments after the opening
    `(`, consuming the closing `)`. -/
partial def parseCtorPatternArgs : ParserM (Array Pattern) := do
  let currentToken ← peek
  match currentToken with
  | Token.rparen =>
    let _ ← advance
    pure #[]
  | _ =>
    let args ← ctorPatternArgsLoop #[]
    let _ ← expect Token.rparen "end of constructor pattern"
    pure args

/-- Accumulating loop for `parseCtorPatternArgs`. -/
partial def ctorPatternArgsLoop (argsSoFar : Array Pattern)
    : ParserM (Array Pattern) := do
  let nextPattern ← parsePattern
  let argsSoFar := argsSoFar.push nextPattern
  let followingToken ← peek
  match followingToken with
  | Token.comma =>
    let _ ← advance
    ctorPatternArgsLoop argsSoFar
  | _ => pure argsSoFar

/-- After consuming `(`, parse either a single pat (grouping) or
    a tuple pattern.  Consumes the closing `)`. -/
partial def parseTupleOrGroupPattern (startSpan : Span) : ParserM Pattern := do
  let currentToken ← peek
  match currentToken with
  | Token.rparen =>
    let _ ← advance
    pure (Pattern.tuple #[] startSpan)
  | _ =>
    let items ← tuplePatternLoop #[]
    let _ ← expect Token.rparen "end of tuple pattern"
    if items.size == 1 then
      pure items[0]!
    else
      pure (Pattern.tuple items startSpan)

/-- Accumulating loop for tuple pattern items. -/
partial def tuplePatternLoop (itemsSoFar : Array Pattern)
    : ParserM (Array Pattern) := do
  let nextPattern ← parsePattern
  let itemsSoFar := itemsSoFar.push nextPattern
  let followingToken ← peek
  match followingToken with
  | Token.comma =>
    let _ ← advance
    tuplePatternLoop itemsSoFar
  | _ => pure itemsSoFar

end  -- mutual

/-! ## Top-level declaration helpers

All declarations below are wrapped in a second `mutual` block so
they can reference each other freely.  They may also reference
anything from the earlier expression/pattern mutual block (now
fully defined). -/

mutual

/-- Parse zero-or-more `@[attr]` attribute blocks. -/
partial def parseAttrs : ParserM (Array Expr) :=
  parseAttrsLoop #[]

/-- Accumulating loop for `parseAttrs`. -/
partial def parseAttrsLoop (accumulator : Array Expr) : ParserM (Array Expr) := do
  let currentToken ← peek
  match currentToken with
  | Token.atLbrack =>
    let _ ← advance
    let accumulator ← attrExprsLoop accumulator
    let _ ← expect Token.rbrack "end of attribute list"
    parseAttrsLoop accumulator
  | _ => pure accumulator

/-- Accumulating loop for individual `@[e1, e2, …]` items. -/
partial def attrExprsLoop (attrsSoFar : Array Expr)
    : ParserM (Array Expr) := do
  let nextAttrExpr ← parseExpr
  let attrsSoFar := attrsSoFar.push nextAttrExpr
  let followingToken ← peek
  match followingToken with
  | Token.comma =>
    let _ ← advance
    attrExprsLoop attrsSoFar
  | _ => pure attrsSoFar

/-- Consume optional `pub`. -/
partial def parseVisibility : ParserM Visibility := do
  if (← consumeKw Keyword.pubKw) then
    pure Visibility.public_
  else
    pure Visibility.private_

/-- `module qualident ;` -/
partial def parseModuleDecl : ParserM Decl := do
  let startSpan ← peekSpan
  let _ ← expectKw Keyword.moduleKw "module declaration"
  let path ← parseQualIdent
  let _ ← expect Token.semi "module declaration terminator"
  let stopSpan ← peekSpan
  pure (Decl.moduleDecl path (Span.merge startSpan stopSpan))

/-- `open qualident (as Upper)? ;` -/
partial def parseOpenDecl : ParserM Decl := do
  let startSpan ← peekSpan
  let _ ← expectKw Keyword.openKw "open declaration"
  let path ← parseQualIdent
  let alias_ ← parseOpenAlias
  let _ ← expect Token.semi "open declaration terminator"
  let stopSpan ← peekSpan
  pure (Decl.openDecl path alias_ (Span.merge startSpan stopSpan))

/-- Optional `as UpperIdent` clause for `open`. -/
partial def parseOpenAlias : ParserM (Option String) := do
  if (← consumeKw Keyword.asKw) then
    let (n, _) ← expectUIdent "open-as alias"
    pure (some n)
  else
    pure none

/-- `include qualident ;` -/
partial def parseIncludeDecl : ParserM Decl := do
  let startSpan ← peekSpan
  let _ ← expectKw Keyword.includeKw "include declaration"
  let path ← parseQualIdent
  let _ ← expect Token.semi "include declaration terminator"
  let stopSpan ← peekSpan
  pure (Decl.includeDecl path (Span.merge startSpan stopSpan))

/-- `val NAME : type ;` — forward declaration without a body
    (grammar §5.10).  In Phase-2 the symbol is registered with a
    placeholder body; callers that actually invoke it fail at
    eval time.  Type parameters (`val f<a: type> : …`) parse OK
    but are discarded — same deferred-to-A10 scope as user ADTs
    with parameterized ctor signatures. -/
partial def parseValDecl : ParserM Decl := do
  let startSpan ← peekSpan
  let _ ← expectKw Keyword.valKw "val declaration"
  let nameToken ← peek
  let name ← match nameToken with
    | Token.ident identString   => do let _ ← advance; pure identString
    | Token.uident uidentString => do let _ ← advance; pure uidentString
    | _ => do
      recordError "P041"
        s!"val name: expected identifier, found '{repr nameToken}'"
      pure "_error"
  -- Optional type params — parsed then ignored at elab time.
  let _discardedTypeParams ← parseOptionalTypeParams
  let _ ← expect Token.colon "val type annotation"
  let typeExpr ← parseExpr
  let _ ← expect Token.semi "val declaration terminator"
  let stopSpan ← peekSpan
  pure (Decl.valDecl name typeExpr (Span.merge startSpan stopSpan))

/-- `const NAME : type = expr ;` -/
partial def parseConstDecl : ParserM Decl := do
  let startSpan ← peekSpan
  let _ ← expectKw Keyword.constKw "const declaration"
  let currentToken ← peek
  let name ← match currentToken with
    | Token.uident n => do let _ ← advance; pure n
    | Token.ident  n => do let _ ← advance; pure n
    | _ => do
      recordError "P005" s!"const name: expected identifier, found '{repr currentToken}'"
      pure "_error"
  let _ ← expect Token.colon "const type annotation"
  let typeExpr ← parseExpr
  let _ ← expect Token.equals "const binding"
  let value ← parseExpr
  let _ ← expect Token.semi "const declaration terminator"
  let stopSpan ← peekSpan
  pure (Decl.constDecl name typeExpr value (Span.merge startSpan stopSpan))

/- ### Function declarations -/

/-- Parse the parameter-mode prefix. -/
partial def parseParamMode : ParserM ParamMode := do
  let currentToken ← peek
  match currentToken with
  | Token.kw Keyword.ownKw    => do let _ ← advance; pure ParamMode.own
  | Token.kw Keyword.refKw    => do
    let _ ← advance
    if (← consumeKw Keyword.mutKw) then
      pure ParamMode.refMut
    else
      pure ParamMode.ref_
  | Token.kw Keyword.affineKw => do let _ ← advance; pure ParamMode.affine
  | Token.kw Keyword.ghostKw  => do let _ ← advance; pure ParamMode.ghost
  | Token.kw Keyword.secretKw => do let _ ← advance; pure ParamMode.secret
  | Token.kw Keyword.linearKw => do let _ ← advance; pure ParamMode.linear
  | _ => pure ParamMode.default_

/-- Parse one function parameter: `[mode] name : type`. -/
partial def parseFnParam : ParserM FnParam := do
  let startSpan ← peekSpan
  let mode ← parseParamMode
  let (name, _) ← expectIdent "function parameter"
  let _ ← expect Token.colon "function parameter type"
  let typeExpr ← parseExpr
  let stopSpan ← peekSpan
  pure (FnParam.mk mode name typeExpr (Span.merge startSpan stopSpan))

/-- `(param1, param2, …)` or `()`. -/
partial def parseFnParams : ParserM (Array FnParam) := do
  let _ ← expect Token.lparen "function parameter list"
  let currentToken ← peek
  match currentToken with
  | Token.rparen =>
    let _ ← advance
    pure #[]
  | _ =>
    let fnParams ← fnParamsLoop #[]
    let _ ← expect Token.rparen "end of function parameters"
    pure fnParams

/-- Accumulating loop for `parseFnParams`. -/
partial def fnParamsLoop (paramsSoFar : Array FnParam)
    : ParserM (Array FnParam) := do
  let nextParam ← parseFnParam
  let paramsSoFar := paramsSoFar.push nextParam
  let followingToken ← peek
  match followingToken with
  | Token.comma =>
    let _ ← advance
    fnParamsLoop paramsSoFar
  | _ => pure paramsSoFar

/-- Parse a function body: `= expr ;` or `begin fn … end fn ;`. -/
partial def parseFnBody : ParserM FnBody := do
  let currentToken ← peek
  match currentToken with
  | Token.equals =>
    let _ ← advance
    let bodyExpr ← parseExpr
    let _ ← expect Token.semi "one-liner function terminator"
    pure (FnBody.oneLiner bodyExpr)
  | Token.kw Keyword.beginKw =>
    parseBlockFnBody
  | _ =>
    recordError "P040"
      s!"expected '=' or 'begin fn' for function body, found '{repr currentToken}'"
    let span ← peekSpan
    let _ ← swallowToSync
    pure (FnBody.oneLiner (Expr.unimplemented "malformed fn body" span))

/-- Parse `begin fn stmt* return expr? ; end fn ;`. -/
partial def parseBlockFnBody : ParserM FnBody := do
  let _ ← expectKw Keyword.beginKw "block fn body"
  let _ ← expectKw Keyword.fnKw "begin fn"
  let stmts ← blockFnStmtsLoop #[]
  let _ ← expectKw Keyword.returnKw "return from function body"
  let ret ← parseReturnValue
  let _ ← expectKw Keyword.endKw "end of function body"
  let _ ← expectKw Keyword.fnKw "end fn closer"
  let _ ← expect Token.semi "function declaration terminator"
  pure (FnBody.block stmts ret)

/-- Collect statements until we see `return` or EOF.  Q52:
    includes explicit EOF stop AND a position-progress check —
    otherwise truncated input where parseExpr/parseLetStmt reaches
    EOF inside a sub-parser whose catch-all `advance` is a no-op
    would spin forever in the `_` expression-statement arm. -/
partial def blockFnStmtsLoop (stmtsSoFar : Array Stmt)
    : ParserM (Array Stmt) := do
  let currentToken ← peek
  match currentToken with
  | Token.kw Keyword.returnKw => pure stmtsSoFar
  | Token.eof                 => pure stmtsSoFar
  | Token.kw Keyword.letKw =>
    let posBefore := (← get).pos
    let letStmt ← parseLetStmt
    let posAfter := (← get).pos
    if posAfter == posBefore then
      pure (stmtsSoFar.push letStmt)
    else
      blockFnStmtsLoop (stmtsSoFar.push letStmt)
  | Token.kw Keyword.fnKw => do
    -- E-7 §4.7 rule 18: local fn inside a `begin fn … end fn`
    -- body.  Same parser as block-expression local fns — see
    -- `parseLocalFnStmt` for the full shape + restriction set.
    let posBefore := (← get).pos
    let stmt? ← parseLocalFnStmt
    let posAfter := (← get).pos
    if posAfter == posBefore then
      pure stmtsSoFar
    else
      match stmt? with
      | some fnStmt => blockFnStmtsLoop (stmtsSoFar.push fnStmt)
      | none        => blockFnStmtsLoop stmtsSoFar
  | _ =>
    let startSpan ← peekSpan
    let posBefore := (← get).pos
    let sideEffectingExpr ← parseExpr
    let _ ← expect Token.semi "expression statement terminator"
    let posAfter := (← get).pos
    let stopSpan ← peekSpan
    let nextStmt := Stmt.exprStmt sideEffectingExpr (Span.merge startSpan stopSpan)
    if posAfter == posBefore then
      pure (stmtsSoFar.push nextStmt)
    else
      blockFnStmtsLoop (stmtsSoFar.push nextStmt)

/-- Parse the expression after `return`, accepting bare `return ;`
    as `return () ;`. -/
partial def parseReturnValue : ParserM Expr := do
  let currentToken ← peek
  match currentToken with
  | Token.semi =>
    let span ← peekSpan
    let _ ← advance
    pure (Expr.unit span)
  | _ =>
    let returnExpr ← parseExpr
    let _ ← expect Token.semi "return value terminator"
    pure returnExpr

/-- Parse a kind expression appearing after a `:` in a type-param
    declaration.  Accepts the two reserved kind keywords (`type`,
    `effect`) plus any lower-case identifier (so built-in
    non-reserved kinds `nat`/`region` per grammar §5.5 and user
    kind aliases work).  Higher-kinded arrows like `type -> type`
    are grammar-valid but deferred — the current call site wraps
    this in the type-param list parser which terminates at `,` or
    `>`, so larger kind expressions would need a separate parser
    anyway.  -/
partial def parseTypeParamKind : ParserM Expr := do
  let currentToken ← peek
  let span ← peekSpan
  match currentToken with
  | Token.kw Keyword.typeKw =>
    let _ ← advance
    pure (Expr.literal currentToken span)
  | Token.kw Keyword.effectKw =>
    let _ ← advance
    pure (Expr.literal currentToken span)
  | Token.ident name =>
    let _ ← advance
    pure (Expr.var { parts := #[], final := name, span := span })
  | Token.uident name =>
    let _ ← advance
    pure (Expr.var { parts := #[], final := name, span := span })
  | _ =>
    recordError "P036"
      s!"expected kind (e.g., 'type', 'effect'), found '{repr currentToken}'"
    let _ ← advance
    pure (Expr.unimplemented "kind" span)

/-- Parse one type parameter `name : kind`, producing a
    ghost-moded `FnParam`.  Type parameters and ghost value
    parameters share the same kernel encoding (grade 0); the
    surface distinction lives only in the elaborator's error
    messages and call-site resolution. -/
partial def parseOneTypeParam : ParserM FnParam := do
  let startSpan ← peekSpan
  let (name, _) ← expectIdent "type parameter name"
  let _ ← expect Token.colon "type parameter kind annotation"
  let kindExpr ← parseTypeParamKind
  let stopSpan ← peekSpan
  pure (FnParam.mk ParamMode.ghost name kindExpr
    (Span.merge startSpan stopSpan))

/-- Accumulating loop for comma-separated type parameters.
    Mirrors `fnParamsLoop`: scan entries separated by `,`, stop
    at the first non-comma, leave the terminator (`>`) for the
    caller to consume.  Delimiter handling lives in
    `parseOptionalTypeParams` so the loop body matches the
    fn-param loop's shape exactly. -/
partial def typeParamsLoop (paramsSoFar : Array FnParam)
    : ParserM (Array FnParam) := do
  let nextParam ← parseOneTypeParam
  let paramsSoFar := paramsSoFar.push nextParam
  let followingToken ← peek
  match followingToken with
  | Token.comma =>
    let _ ← advance
    typeParamsLoop paramsSoFar
  | _ => pure paramsSoFar

/-- Parse an optional `< tp1 : kind, tp2 : kind, … >` type-parameter
    list.  Returns `#[]` when no `<` follows.  Otherwise consumes
    through the matching `>`.  Type parameters compile to
    ghost-moded `FnParam`s that prepend the regular parameter
    list, so `fn id<a: type>(x: a) : a` becomes the same shape
    as `fn id(ghost a: type, x: a) : a`.  Reports P035 when
    neither `,` nor `>` follows a type parameter — a targeted
    diagnostic pointing users at the `<a: kind, b: kind>` form
    rather than the generic P001 "expected `>`" that `expect`
    would emit. -/
partial def parseOptionalTypeParams : ParserM (Array FnParam) := do
  let currentToken ← peek
  match currentToken with
  | Token.lt =>
    let _ ← advance
    let typeParams ← typeParamsLoop #[]
    let followingToken ← peek
    match followingToken with
    | Token.gt =>
      let _ ← advance
      pure typeParams
    | _ =>
      recordError "P035"
        s!"expected ',' or '>' in type-parameter list, found '{repr followingToken}'"
      pure typeParams
  | _ => pure #[]

/-- Parse an optional `with EFFECT, EFFECT, …` clause after a
    function's return-type.  The parsed list is carried to the
    elaborator via a synthetic `__effects(...)` attribute
    prepended to the fn's attrs array (see `fn_decl` parser
    below); this avoids growing the `Decl.fnDecl` constructor's
    positional arity while preserving the effect information.

    A12 (commit 2ac13c28) enforces effect-row subsumption at
    every App site by walking each pass-2 body's `Term.const`
    refs, unioning declared effects via `Grade.Effect.add`
    (with `Read ≤ Write` honored through `write_`'s
    pre-saturation), and comparing to the enclosing fn's
    declared row via `Effect.LessEq`.  Widening emits E044.

    Each effect in the list is parsed as a general expression
    so effect variables, type-applied effects (`eff(Nat)`),
    and lowercase effect identifiers all ride through the
    same path; non-`.var` shapes silently drop at the elab
    bridge today (full handling of `eff(T)` parameterized
    effects lands with §9.5's user-effect decls). -/
partial def parseOptionalEffectRow : ParserM (Array Expr) := do
  if !(← consumeKw Keyword.withKw) then
    pure #[]
  else
    let mut effectsSoFar : Array Expr := #[]
    let first ← parseExpr
    effectsSoFar := effectsSoFar.push first
    while (← consume Token.comma) do
      let currentToken ← peek
      match currentToken with
      | Token.kw Keyword.beginKw => break
      | Token.equals             => break
      | Token.semi               => break
      | _ =>
        let next ← parseExpr
        effectsSoFar := effectsSoFar.push next
    pure effectsSoFar

/-- Parse an optional chain of spec clauses between the effect
    row and the function body (§5.1).  Four clause kinds:

      * `pre <expr>;` — precondition.
      * `post <ident> => <expr>;` — postcondition; the ident
        names the return value.
      * `decreases <expr>;` — termination measure.
      * `where <expr>;` — type-class constraints.

    Multiple `pre` and `post` clauses may appear in sequence;
    `decreases` and `where` are typically one each.  Strict
    ordering per §5.1 (effects → pre → post → decreases →
    where) is validated here at parse time as part of the
    expected-token discipline; a more lenient elaborator pass
    will normalize ordering later.

    Phase-2 accepts the syntax and ATTACHES the clauses to
    the fnDecl AST's `specs` field as `Ast.SpecClause` values —
    SMT discharge for pre/post/decreases lands with Stream E
    (E1-E4); `where` constraints need type-class resolution
    (M7).  Until then, the elaborator validates clause
    ordering (§5.1: where → pre → post → decreases) and
    elaborates each predicate under the fn's parameter scope
    so syntactic errors surface immediately; the elaborated
    Term list is carried through to Stream E for discharge. -/
partial def parseOptionalSpecClauses : ParserM (Array Ast.SpecClause) := do
  let rec loop (acc : Array Ast.SpecClause)
      : ParserM (Array Ast.SpecClause) := do
    let startSpan ← peekSpan
    let currentToken ← peek
    match currentToken with
    | Token.kw Keyword.preKw =>
      let _ ← advance
      let predicateExpr ← parseExpr
      let _ ← expect Token.semi "pre clause terminator"
      let stopSpan ← peekSpan
      loop (acc.push
        (Ast.SpecClause.preCond predicateExpr (Span.merge startSpan stopSpan)))
    | Token.kw Keyword.postKw =>
      let _ ← advance
      -- Look for the `<binder> =>` form.  The identifier
      -- followed by `=>` names the return value; absent
      -- this pattern, `post EXPR;` has no explicit binder
      -- (the elaborator synthesizes a fresh `result` name).
      let afterPost ← peek
      let (returnBinder, predicateExpr) ← match afterPost with
        | Token.ident identName => do
          -- Peek past the ident for `=>` to decide.
          let parserState ← get
          let nextIdx := parserState.pos + 1
          let followToken :=
            if nextIdx < parserState.tokens.size then
              parserState.tokens[nextIdx]!.token
            else
              Token.eof
          match followToken with
          | Token.fatArrow => do
            let _ ← advance  -- consume identifier
            let _ ← advance  -- consume `=>`
            let expr ← parseExpr
            pure (identName, expr)
          | _ =>
            -- Plain `post EXPR;` — binder defaults to "_".
            let expr ← parseExpr
            pure ("_", expr)
        | _ => do
          let expr ← parseExpr
          pure ("_", expr)
      let _ ← expect Token.semi "post clause terminator"
      let stopSpan ← peekSpan
      loop (acc.push
        (Ast.SpecClause.postCond returnBinder predicateExpr
          (Span.merge startSpan stopSpan)))
    | Token.kw Keyword.decreasesKw =>
      let _ ← advance
      let measureExpr ← parseExpr
      let _ ← expect Token.semi "decreases clause terminator"
      let stopSpan ← peekSpan
      loop (acc.push
        (Ast.SpecClause.decreases measureExpr (Span.merge startSpan stopSpan)))
    | Token.kw Keyword.whereKw =>
      let _ ← advance
      let constraintExpr ← parseExpr
      let _ ← expect Token.semi "where clause terminator"
      let stopSpan ← peekSpan
      loop (acc.push
        (Ast.SpecClause.whereCstr constraintExpr (Span.merge startSpan stopSpan)))
    | _ => pure acc
  loop #[]

/-- Parse a `fn` declaration.  Attributes + visibility come from
    the caller (already consumed).  Type parameters `<a: kind, …>`
    are optional and land as ghost-moded `FnParam`s prepended to
    the regular parameter list — the kernel encoding of the two
    kinds of parameter is identical (usage grade 0 for ghost). -/
partial def parseFnDecl (attrs : Array Expr) (visibility : Visibility)
    : ParserM Decl := do
  let startSpan ← peekSpan
  let _ ← expectKw Keyword.fnKw "function declaration"
  let (name, _) ← expectIdent "function name"
  let typeParams ← parseOptionalTypeParams
  let regularParams ← parseFnParams
  let params := typeParams ++ regularParams
  let _ ← expect Token.colon "function return-type colon"
  let retType ← parseExpr
  -- B3: parse the `with EFFECT, EFFECT, …` row and stash on the
  -- fnDecl AST's first-class `effects` field.  A12 uses this
  -- directly per `FX/Elab/Elaborate.lean`'s pass-1 effect extractor.
  let effects ← parseOptionalEffectRow
  -- B4: parse pre/post/decreases/where clauses into the fnDecl
  -- AST's `specs` field.  Ordering validation + SMT discharge
  -- live in the elaborator (§5.1 and Stream E).
  let specs ← parseOptionalSpecClauses
  let body ← parseFnBody
  let stopSpan ← peekSpan
  pure (Decl.fnDecl attrs visibility name params retType effects specs body
    (Span.merge startSpan stopSpan))

/- ### Decl dispatcher -/

-- ### ADT declarations (task B9)
--
-- Variant form per fx_grammar.md §5.9:
--
--   type NAME typeParams?
--     Ctor1;
--     Ctor2;
--     Ctor3(arg: type, arg: type);
--     Ctor4(type, type);                     // positional — synth names
--   end type;
--
-- The alias form (`type NAME = expr;`) and record form (`type NAME {
-- ...fields }`) are deferred to B8 (records).  This parser rejects
-- them with `P037` so the grammar surface remains documented.

/-- Parse one constructor-field: either `lower_ident ":" type`
    (named) or plain `type` (positional).  Positional fields get
    synthetic names `_arg_0`, `_arg_1`, … — chosen here so the
    elaborator has a unique name per position while still knowing
    the field was positional (the leading underscore is the hint). -/
partial def parseCtorField (positionalIndex : Nat) : ParserM FnParam := do
  let startSpan ← peekSpan
  -- Lookahead: if the next two tokens are `ident :`, treat as
  -- named form; otherwise as positional.
  let firstToken ← peek
  match firstToken with
  | Token.ident fieldName => do
    -- Could be a named field (`radius: f64`) or a positional
    -- typed-with-a-lowercase-typename like `nat`.  Peek past the
    -- ident for `:`.
    let parserState ← get
    let nextIdx := parserState.pos + 1
    let followToken :=
      if nextIdx < parserState.tokens.size then
        parserState.tokens[nextIdx]!.token
      else
        Token.eof
    match followToken with
    | Token.colon => do
      let _ ← advance  -- consume the ident
      let _ ← advance  -- consume the colon
      let typeExpr ← parseExpr
      let stopSpan ← peekSpan
      pure (FnParam.mk ParamMode.default_ fieldName typeExpr
        (Span.merge startSpan stopSpan))
    | _ => do
      -- Positional: the ident is a type expression's head.
      let typeExpr ← parseExpr
      let stopSpan ← peekSpan
      pure (FnParam.mk ParamMode.default_ s!"_arg_{positionalIndex}"
        typeExpr (Span.merge startSpan stopSpan))
  | _ => do
    -- Leading token is something other than ident (uident, keyword
    -- type, parenthesized type expression) — always positional.
    let typeExpr ← parseExpr
    let stopSpan ← peekSpan
    pure (FnParam.mk ParamMode.default_ s!"_arg_{positionalIndex}"
      typeExpr (Span.merge startSpan stopSpan))

/-- Loop over constructor arg fields separated by `,`, terminating
    at `)`.  Threads a positional-index counter for synthetic names. -/
partial def ctorFieldsLoop (positionalIndex : Nat)
    (fieldsSoFar : Array FnParam) : ParserM (Array FnParam) := do
  let currentToken ← peek
  match currentToken with
  | Token.rparen => pure fieldsSoFar
  | _ => do
    let nextField ← parseCtorField positionalIndex
    let fieldsSoFar := fieldsSoFar.push nextField
    let followingToken ← peek
    match followingToken with
    | Token.comma => do
      let _ ← advance
      ctorFieldsLoop (positionalIndex + 1) fieldsSoFar
    | _ => pure fieldsSoFar

/-- Parse one named record field: `lower_ident ":" type`.  Returns a
    `FnParam` with the field name and elaborated type expression.
    Mandatorily named — positional form is a grammar violation. -/
partial def parseRecordField : ParserM FnParam := do
  let startSpan ← peekSpan
  let (fieldName, _) ← expectIdent "record field name"
  let _ ← expect Token.colon "record field type annotation"
  let typeExpr ← parseExpr
  let stopSpan ← peekSpan
  pure (FnParam.mk ParamMode.default_ fieldName typeExpr
    (Span.merge startSpan stopSpan))

/-- Loop over record fields separated by `;`, terminating at `}`.
    Per grammar §5.9 a trailing `;` is optional. -/
partial def recordFieldsLoop (fieldsSoFar : Array FnParam)
    : ParserM (Array FnParam) := do
  let currentToken ← peek
  match currentToken with
  | Token.rbrace => pure fieldsSoFar
  | _ => do
    let nextField ← parseRecordField
    let fieldsSoFar := fieldsSoFar.push nextField
    let followingToken ← peek
    match followingToken with
    | Token.semi => do
      let _ ← advance
      recordFieldsLoop fieldsSoFar
    | Token.rbrace => pure fieldsSoFar  -- trailing-`;` elision
    | _ => do
      recordError "P042" "expected ';' or '}' after record field"
      pure fieldsSoFar

/-- Parse one variant constructor: `UIdent` or `UIdent(fields)`,
    terminated by `;`. -/
partial def parseVariantCtor : ParserM VariantCtor := do
  let startSpan ← peekSpan
  let ctorToken ← peek
  let ctorName ← match ctorToken with
    | Token.uident nameString => do
      let _ ← advance
      pure nameString
    | _ => do
      recordError "P038"
        s!"constructor name: expected PascalCase identifier, found '{repr ctorToken}'"
      let _ ← advance
      pure "_error"
  -- Optional `(fields)`.
  let ctorArgs ← do
    if (← consume Token.lparen) then
      let fields ← ctorFieldsLoop 0 #[]
      let _ ← expect Token.rparen "constructor argument list"
      pure fields
    else
      pure #[]
  let _ ← expect Token.semi "constructor terminator"
  let stopSpan ← peekSpan
  pure (VariantCtor.mk ctorName ctorArgs (Span.merge startSpan stopSpan))

/-- Loop over variant constructors until `end type` is seen.
    Terminates either at `end type` (success) or EOF (records P040). -/
partial def variantCtorsLoop (ctorsSoFar : Array VariantCtor)
    : ParserM (Array VariantCtor) := do
  let currentToken ← peek
  match currentToken with
  | Token.kw Keyword.endKw => pure ctorsSoFar
  | Token.eof => do
    recordError "P040" "unexpected EOF inside type declaration (expected 'end type')"
    pure ctorsSoFar
  | _ => do
    let nextCtor ← parseVariantCtor
    variantCtorsLoop (ctorsSoFar.push nextCtor)

/-- `type NAME <typeParams>? ctor+ end type ;` — variant ADT
    declaration.  The alias form (`type NAME = expr`) and record
    form (`type NAME { ... }`) are recognized but not yet
    elaborated; they emit `P037`.

    `attrs` is the pre-parsed `@[...]` block (consumed by
    `parseDecl` before dispatch); `@[copy]` (§7.8) is recognized
    by the elaborator and stored on the resulting `IndSpec`. -/
partial def parseTypeDecl (attrs : Array Expr) : ParserM Decl := do
  let startSpan ← peekSpan
  let _ ← expectKw Keyword.typeKw "type declaration"
  let nameToken ← peek
  let name ← match nameToken with
    | Token.ident identString  => do let _ ← advance; pure identString
    | Token.uident uidentString => do let _ ← advance; pure uidentString
    | _ => do
      recordError "P037"
        s!"type name: expected identifier, found '{repr nameToken}'"
      pure "_error"
  let typeParams ← parseOptionalTypeParams
  -- Non-variant forms emit P037 for now.
  let afterNameToken ← peek
  match afterNameToken with
  | Token.equals => do
    recordError "P037" "type alias form `type NAME = ...` not yet supported (B9 is variant form)"
    let _ ← swallowToSync
    let stopSpan ← peekSpan
    pure (Decl.typeDecl attrs name typeParams #[] (Span.merge startSpan stopSpan))
  | Token.lbrace => do
    -- B8 record form: `type NAME { field: type; field: type; };`
    -- Translated into a single-ctor ADT whose ctor is named same as
    -- the type (Lean/Idris convention).  Each record field becomes
    -- a named ctor arg; field names are preserved via the FnParam
    -- name so field access (`.name`) and pattern destructuring
    -- (`match r; NAME(field_a, field_b) => ...`) both work.
    let _ ← advance  -- consume `{`
    let recordFields ← recordFieldsLoop #[]
    let _ ← expect Token.rbrace "record field list closer"
    let _ ← expect Token.semi "record type declaration terminator"
    let stopSpan ← peekSpan
    let ctorSpan := Span.merge startSpan stopSpan
    -- Record form desugars to a single-ctor ADT whose ctor is the
    -- PascalCase-ified type name (`config` → `Config`, `Point` →
    -- `Point`).  Pattern matching requires UIDENT ctor heads per
    -- grammar §8, so lowercase type names are forcibly capitalized
    -- on the ctor side to satisfy that discipline.  Two records
    -- with distinct type names get distinct ctors by construction,
    -- so unqualified-ctor sweep (§B9 resolveUnqualCtor?) is
    -- unambiguous across a program.
    let capitalize (s : String) : String :=
      match s.toList with
      | c :: rest => String.ofList (c.toUpper :: rest)
      | []        => s
    let syntheticCtorName := capitalize name
    let syntheticCtor : VariantCtor :=
      VariantCtor.mk syntheticCtorName recordFields ctorSpan
    pure (Decl.typeDecl attrs name typeParams #[syntheticCtor] ctorSpan)
  | _ => do
    let ctors ← variantCtorsLoop #[]
    let _ ← expectKw Keyword.endKw "type declaration closer"
    let _ ← expectKw Keyword.typeKw "type declaration closer"
    let _ ← expect Token.semi "type declaration terminator"
    let stopSpan ← peekSpan
    pure (Decl.typeDecl attrs name typeParams ctors (Span.merge startSpan stopSpan))

/-- Parse `impl TypeName fn-members end impl;` — method bundle
    per §16.1.  Each member is a full top-level-style `fnDecl`
    parsed via `parseFnDecl`; the `typeName` is the enclosing
    type the methods attach to.  Phase-2 limitation: no `self`
    keyword support — every member's first parameter must name
    its type explicitly (e.g. `fn foo(x: Connection) : ...`).
    Later work will inject `self` as a synthetic first
    parameter of type `typeName`. -/
partial def parseImplDecl : ParserM Decl := do
  let startSpan ← peekSpan
  let _ ← expectKw Keyword.implKw "impl declaration"
  let nameTok ← peek
  let typeName ← match nameTok with
    | Token.ident identString  => do let _ ← advance; pure identString
    | Token.uident uidentString => do let _ ← advance; pure uidentString
    | _ => do
      recordError "P060"
        s!"impl type name: expected identifier, found '{repr nameTok}'"
      pure "_impl_type_error"
  let members ← implMembersLoop #[]
  let _ ← expectKw Keyword.endKw "end of impl block"
  let _ ← expectKw Keyword.implKw "end impl closer"
  let _ ← expect Token.semi "impl declaration terminator"
  let stopSpan ← peekSpan
  pure (Decl.implDecl typeName members (Span.merge startSpan stopSpan))

/-- Loop over impl members — zero or more `fn NAME(...) : T =
    body;` declarations.  Terminates at `end impl;`. -/
partial def implMembersLoop (acc : Array Decl) : ParserM (Array Decl) := do
  let currentToken ← peek
  match currentToken with
  | Token.kw Keyword.endKw =>
    -- Guard: end must be followed by impl (the closer).  If
    -- some other `end foo;` appears we fall through to the
    -- fn-parse arm where parseFnDecl will emit P040.
    pure acc
  | Token.kw Keyword.fnKw => do
    let memberDecl ← parseFnDecl #[] Visibility.private_
    implMembersLoop (acc.push memberDecl)
  | _ => do
    recordError "P061"
      s!"impl member: expected 'fn' or 'end impl', found '{repr currentToken}'"
    let _ ← swallowToSync
    pure acc

-- Session declarations (task S10).  Per fx_grammar.md §11:
--   session_decl  := SESSION lower_ident type_params? session_body END SESSION ";"
--   session_body  := session_step+ | REC upper_ident ";" session_step+
--   session_step  := SEND "(" payload ")" ";"
--                  | RECEIVE "(" payload ")" ";"
--                  | BRANCH arm+ END BRANCH ";"
--                  | SELECT arm+ END SELECT ";"
--                  | upper_ident ";"
--                  | END ";"
--   arm           := lower_ident "=>" session_step* END ";"
--
-- `branch` is NOT in the global keyword set — recognized as a
-- contextual identifier via `Token.ident "branch"`.  `select`,
-- `send`, `receive`, `rec`, `end` ARE keywords.  The elaborator
-- (S11) consumes the AST and feeds payload `Expr`s through type
-- elaboration, producing `SessionType` which S9's translator
-- lifts into `CoindSpec`s.

/-- Parse `(LABEL : TYPE)` inside a send/receive step.  Returns
    the payload name + elaborated-later type expression. -/
partial def parseSessionPayload : ParserM (String × Ast.Expr) := do
  let _ ← expect Token.lparen "session payload opener"
  let nameTok ← peek
  let payloadName ← match nameTok with
    | Token.ident identName =>
      let _ ← advance; pure identName
    | _ =>
      recordError "P040"
        s!"session payload: expected lowercase identifier, found '{repr nameTok}'"
      pure "_error_payload"
  let _ ← expect Token.colon "session payload name terminator"
  let payloadTypeExpr ← parseExpr
  let _ ← expect Token.rparen "session payload closer"
  pure (payloadName, payloadTypeExpr)

/-- Parse zero-or-more session steps until one of the terminators
    (`end session`, `end branch`, `end select`, `end`) appears.
    Doesn't consume the `end`.  `stopOnArmEnd` flags the branch-arm
    context where a bare `end ;` terminates the arm (not the
    enclosing branch/select).  Phase-1 v1 terminates a list on
    ANY `end` — caller does the specific-keyword check. -/
-- Parse a session step list.  `bodyLevel = true` when called
-- from `parseSessionDecl`'s top-level body; `false` when called
-- from inside a branch-arm body via `parseSessionBranchArm`.
--
-- The distinction governs interpretation of an `end` lookahead:
--   * At body level, `end;` (END semi) is an explicit endStep
--     — consume it; `end session;` is the decl closer — stop.
--   * At arm level, ANY `end` closes the arm — stop without
--     consuming.
--
-- Without this split, the grammar ambiguity
-- (`session_step ::= ... | END ";"`  vs arm/decl closer) would
-- either swallow the closer as a step (leaving the caller
-- stuck) or skip a legal `end;` step at the session level.
partial def parseSessionSteps (bodyLevel : Bool)
    : ParserM (Array Ast.SessionStep) :=
  stepsLoop bodyLevel #[]

partial def stepsLoop (bodyLevel : Bool)
    (stepsSoFar : Array Ast.SessionStep)
    : ParserM (Array Ast.SessionStep) := do
  let peekedTok ← peek
  match peekedTok with
  -- EOF always stops — `parseSessionStep`'s catch-all calls
  -- `advance`, which is a no-op at EOF.  Recursing here would
  -- grow the array unboundedly → OOM.
  | Token.eof => pure stepsSoFar
  | Token.kw Keyword.endKw =>
    if bodyLevel then
      -- At session body level, peek offset 1 to disambiguate.
      let nextTok ← peekAt 1
      match nextTok with
      | Token.semi =>
        -- `end ;` — explicit endStep.  parseSessionStep's
        -- endKw arm consumes the `end` and the `;`.
        let oneStep ← parseSessionStep
        stepsLoop bodyLevel (stepsSoFar.push oneStep)
      | _ =>
        -- `end session ;` / `end branch ;` / `end select ;`
        -- — decl/block closer.  Stop without consuming.
        pure stepsSoFar
    else
      -- Arm level: every `end` closes the arm.  Stop.
      pure stepsSoFar
  | _ =>
    -- Progress check: abort the loop if parseSessionStep fails
    -- to advance the cursor (malformed recovery path), to prevent
    -- unbounded array growth → OOM.
    let posBefore := (← get).pos
    let oneStep ← parseSessionStep
    let posAfter := (← get).pos
    if posAfter == posBefore then
      pure (stepsSoFar.push oneStep)
    else
      stepsLoop bodyLevel (stepsSoFar.push oneStep)

/-- Parse one session step. -/
partial def parseSessionStep : ParserM Ast.SessionStep := do
  let startSpan ← peekSpan
  let peekedTok ← peek
  match peekedTok with
  | Token.kw Keyword.sendKw => do
    let _ ← advance
    let (payloadName, payloadType) ← parseSessionPayload
    let _ ← expect Token.semi "send step terminator"
    let stopSpan ← peekSpan
    pure (Ast.SessionStep.sendStep payloadName payloadType
      (Span.merge startSpan stopSpan))
  | Token.kw Keyword.receiveKw => do
    let _ ← advance
    let (payloadName, payloadType) ← parseSessionPayload
    let _ ← expect Token.semi "receive step terminator"
    let stopSpan ← peekSpan
    pure (Ast.SessionStep.recvStep payloadName payloadType
      (Span.merge startSpan stopSpan))
  | Token.kw Keyword.selectKw => do
    let _ ← advance
    let armsList ← parseSessionBranchArms #[]
    let _ ← expectKw Keyword.endKw "select block closer"
    let _ ← expectKw Keyword.selectKw "select block closer"
    let _ ← expect Token.semi "select terminator"
    let stopSpan ← peekSpan
    pure (Ast.SessionStep.selectStep armsList
      (Span.merge startSpan stopSpan))
  | Token.ident "branch" => do
    let _ ← advance
    let armsList ← parseSessionBranchArms #[]
    let _ ← expectKw Keyword.endKw "branch block closer"
    let endCloserTok ← peek
    match endCloserTok with
    | Token.ident "branch" =>
      let _ ← advance
    | _ =>
      recordError "P041"
        s!"branch block closer: expected 'branch', found '{repr endCloserTok}'"
    let _ ← expect Token.semi "branch terminator"
    let stopSpan ← peekSpan
    pure (Ast.SessionStep.branchStep armsList
      (Span.merge startSpan stopSpan))
  | Token.kw Keyword.endKw => do
    -- Bare `end;` — session terminator (protocol complete).
    let _ ← advance
    let _ ← expect Token.semi "end step terminator"
    let stopSpan ← peekSpan
    pure (Ast.SessionStep.endStep (Span.merge startSpan stopSpan))
  | Token.uident upperName => do
    -- `LABEL;` — reference to the enclosing `rec LABEL` binder.
    let _ ← advance
    let _ ← expect Token.semi "continue step terminator"
    let stopSpan ← peekSpan
    pure (Ast.SessionStep.continueStep upperName
      (Span.merge startSpan stopSpan))
  | _ => do
    recordError "P042"
      s!"session step: expected 'send', 'receive', 'branch', 'select', 'end', or rec-label, found '{repr peekedTok}'"
    let _ ← advance
    pure (Ast.SessionStep.endStep startSpan)

/-- Parse one branch arm: `LABEL => session_step* end ;`. -/
partial def parseSessionBranchArm : ParserM Ast.SessionBranchArm := do
  let startSpan ← peekSpan
  let labelTok ← peek
  let armLabel ← match labelTok with
    | Token.ident labelName => do
      let _ ← advance; pure labelName
    | _ => do
      recordError "P041"
        s!"branch arm label: expected identifier, found '{repr labelTok}'"
      pure "_error_label"
  let _ ← expect Token.fatArrow "branch arm body"
  -- bodyLevel := false — arm-level steps stop at the first `end`
  -- which is the arm closer; there is no ambiguity here.
  let armSteps ← parseSessionSteps false
  let _ ← expectKw Keyword.endKw "branch arm closer"
  let _ ← expect Token.semi "branch arm terminator"
  let stopSpan ← peekSpan
  pure (Ast.SessionBranchArm.mk armLabel armSteps
    (Span.merge startSpan stopSpan))

/-- Accumulating loop for branch arms.  Stops when the peeked
    token is `end` (closer for the branch/select block) OR at
    EOF, AND on any iteration where `parseSessionBranchArm`
    fails to advance the cursor (prevents unbounded array
    growth on malformed input — same trap as `stepsLoop`). -/
partial def parseSessionBranchArms
    (armsSoFar : Array Ast.SessionBranchArm)
    : ParserM (Array Ast.SessionBranchArm) := do
  let peekedTok ← peek
  match peekedTok with
  | Token.kw Keyword.endKw => pure armsSoFar
  | Token.eof              => pure armsSoFar
  | _ =>
    let posBefore := (← get).pos
    let nextArm ← parseSessionBranchArm
    let posAfter := (← get).pos
    if posAfter == posBefore then
      pure (armsSoFar.push nextArm)
    else
      parseSessionBranchArms (armsSoFar.push nextArm)

/-- Parse `session NAME<typeParams>? (rec LABEL;)? step+ end
    session;`. -/
partial def parseSessionDecl : ParserM Decl := do
  let startSpan ← peekSpan
  let _ ← expectKw Keyword.sessionKw "session declaration"
  let nameTok ← peek
  let sessionName ← match nameTok with
    | Token.ident identName =>
      let _ ← advance; pure identName
    | Token.uident uidentName =>
      let _ ← advance; pure uidentName
    | _ =>
      recordError "P039"
        s!"session name: expected identifier, found '{repr nameTok}'"
      pure "_error_session"
  let typeParamsList ← parseOptionalTypeParams
  -- Optional `rec UIDENT;` prefix.
  let peekedRec ← peek
  let recBinderOpt ← match peekedRec with
    | Token.kw Keyword.recKw => do
      let _ ← advance
      let labelTok ← peek
      match labelTok with
      | Token.uident labelName => do
        let _ ← advance
        let _ ← expect Token.semi "rec binder terminator"
        pure (some labelName)
      | _ => do
        recordError "P039"
          s!"rec binder label: expected UIDENT, found '{repr labelTok}'"
        pure (some "_error_rec")
    | _ => pure none
  -- bodyLevel := true — at the decl body level, a bare `end;`
  -- is an explicit endStep; only `end session;` closes the decl.
  let stepsList ← parseSessionSteps true
  let _ ← expectKw Keyword.endKw "end of session"
  let _ ← expectKw Keyword.sessionKw "end session closer"
  let _ ← expect Token.semi "session declaration terminator"
  let stopSpan ← peekSpan
  pure (Decl.sessionDecl sessionName typeParamsList recBinderOpt
    stepsList (Span.merge startSpan stopSpan))

/-- Parse one operation signature inside an `effect` block.
    Shape: `fn NAME(params) : RET_TYPE (with EFFECT_ROW)? ;` —
    like a regular fn signature but with no body.  The optional
    `with` clause declares effects the operation itself uses
    (e.g. an operation that internally needs `IO`).

    Reuses `parseFnParams`, the return-type path
    (`: <expr>`), and `parseOptionalEffectRow` — same sub-parsers
    as `parseFnDecl`, just without the `= body ;` or `begin fn
    ... end fn ;` tail.  Keeps the shape exactly parallel so
    the Phase-2 AST / elaborator picks up EffectOps the same
    way it does parameter telescopes. -/
partial def parseEffectOp : ParserM EffectOp := do
  let startSpan ← peekSpan
  let _ ← expectKw Keyword.fnKw "effect operation (expected 'fn')"
  let (opName, _) ← expectIdent "effect operation name"
  let paramsList ← parseFnParams
  let _ ← expect Token.colon "effect operation return-type ':'"
  let returnTypeExpr ← parseExpr
  let effectsList ← parseOptionalEffectRow
  let _ ← expect Token.semi "effect operation terminator"
  let stopSpan ← peekSpan
  pure (EffectOp.mk opName paramsList returnTypeExpr effectsList
    (Span.merge startSpan stopSpan))

/-- Accumulate `op+` until `end effect ;` closer.  Stops at any
    non-`fn` token — the caller (`parseEffectDecl`) verifies the
    closer shape.  Bailout: if EOF is reached before the closer,
    returns whatever has accumulated and lets `expectKw`
    downstream record the diagnostic.  Follows the
    position-progress discipline from Q51/Q52 —
    `parseEffectOp` advances through at least `fn`, so progress
    is structural. -/
partial def effectOpsLoop (opsSoFar : Array EffectOp)
    : ParserM (Array EffectOp) := do
  let currentToken ← peek
  match currentToken with
  | Token.eof             => pure opsSoFar
  | Token.kw Keyword.fnKw => do
    let nextOp ← parseEffectOp
    effectOpsLoop (opsSoFar.push nextOp)
  | _ => pure opsSoFar

/-- Parse `effect NAME<typeParams>? op+ end effect ;` per
    `fx_grammar.md §5.12` / `fx_design.md §9.5` (task E-4,
    parser half).

    Subsumption relations (`subsumes OtherEffect;`) are not
    parsed in this pass — they land with the elaborator half
    once the effect row becomes extensible and the subsumption
    edge has a place to register.  Bare effect blocks (ops
    only) are accepted; an encountered `subsumes` keyword
    today falls through to `effectOpsLoop`'s non-`fn` stop
    and surfaces later as a P-code via the closer check. -/
partial def parseEffectDecl : ParserM Decl := do
  let startSpan ← peekSpan
  let _ ← expectKw Keyword.effectKw "effect declaration"
  let nameTok ← peek
  let effectName ← match nameTok with
    | Token.uident uidentName =>
      let _ ← advance; pure uidentName
    | Token.ident identName =>
      -- Spec requires UIDENT (§2.3 / §9.1: effect names are
      -- PascalCase), but accept lower-case identifiers with a
      -- recorded error so the parser stays productive and
      -- downstream tools can still traverse the shape.
      let _ ← advance
      recordError "P040"
        s!"effect name must be PascalCase, got '{identName}'"
      pure identName
    | _ =>
      recordError "P039"
        s!"effect name: expected PascalCase identifier, found '{repr nameTok}'"
      pure "_error_effect"
  let typeParamsList ← parseOptionalTypeParams
  let opsList ← effectOpsLoop #[]
  let _ ← expectKw Keyword.endKw "end of effect"
  let _ ← expectKw Keyword.effectKw "end effect closer"
  let _ ← expect Token.semi "effect declaration terminator"
  let stopSpan ← peekSpan
  pure (Decl.effectDecl effectName typeParamsList opsList
    (Span.merge startSpan stopSpan))

/-- Parse a single top-level declaration.  Dispatches on the
    opening keyword after attrs + visibility have been consumed. -/
partial def parseDecl : ParserM Decl := do
  let attrs ← parseAttrs
  let visibility ← parseVisibility
  let currentToken ← peek
  match currentToken with
  | Token.kw Keyword.moduleKw   => parseModuleDecl
  | Token.kw Keyword.openKw     => parseOpenDecl
  | Token.kw Keyword.includeKw  => parseIncludeDecl
  | Token.kw Keyword.constKw    => parseConstDecl
  | Token.kw Keyword.valKw      => parseValDecl
  | Token.kw Keyword.typeKw     => parseTypeDecl attrs
  | Token.kw Keyword.fnKw       => parseFnDecl attrs visibility
  | Token.kw Keyword.implKw     => parseImplDecl
  | Token.kw Keyword.sessionKw  => parseSessionDecl
  | Token.kw Keyword.effectKw   => parseEffectDecl
  | Token.kw Keyword.sorryKw    => do
    let span ← peekSpan
    let _ ← advance
    let _ ← expect Token.semi "sorry declaration terminator"
    pure (Decl.sorryDecl span)
  | Token.kw k => do
    -- Recognized form we don't yet fully parse — swallow.
    let span ← peekSpan
    let _ ← advance
    let _ ← swallowToSync
    pure (Decl.unimplemented s!"decl kind '{k.toString}' not yet parsed" span)
  | _ => do
    recordError "P100" s!"expected declaration, found '{repr currentToken}'"
    let span ← peekSpan
    let _ ← swallowToSync
    pure (Decl.unimplemented "unrecognized declaration" span)

end  -- mutual (top-level helpers)

/-! ## File entry point -/

/-- Collect top-level declarations, skipping stray doc comments
    (the Phase-1 parser drops them; the elaborator attaches them
    later). -/
partial def declsLoop (declsSoFar : Array Decl) : ParserM (Array Decl) := do
  let parserState ← get
  if parserState.isAtEnd then
    pure declsSoFar
  else
    match parserState.peek.token with
    | Token.docComment _ =>
      set { parserState with pos := parserState.pos + 1 }
      declsLoop declsSoFar
    | _ =>
      let nextDecl ← parseDecl
      declsLoop (declsSoFar.push nextDecl)

/-- Parse a whole file.  Returns the `File` AST and an array of
    non-fatal errors. -/
def parseFile (tokens : Array LocatedToken)
    : File × Array FX.Util.Error :=
  let initialState : ParserState := { tokens := tokens }
  let (decls, finalState) := declsLoop #[] |>.run initialState
  let fileSpan : Span :=
    match tokens[0]?, tokens[tokens.size - 1]? with
    | some firstToken, some lastToken =>
      Span.merge firstToken.span lastToken.span
    | _, _ => Span.zero
  ({ decls := decls, span := fileSpan }, finalState.errors)

end FX.Syntax.Parser
