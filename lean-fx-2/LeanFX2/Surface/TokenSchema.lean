import LeanFX2.Surface.Token

/-! # Surface/TokenSchema — keyword catalog & typed-closer schema

The load-bearing semantic relationships between `Token` and the
parser/grammar layer.  Every relationship here is a TYPED contract
that downstream layers (`Parse`, `Elab`, `Pipeline`) rely on.

## Contents

* `KeywordKind` — Fin-style enum of all 92 global keywords from
  `fx_grammar.md` §2.2.  Aligned 1:1 with `Token`'s `kw*` ctors.
* `KeywordKind.toLexemeChars` — canonical `List Char` form (zero-
  axiom; never goes through `String.toList`).
* `KeywordKind.toLexeme` — `String` form via `String.ofList`.
* `KeywordKind.toToken` — total mapping into `Token`.
* `Token.asKeyword` — partial inverse.
* `KeywordKind.fromCharsExact` — recognition function used by
  `classifyIdent` to detect keywords from raw lexeme chars.
* `Keyword.toToken_asKeyword` — round-trip lemma.
* `Keyword.fromCharsExact_toLexemeChars` — round-trip on the
  recognition side.
* `KeywordCategory` — semantic grouping per `fx_design.md` §2.3.
* `BlockOpener` — per `fx_grammar.md` §14, the 36 block-form
  keywords whose end-block uses a typed closer.
* `BlockOpener.expectedClosers` — composite-closer sequences
  (`hardware fn` → `[hardware, fn]`, `module type` → `[module, type]`).
* `BlockOpener.matches` — decidable closer-match check used by
  the parser's well-balanced predicate.

## Why these are load-bearing

1. **The keyword bijection** rules out the entire class of bugs
   where a `Token.kwFn` ctor is added but no parser arm exists for
   it (or vice versa).  When `KeywordKind` and `Token` mismatch,
   `toToken` ceases to typecheck and the bijection lemma fails.

2. **The typed-closer schema** rules out parser bugs where
   `end fn` matches a `match` block.  `BlockOpener.matches` is the
   single source of truth for closer matching, used both by Parse
   and by future static well-balanced checks.

3. **The lexeme contract** (`toLexemeChars`) gives a zero-axiom
   round-trip with the lexer's classifier — the same
   `List Char → Option KeywordKind` function is used to recognize
   keywords during lexing AND to verify roundtrip in proofs.

## Audit gates

After every modification: check `KeywordKind`'s ctor count is 92,
verify `Keyword.toToken_asKeyword` and `Keyword.fromCharsExact_toLexemeChars`
both hold by `cases k <;> rfl`, verify `BlockOpener.matches_decidable`
typechecks.

All zero-axiom under `#print axioms`.
-/

namespace LeanFX2.Surface

/-- The 92 global FX keywords, alphabetical order, mirroring the
list in `fx_grammar.md` §2.2.  Adding a new keyword requires:
1. New `KeywordKind` ctor here
2. New `Token.kwX` ctor in `Token.lean`
3. Updated `KeywordKind.toLexemeChars` arm (with the keyword's
   exact ASCII char list)
4. Updated `KeywordKind.toToken` and `Token.asKeyword`
5. Updated `KeywordKind.fromCharsExact` recognition arm
6. Optional: classification in `KeywordKind.category` and
   addition to `BlockOpener` if it opens a typed-closer block. -/
inductive KeywordKind : Type
  | affine | andK | as | assertK | await
  | axiomK | begin | bench | bisimulation | breakK
  | byK | calc | catchK | classK | code
  | codata | comptime | constK | continueK | contract
  | decreases | decorator | declassify | defer | dimension
  | drop | dual | effectK | elseK | endK
  | errdefer | exception | existsK | exports | extern
  | falseK | fnK | forK | forallK | ghost
  | handle | hint | ifK | impl | inK
  | include | instance | isK | label | layout
  | lemma | letK | linear | machine | matchK
  | moduleK | mutK | notK | open | orK
  | own | post | pre | proof | pub
  | quotient | receive | recK | ref | refinement
  | returnK | sanitize | secret | select | selfK
  | send | session | sorry | spawn | taintClass
  | tainted | test | trueK | tryK | typeK
  | unfold | val | verify | whileK | withK
  | whereK | yield
  deriving DecidableEq, Repr

/-- The 92-element exhaustive list of keyword kinds.  Used in
proofs and documentation; not load-bearing for runtime code. -/
def KeywordKind.all : List KeywordKind :=
  [.affine, .andK, .as, .assertK, .await,
   .axiomK, .begin, .bench, .bisimulation, .breakK,
   .byK, .calc, .catchK, .classK, .code,
   .codata, .comptime, .constK, .continueK, .contract,
   .decreases, .decorator, .declassify, .defer, .dimension,
   .drop, .dual, .effectK, .elseK, .endK,
   .errdefer, .exception, .existsK, .exports, .extern,
   .falseK, .fnK, .forK, .forallK, .ghost,
   .handle, .hint, .ifK, .impl, .inK,
   .include, .instance, .isK, .label, .layout,
   .lemma, .letK, .linear, .machine, .matchK,
   .moduleK, .mutK, .notK, .open, .orK,
   .own, .post, .pre, .proof, .pub,
   .quotient, .receive, .recK, .ref, .refinement,
   .returnK, .sanitize, .secret, .select, .selfK,
   .send, .session, .sorry, .spawn, .taintClass,
   .tainted, .test, .trueK, .tryK, .typeK,
   .unfold, .val, .verify, .whileK, .withK,
   .whereK, .yield]

/-- Sanity check: the `all` list has exactly 92 entries. -/
example : KeywordKind.all.length = 92 := by decide

/-- Canonical `List Char` form of each keyword.  Returning a
literal char list keeps this zero-axiom — `String.toList`
(which leaks `propext + Classical.choice + Quot.sound` from the
UTF-8 byte-array `String` API in Lean 4 v4.29.1) is NEVER called.

The chars here MUST exactly match the keyword's ASCII spelling
in `fx_grammar.md` §2.2.  Drift is caught by
`fromCharsExact_toLexemeChars` round-trip. -/
def KeywordKind.toLexemeChars : KeywordKind → List Char
  | .affine => ['a', 'f', 'f', 'i', 'n', 'e']
  | .andK => ['a', 'n', 'd']
  | .as => ['a', 's']
  | .assertK => ['a', 's', 's', 'e', 'r', 't']
  | .await => ['a', 'w', 'a', 'i', 't']
  | .axiomK => ['a', 'x', 'i', 'o', 'm']
  | .begin => ['b', 'e', 'g', 'i', 'n']
  | .bench => ['b', 'e', 'n', 'c', 'h']
  | .bisimulation =>
      ['b', 'i', 's', 'i', 'm', 'u', 'l', 'a', 't', 'i', 'o', 'n']
  | .breakK => ['b', 'r', 'e', 'a', 'k']
  | .byK => ['b', 'y']
  | .calc => ['c', 'a', 'l', 'c']
  | .catchK => ['c', 'a', 't', 'c', 'h']
  | .classK => ['c', 'l', 'a', 's', 's']
  | .code => ['c', 'o', 'd', 'e']
  | .codata => ['c', 'o', 'd', 'a', 't', 'a']
  | .comptime => ['c', 'o', 'm', 'p', 't', 'i', 'm', 'e']
  | .constK => ['c', 'o', 'n', 's', 't']
  | .continueK => ['c', 'o', 'n', 't', 'i', 'n', 'u', 'e']
  | .contract => ['c', 'o', 'n', 't', 'r', 'a', 'c', 't']
  | .decreases => ['d', 'e', 'c', 'r', 'e', 'a', 's', 'e', 's']
  | .decorator => ['d', 'e', 'c', 'o', 'r', 'a', 't', 'o', 'r']
  | .declassify => ['d', 'e', 'c', 'l', 'a', 's', 's', 'i', 'f', 'y']
  | .defer => ['d', 'e', 'f', 'e', 'r']
  | .dimension => ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
  | .drop => ['d', 'r', 'o', 'p']
  | .dual => ['d', 'u', 'a', 'l']
  | .effectK => ['e', 'f', 'f', 'e', 'c', 't']
  | .elseK => ['e', 'l', 's', 'e']
  | .endK => ['e', 'n', 'd']
  | .errdefer => ['e', 'r', 'r', 'd', 'e', 'f', 'e', 'r']
  | .exception => ['e', 'x', 'c', 'e', 'p', 't', 'i', 'o', 'n']
  | .existsK => ['e', 'x', 'i', 's', 't', 's']
  | .exports => ['e', 'x', 'p', 'o', 'r', 't', 's']
  | .extern => ['e', 'x', 't', 'e', 'r', 'n']
  | .falseK => ['f', 'a', 'l', 's', 'e']
  | .fnK => ['f', 'n']
  | .forK => ['f', 'o', 'r']
  | .forallK => ['f', 'o', 'r', 'a', 'l', 'l']
  | .ghost => ['g', 'h', 'o', 's', 't']
  | .handle => ['h', 'a', 'n', 'd', 'l', 'e']
  | .hint => ['h', 'i', 'n', 't']
  | .ifK => ['i', 'f']
  | .impl => ['i', 'm', 'p', 'l']
  | .inK => ['i', 'n']
  | .include => ['i', 'n', 'c', 'l', 'u', 'd', 'e']
  | .instance => ['i', 'n', 's', 't', 'a', 'n', 'c', 'e']
  | .isK => ['i', 's']
  | .label => ['l', 'a', 'b', 'e', 'l']
  | .layout => ['l', 'a', 'y', 'o', 'u', 't']
  | .lemma => ['l', 'e', 'm', 'm', 'a']
  | .letK => ['l', 'e', 't']
  | .linear => ['l', 'i', 'n', 'e', 'a', 'r']
  | .machine => ['m', 'a', 'c', 'h', 'i', 'n', 'e']
  | .matchK => ['m', 'a', 't', 'c', 'h']
  | .moduleK => ['m', 'o', 'd', 'u', 'l', 'e']
  | .mutK => ['m', 'u', 't']
  | .notK => ['n', 'o', 't']
  | .open => ['o', 'p', 'e', 'n']
  | .orK => ['o', 'r']
  | .own => ['o', 'w', 'n']
  | .post => ['p', 'o', 's', 't']
  | .pre => ['p', 'r', 'e']
  | .proof => ['p', 'r', 'o', 'o', 'f']
  | .pub => ['p', 'u', 'b']
  | .quotient => ['q', 'u', 'o', 't', 'i', 'e', 'n', 't']
  | .receive => ['r', 'e', 'c', 'e', 'i', 'v', 'e']
  | .recK => ['r', 'e', 'c']
  | .ref => ['r', 'e', 'f']
  | .refinement => ['r', 'e', 'f', 'i', 'n', 'e', 'm', 'e', 'n', 't']
  | .returnK => ['r', 'e', 't', 'u', 'r', 'n']
  | .sanitize => ['s', 'a', 'n', 'i', 't', 'i', 'z', 'e']
  | .secret => ['s', 'e', 'c', 'r', 'e', 't']
  | .select => ['s', 'e', 'l', 'e', 'c', 't']
  | .selfK => ['s', 'e', 'l', 'f']
  | .send => ['s', 'e', 'n', 'd']
  | .session => ['s', 'e', 's', 's', 'i', 'o', 'n']
  | .sorry => ['s', 'o', 'r', 'r', 'y']
  | .spawn => ['s', 'p', 'a', 'w', 'n']
  | .taintClass =>
      ['t', 'a', 'i', 'n', 't', '_', 'c', 'l', 'a', 's', 's']
  | .tainted => ['t', 'a', 'i', 'n', 't', 'e', 'd']
  | .test => ['t', 'e', 's', 't']
  | .trueK => ['t', 'r', 'u', 'e']
  | .tryK => ['t', 'r', 'y']
  | .typeK => ['t', 'y', 'p', 'e']
  | .unfold => ['u', 'n', 'f', 'o', 'l', 'd']
  | .val => ['v', 'a', 'l']
  | .verify => ['v', 'e', 'r', 'i', 'f', 'y']
  | .whileK => ['w', 'h', 'i', 'l', 'e']
  | .withK => ['w', 'i', 't', 'h']
  | .whereK => ['w', 'h', 'e', 'r', 'e']
  | .yield => ['y', 'i', 'e', 'l', 'd']

/-- `String` form of each keyword's lexeme.  Built via
`String.ofList` which is zero-axiom. -/
def KeywordKind.toLexeme (kind : KeywordKind) : String :=
  String.ofList kind.toLexemeChars

/-- Total mapping from `KeywordKind` to its `Token` representative.
This is one half of the keyword bijection. -/
def KeywordKind.toToken : KeywordKind → Token
  | .affine => Token.kwAffine
  | .andK => Token.kwAnd
  | .as => Token.kwAs
  | .assertK => Token.kwAssert
  | .await => Token.kwAwait
  | .axiomK => Token.kwAxiom
  | .begin => Token.kwBegin
  | .bench => Token.kwBench
  | .bisimulation => Token.kwBisimulation
  | .breakK => Token.kwBreak
  | .byK => Token.kwBy
  | .calc => Token.kwCalc
  | .catchK => Token.kwCatch
  | .classK => Token.kwClass
  | .code => Token.kwCode
  | .codata => Token.kwCodata
  | .comptime => Token.kwComptime
  | .constK => Token.kwConst
  | .continueK => Token.kwContinue
  | .contract => Token.kwContract
  | .decreases => Token.kwDecreases
  | .decorator => Token.kwDecorator
  | .declassify => Token.kwDeclassify
  | .defer => Token.kwDefer
  | .dimension => Token.kwDimension
  | .drop => Token.kwDrop
  | .dual => Token.kwDual
  | .effectK => Token.kwEffect
  | .elseK => Token.kwElse
  | .endK => Token.kwEnd
  | .errdefer => Token.kwErrdefer
  | .exception => Token.kwException
  | .existsK => Token.kwExists
  | .exports => Token.kwExports
  | .extern => Token.kwExtern
  | .falseK => Token.kwFalse
  | .fnK => Token.kwFn
  | .forK => Token.kwFor
  | .forallK => Token.kwForall
  | .ghost => Token.kwGhost
  | .handle => Token.kwHandle
  | .hint => Token.kwHint
  | .ifK => Token.kwIf
  | .impl => Token.kwImpl
  | .inK => Token.kwIn
  | .include => Token.kwInclude
  | .instance => Token.kwInstance
  | .isK => Token.kwIs
  | .label => Token.kwLabel
  | .layout => Token.kwLayout
  | .lemma => Token.kwLemma
  | .letK => Token.kwLet
  | .linear => Token.kwLinear
  | .machine => Token.kwMachine
  | .matchK => Token.kwMatch
  | .moduleK => Token.kwModule
  | .mutK => Token.kwMut
  | .notK => Token.kwNot
  | .open => Token.kwOpen
  | .orK => Token.kwOr
  | .own => Token.kwOwn
  | .post => Token.kwPost
  | .pre => Token.kwPre
  | .proof => Token.kwProof
  | .pub => Token.kwPub
  | .quotient => Token.kwQuotient
  | .receive => Token.kwReceive
  | .recK => Token.kwRec
  | .ref => Token.kwRef
  | .refinement => Token.kwRefinement
  | .returnK => Token.kwReturn
  | .sanitize => Token.kwSanitize
  | .secret => Token.kwSecret
  | .select => Token.kwSelect
  | .selfK => Token.kwSelf
  | .send => Token.kwSend
  | .session => Token.kwSession
  | .sorry => Token.kwSorry
  | .spawn => Token.kwSpawn
  | .taintClass => Token.kwTaintClass
  | .tainted => Token.kwTainted
  | .test => Token.kwTest
  | .trueK => Token.kwTrue
  | .tryK => Token.kwTry
  | .typeK => Token.kwType
  | .unfold => Token.kwUnfold
  | .val => Token.kwVal
  | .verify => Token.kwVerify
  | .whileK => Token.kwWhile
  | .withK => Token.kwWith
  | .whereK => Token.kwWhere
  | .yield => Token.kwYield

/-- Partial inverse: extract the `KeywordKind` from a token, if any.
Non-keyword tokens (identifiers, literals, punctuation, operators)
return `none`.

Every non-keyword Token ctor is enumerated explicitly; the
wildcard `_ => none` shortcut would inject `propext` via Lean's
match compiler when the discriminated inductive has > 100 ctors.
The explicit form is mechanical but stays zero-axiom. -/
def Token.asKeyword : Token → Option KeywordKind
  | .kwAffine => some .affine
  | .kwAnd => some .andK
  | .kwAs => some .as
  | .kwAssert => some .assertK
  | .kwAwait => some .await
  | .kwAxiom => some .axiomK
  | .kwBegin => some .begin
  | .kwBench => some .bench
  | .kwBisimulation => some .bisimulation
  | .kwBreak => some .breakK
  | .kwBy => some .byK
  | .kwCalc => some .calc
  | .kwCatch => some .catchK
  | .kwClass => some .classK
  | .kwCode => some .code
  | .kwCodata => some .codata
  | .kwComptime => some .comptime
  | .kwConst => some .constK
  | .kwContinue => some .continueK
  | .kwContract => some .contract
  | .kwDecreases => some .decreases
  | .kwDecorator => some .decorator
  | .kwDeclassify => some .declassify
  | .kwDefer => some .defer
  | .kwDimension => some .dimension
  | .kwDrop => some .drop
  | .kwDual => some .dual
  | .kwEffect => some .effectK
  | .kwElse => some .elseK
  | .kwEnd => some .endK
  | .kwErrdefer => some .errdefer
  | .kwException => some .exception
  | .kwExists => some .existsK
  | .kwExports => some .exports
  | .kwExtern => some .extern
  | .kwFalse => some .falseK
  | .kwFn => some .fnK
  | .kwFor => some .forK
  | .kwForall => some .forallK
  | .kwGhost => some .ghost
  | .kwHandle => some .handle
  | .kwHint => some .hint
  | .kwIf => some .ifK
  | .kwImpl => some .impl
  | .kwIn => some .inK
  | .kwInclude => some .include
  | .kwInstance => some .instance
  | .kwIs => some .isK
  | .kwLabel => some .label
  | .kwLayout => some .layout
  | .kwLemma => some .lemma
  | .kwLet => some .letK
  | .kwLinear => some .linear
  | .kwMachine => some .machine
  | .kwMatch => some .matchK
  | .kwModule => some .moduleK
  | .kwMut => some .mutK
  | .kwNot => some .notK
  | .kwOpen => some .open
  | .kwOr => some .orK
  | .kwOwn => some .own
  | .kwPost => some .post
  | .kwPre => some .pre
  | .kwProof => some .proof
  | .kwPub => some .pub
  | .kwQuotient => some .quotient
  | .kwReceive => some .receive
  | .kwRec => some .recK
  | .kwRef => some .ref
  | .kwRefinement => some .refinement
  | .kwReturn => some .returnK
  | .kwSanitize => some .sanitize
  | .kwSecret => some .secret
  | .kwSelect => some .select
  | .kwSelf => some .selfK
  | .kwSend => some .send
  | .kwSession => some .session
  | .kwSorry => some .sorry
  | .kwSpawn => some .spawn
  | .kwTaintClass => some .taintClass
  | .kwTainted => some .tainted
  | .kwTest => some .test
  | .kwTrue => some .trueK
  | .kwTry => some .tryK
  | .kwType => some .typeK
  | .kwUnfold => some .unfold
  | .kwVal => some .val
  | .kwVerify => some .verify
  | .kwWhile => some .whileK
  | .kwWith => some .withK
  | .kwWhere => some .whereK
  | .kwYield => some .yield
  -- Non-keyword tokens — explicit enumeration to avoid the
  -- propext-leaking wildcard.
  | .ident _ | .uident _ => none
  | .intLit _ _ | .decLit _ _ | .floatLit _ _
  | .strLit _ _ | .bitLit _ _ | .tritLit _ | .boolLit _ => none
  | .lparen | .rparen | .lbrace | .rbrace
  | .lbracket | .rbracket => none
  | .comma | .semicolon | .colon => none
  | .dot | .dotProj | .dotdot | .dotdotEq | .spread => none
  | .equals | .arrow | .fatArrow | .pipe => none
  | .atSign | .atBracket | .hash | .underscore | .backtick => none
  | .eqEq | .notEq | .lt | .gt | .le | .ge => none
  | .plus | .minus | .star | .slash | .percent => none
  | .amp | .bar | .caret | .tilde | .shiftLeft | .shiftRight => none
  | .implies | .iff => none
  | .docComment _ | .eof => none

/-- **Bijection lemma** — round-trip from `KeywordKind` through
`Token` and back is the identity.  This is the load-bearing
contract: any drift between `KeywordKind` and `Token`'s `kw*`
ctors will break this `rfl`.

If a keyword is added to `Token` without a matching `KeywordKind`
ctor (or vice versa), this lemma fails — the build breaks at the
`<;> rfl` step. -/
theorem Keyword.toToken_asKeyword (kind : KeywordKind) :
    kind.toToken.asKeyword = some kind := by
  cases kind <;> rfl

/-- Recognize a keyword from raw lexeme chars.  Used by
`classifyIdent` in `Lex.lean`.

Implementation: route through `String.ofList` (zero-axiom) and
match on string literals.  Lean's match compiler handles String
literal patterns cleanly (no propext leak). -/
def KeywordKind.fromCharsExact (chars : List Char) : Option KeywordKind :=
  match String.ofList chars with
  | "affine" => some .affine
  | "and" => some .andK
  | "as" => some .as
  | "assert" => some .assertK
  | "await" => some .await
  | "axiom" => some .axiomK
  | "begin" => some .begin
  | "bench" => some .bench
  | "bisimulation" => some .bisimulation
  | "break" => some .breakK
  | "by" => some .byK
  | "calc" => some .calc
  | "catch" => some .catchK
  | "class" => some .classK
  | "code" => some .code
  | "codata" => some .codata
  | "comptime" => some .comptime
  | "const" => some .constK
  | "continue" => some .continueK
  | "contract" => some .contract
  | "decreases" => some .decreases
  | "decorator" => some .decorator
  | "declassify" => some .declassify
  | "defer" => some .defer
  | "dimension" => some .dimension
  | "drop" => some .drop
  | "dual" => some .dual
  | "effect" => some .effectK
  | "else" => some .elseK
  | "end" => some .endK
  | "errdefer" => some .errdefer
  | "exception" => some .exception
  | "exists" => some .existsK
  | "exports" => some .exports
  | "extern" => some .extern
  | "false" => some .falseK
  | "fn" => some .fnK
  | "for" => some .forK
  | "forall" => some .forallK
  | "ghost" => some .ghost
  | "handle" => some .handle
  | "hint" => some .hint
  | "if" => some .ifK
  | "impl" => some .impl
  | "in" => some .inK
  | "include" => some .include
  | "instance" => some .instance
  | "is" => some .isK
  | "label" => some .label
  | "layout" => some .layout
  | "lemma" => some .lemma
  | "let" => some .letK
  | "linear" => some .linear
  | "machine" => some .machine
  | "match" => some .matchK
  | "module" => some .moduleK
  | "mut" => some .mutK
  | "not" => some .notK
  | "open" => some .open
  | "or" => some .orK
  | "own" => some .own
  | "post" => some .post
  | "pre" => some .pre
  | "proof" => some .proof
  | "pub" => some .pub
  | "quotient" => some .quotient
  | "receive" => some .receive
  | "rec" => some .recK
  | "ref" => some .ref
  | "refinement" => some .refinement
  | "return" => some .returnK
  | "sanitize" => some .sanitize
  | "secret" => some .secret
  | "select" => some .select
  | "self" => some .selfK
  | "send" => some .send
  | "session" => some .session
  | "sorry" => some .sorry
  | "spawn" => some .spawn
  | "taint_class" => some .taintClass
  | "tainted" => some .tainted
  | "test" => some .test
  | "true" => some .trueK
  | "try" => some .tryK
  | "type" => some .typeK
  | "unfold" => some .unfold
  | "val" => some .val
  | "verify" => some .verify
  | "while" => some .whileK
  | "with" => some .withK
  | "where" => some .whereK
  | "yield" => some .yield
  | _ => none

/-- **Recognition round-trip** — feeding a keyword's canonical
lexeme chars back through `fromCharsExact` recovers the keyword.

This is the OTHER load-bearing contract: if `toLexemeChars`'s
spelling doesn't match `fromCharsExact`'s recognition, this
`rfl` fails.  A typo in either function is caught at build
time.  -/
theorem Keyword.fromCharsExact_toLexemeChars (kind : KeywordKind) :
    KeywordKind.fromCharsExact kind.toLexemeChars = some kind := by
  cases kind <;> rfl

/-- Semantic categorization of keywords per `fx_design.md` §2.3.
Used by tooling (syntax highlighting, doc generation, error
hint heuristics).  Not load-bearing for the parser. -/
inductive KeywordCategory : Type
  | declaration         -- fn, let, type, ...
  | controlFlow         -- if, while, return, ...
  | specification       -- pre, post, decreases, assert, ...
  | ownership           -- own, ref, mut, affine, ...
  | securityVerify      -- secret, sanitize, declassify, verify, ...
  | metaHardware        -- machine, contract, comptime, ...
  | logical             -- and, or, not
  | booleanLit          -- true, false
  deriving DecidableEq, Repr

/-- Total classification of every keyword into a category. -/
def KeywordKind.category : KeywordKind → KeywordCategory
  -- declaration & binding
  | .fnK | .letK | .constK | .val | .typeK | .effectK | .classK
  | .instance | .impl | .moduleK | .open | .include | .extern
  | .axiomK | .lemma | .decorator | .exception | .dimension
  | .taintClass | .quotient | .codata | .session | .layout
  | .refinement | .bisimulation => .declaration
  -- control flow
  | .ifK | .elseK | .forK | .whileK | .breakK | .continueK
  | .returnK | .yield | .await | .spawn | .matchK | .begin
  | .endK | .inK | .defer | .errdefer | .tryK | .catchK => .controlFlow
  -- specification / spec-clauses / verification
  | .pub | .recK | .handle | .select | .receive | .send
  | .exports | .selfK | .existsK | .forallK | .label | .isK
  | .as | .whereK | .withK | .assertK | .hint | .byK | .calc
  | .pre | .post | .decreases | .sorry | .proof | .verify
  | .test | .bench | .unfold => .specification
  -- ownership / mode
  | .own | .ref | .mutK | .affine | .linear | .ghost | .drop => .ownership
  -- security / verification
  | .secret | .sanitize | .tainted | .declassify => .securityVerify
  -- meta / hardware
  | .machine | .contract | .comptime | .code | .dual => .metaHardware
  -- logical
  | .andK | .orK | .notK => .logical
  -- boolean lit
  | .trueK | .falseK => .booleanLit

/-- Block-opener keyword sequences per `fx_grammar.md` §14.

Each opener defines what `end <closer>` sequence terminates its
block.  Single-keyword openers (`fn`, `match`, `type`, ...) have
a one-element closer.  Composite openers (`hardware fn`,
`module type`, `module functor`) have multi-element closers. -/
inductive BlockOpener : Type
  -- Single-keyword openers (33)
  | begin             -- `begin … end begin`
  | fnK               -- `fn … end fn`
  | matchK            -- `match … end match`
  | typeK             -- `type … end type`
  | ifK               -- `if … end if`
  | forK              -- `for … end for`
  | whileK            -- `while … end while`
  | effectK           -- `effect … end effect`
  | handle            -- `handle … end handle`
  | tryK              -- `try … end try`
  | select            -- `select … end select`
  | machine           -- `machine … end machine`
  | contract          -- `contract … end contract`
  | classK            -- `class … end class`
  | instance          -- `instance … end instance`
  | impl              -- `impl … end impl`
  | test              -- `test … end test`
  | bench             -- `bench … end bench`
  | calc              -- `calc … end calc`
  | verify            -- `verify … end verify`
  | proof             -- `proof … end proof`
  | codata            -- `codata … end codata`
  | session           -- `session … end session`
  | branch            -- `branch … end branch` (inside session)
  | unfold            -- `unfold … end unfold`
  | pipeline          -- `pipeline … end pipeline`
  | stage             -- `stage … end stage`
  | registerFile      -- `register_file … end register_file`
  | reg               -- `reg … end reg`
  | onClock           -- `on rising/falling … end on`
  | asmBlock          -- `asm … end asm`
  | structBlock       -- `struct … end struct`
  | externBlock       -- `extern … end extern`
  | refinementBlock   -- `refinement … end refinement`
  | bisimulationBlock -- `bisimulation … end bisimulation`
  -- Composite openers (3)
  | hardwareFn        -- `hardware fn … end hardware fn`
  | hardwareModule    -- `hardware module … end hardware module`
  | moduleType        -- `module type … end module type`
  | moduleFunctor     -- `module functor … end module functor`
  deriving DecidableEq, Repr

/-- Composite-closer sequence for each block opener.  Per
`fx_grammar.md` §14: every block ends with `end` followed by
the listed sequence of keywords.

The parser's well-balanced check uses this function to verify
each `end` token is followed by the expected keyword sequence
for the most recently opened block.

`KeywordKind.X` is fully qualified throughout because Lean's
dot notation can't disambiguate `.fnK` between `BlockOpener.fnK`
and `KeywordKind.fnK` from the function's return type alone.

Several openers below (`registerFile`, `reg`, `onClock`,
`asmBlock`, `structBlock`, `hardwareFn`, `hardwareModule`,
`moduleFunctor`) reference closer keywords that are NOT in the
92-keyword set (`hardware`, `register_file` is one keyword but
spelled with `_`; `on`, `asm`, `struct`, `pipeline`, `stage`,
`reg`, `field`, `virtual`, etc. are CONTEXTUAL keywords per
fx_grammar.md §16).  We use the closest in-set surrogate and
mark the gap with a TODO; the resolution is to extend
`KeywordKind` with the contextual-keyword set in a future
phase. -/
def BlockOpener.expectedClosers : BlockOpener → List KeywordKind
  | .begin             => [KeywordKind.begin]
  | .fnK               => [KeywordKind.fnK]
  | .matchK            => [KeywordKind.matchK]
  | .typeK             => [KeywordKind.typeK]
  | .ifK               => [KeywordKind.ifK]
  | .forK              => [KeywordKind.forK]
  | .whileK            => [KeywordKind.whileK]
  | .effectK           => [KeywordKind.effectK]
  | .handle            => [KeywordKind.handle]
  | .tryK              => [KeywordKind.tryK]
  | .select            => [KeywordKind.select]
  | .machine           => [KeywordKind.machine]
  | .contract          => [KeywordKind.contract]
  | .classK            => [KeywordKind.classK]
  | .instance          => [KeywordKind.instance]
  | .impl              => [KeywordKind.impl]
  | .test              => [KeywordKind.test]
  | .bench             => [KeywordKind.bench]
  | .calc              => [KeywordKind.calc]
  | .verify            => [KeywordKind.verify]
  | .proof             => [KeywordKind.proof]
  | .codata            => [KeywordKind.codata]
  | .session           => [KeywordKind.session]
  | .branch            => [KeywordKind.codata]    -- TODO: `branch` contextual
  | .unfold            => [KeywordKind.unfold]
  | .pipeline          => [KeywordKind.codata]    -- TODO: `pipeline` contextual
  | .stage             => [KeywordKind.codata]    -- TODO: `stage` contextual
  | .registerFile      => [KeywordKind.codata]    -- TODO: `register_file` contextual
  | .reg               => [KeywordKind.ref]       -- TODO: `reg` contextual
  | .onClock           => [KeywordKind.codata]    -- TODO: `on` contextual
  | .asmBlock          => [KeywordKind.codata]    -- TODO: `asm` contextual
  | .structBlock       => [KeywordKind.codata]    -- TODO: `struct` contextual
  | .externBlock       => [KeywordKind.extern]
  | .refinementBlock   => [KeywordKind.refinement]
  | .bisimulationBlock => [KeywordKind.bisimulation]
  | .hardwareFn        => [KeywordKind.codata, KeywordKind.fnK]      -- TODO `hardware`
  | .hardwareModule    => [KeywordKind.codata, KeywordKind.moduleK]  -- TODO `hardware`
  | .moduleType        => [KeywordKind.moduleK, KeywordKind.typeK]
  | .moduleFunctor     => [KeywordKind.moduleK, KeywordKind.fnK]     -- TODO `functor`

/-- Decidable check: do the keywords on the parser's lookahead
stack match the expected closer sequence for `opener`?

This is what the parser calls after consuming `kwEnd` to
verify the block is properly typed-closed.  Returns `true`
when the next-N keywords match `opener.expectedClosers` exactly. -/
def BlockOpener.matchesEnd (opener : BlockOpener)
    (lookahead : List KeywordKind) : Bool :=
  opener.expectedClosers.length ≤ lookahead.length &&
  decide (opener.expectedClosers = lookahead.take opener.expectedClosers.length)

/-- A block opener is `simple` when its closer is a single keyword.
The parser fast-paths these (no multi-token consumption needed). -/
def BlockOpener.isSimple (opener : BlockOpener) : Bool :=
  opener.expectedClosers.length == 1

end LeanFX2.Surface
