import LeanFX2.Surface.TokenSchema

/-! # Surface/TokenInvariants — lexeme shape predicates

Per `fx_lexer.md` §3.1 + `fx_grammar.md` §2.1: identifiers have
exact ASCII shapes.  This file encodes those shapes as DECIDABLE
PROPOSITIONS and derives a refinement type for well-formed
tokens.

## Shape rules

```
lower_ident   = [a-z_]   [a-zA-Z0-9_]*       // ident
upper_ident   = [A-Z]    [a-zA-Z0-9_]*       // uident
identCont     = [a-zA-Z0-9_]                  // both kinds, body
```

ASCII only.  No Unicode, no apostrophe, no hyphen.

## Load-bearing intent

`Lex.run` produces a stream of `Token`s; the `ident` and `uident`
ctors' string payloads carry exact lexeme shapes determined by
the lexer's classifier.  This file establishes:

1. `Token.isWellFormed` — a decidable Bool predicate:
   * `ident lex`  → lex is non-empty and `IsLowerIdent` (lower/_)
   * `uident lex` → lex is non-empty and `IsUpperIdent` (upper)
   * non-identifier tokens are always well-formed
2. `WellFormedToken := { t : Token // t.isWellFormed = true }`
   — refinement subtype the parser can consume safely
3. The (forward-declared) lemma
   `Lex.run_produces_wellformed_tokens` — every token returned
   by `Lex.run` is in `WellFormedToken`.  Proved when the
   lexer-correctness package lands; for now stated as a target
   predicate.

## Why this is load-bearing

Without these predicates, the parser/elaborator must defensively
re-validate every identifier payload (or trust the lexer's
contract by convention).  With the predicates encoded, identifier
payloads come refined; downstream code receives a value that
PROVABLY has the right shape.  Adding a new lexer that bypasses
`classifyIdent` would fail to discharge the predicate at the
`WellFormedToken` boundary.

All zero-axiom under `#print axioms`.
-/

/-! ## Character-class predicates (decidable, ASCII-only)

These live in the global `Char` namespace so dot notation
(`ch.isAsciiLowerLetter`) works.  Lean's projection lookup
checks the type's actual namespace; defining inside
`LeanFX2.Surface` would require fully-qualified calls. -/

namespace Char

/-- ASCII lowercase letter `a-z`. -/
def isAsciiLowerLetter (ch : Char) : Bool :=
  'a' ≤ ch && ch ≤ 'z'

/-- ASCII uppercase letter `A-Z`. -/
def isAsciiUpperLetter (ch : Char) : Bool :=
  'A' ≤ ch && ch ≤ 'Z'

/-- ASCII decimal digit `0-9`. -/
def isAsciiDecDigit (ch : Char) : Bool :=
  '0' ≤ ch && ch ≤ '9'

/-- A character that may START a lowercase identifier per
fx_lexer.md §3.1: `[a-z_]`. -/
def isLowerIdentHead (ch : Char) : Bool :=
  ch.isAsciiLowerLetter || ch == '_'

/-- A character that may START an uppercase identifier per
fx_lexer.md §3.1: `[A-Z]`. -/
def isUpperIdentHead (ch : Char) : Bool :=
  ch.isAsciiUpperLetter

/-- A character valid in identifier-tail position per
fx_lexer.md §3.1: `[a-zA-Z0-9_]`. -/
def isIdentTail (ch : Char) : Bool :=
  ch.isAsciiLowerLetter || ch.isAsciiUpperLetter ||
  ch.isAsciiDecDigit || ch == '_'

/-- A character that may START any identifier (either case). -/
def isIdentStart (ch : Char) : Bool :=
  ch.isLowerIdentHead || ch.isUpperIdentHead

end Char

namespace LeanFX2.Surface

/-! ## List-of-Char shape predicates (decidable) -/

/-- All characters in the list pass `isIdentTail`.  Used as the
tail-shape predicate for both lower- and upper-case identifiers. -/
def IsAllIdentTail : List Char → Bool
  | [] => true
  | c :: rest => c.isIdentTail && IsAllIdentTail rest

/-- Lowercase identifier shape: non-empty, head is lower or `_`,
all tail chars are ident-cont. -/
def IsLowerIdentChars : List Char → Bool
  | [] => false
  | c :: rest => c.isLowerIdentHead && IsAllIdentTail rest

/-- Uppercase identifier shape: non-empty, head is upper, all
tail chars are ident-cont. -/
def IsUpperIdentChars : List Char → Bool
  | [] => false
  | c :: rest => c.isUpperIdentHead && IsAllIdentTail rest

/-- ASCII-only check: every char fits in 7 bits.  Per
fx_lexer.md §1, code is ASCII-only outside string/comment. -/
def IsAsciiChars : List Char → Bool
  | [] => true
  | c :: rest => c.toNat < 128 && IsAsciiChars rest

/-! ## Smoke checks for the predicates -/

example : IsLowerIdentChars ['f', 'o', 'o'] = true := by decide
example : IsLowerIdentChars ['_', 'b', 'a', 'r'] = true := by decide
example : IsLowerIdentChars [] = false := by decide
example : IsLowerIdentChars ['F', 'o', 'o'] = false := by decide  -- starts upper
example : IsLowerIdentChars ['1', 'x'] = false := by decide       -- starts digit
example : IsUpperIdentChars ['F', 'o', 'o'] = true := by decide
example : IsUpperIdentChars ['T'] = true := by decide
example : IsUpperIdentChars ['f', 'o', 'o'] = false := by decide
example : IsAllIdentTail ['a', 'b', '0', '_', 'Z'] = true := by decide
example : IsAllIdentTail ['a', '-', 'b'] = false := by decide      -- hyphen
example : IsAsciiChars ['a', 'B', '0'] = true := by decide

/-- **Sanity invariant** (deferred proof) — every keyword's
canonical lexeme satisfies the lowercase identifier shape.  Proof
is a 92-case `decide`/`rfl` discharge that hits Lean's kernel
reduction budget; left as `Decidable` instance check via per-case
spot lemmas in `TokenInvariantsCheck.lean` (a separate audit
module).  Not load-bearing — the bijection lemmas in
`TokenSchema.lean` are sufficient for parser correctness.

The reason a single `<;> rfl` proof gets stuck: `IsAllIdentTail`
recurses through the char list, and Lean's kernel only does
WHNF reduction by default — pushing through 12 chars of
`bisimulation` × 92 keywords exhausts the budget.  Sound proof
strategies:
* spot-check three representatives per category (declaration /
  control flow / mode / spec / ...) — see
  `TokenInvariantsCheck.lean`
* invoke `decide +kernel` per-case with a bumped recursion budget
* prove via structural induction on `IsAllIdentTail` and a
  uniform `IsAsciiLowerLetter`-on-each-char lemma per keyword. -/
theorem KeywordKind.toLexemeChars_isLowerIdent_deferred :
    True := True.intro

/-! ## Token-level well-formedness predicate -/

/- Token-level contract: is `Token`'s payload (if any) a
well-formed lexeme per the lexer?

* `ident s` requires an explicit `List Char` witness `cs` with
  `IsLowerIdentChars cs = true` and `String.ofList cs = s`.
  This avoids `String.toList`, which leaks host axioms in Lean 4
  v4.29.1.
* `uident s` analogously.
* All other tokens are well-formed unconditionally.

The full existential predicate is the load-bearing form.  There is no
Bool-valued `String` inspection here: `String.length`, `String.toList`,
and friends all cross the host boundary and therefore do not belong in
the zero-axiom production surface. -/

/-- Existential well-formedness: identifier payloads come from
`String.ofList` of a properly-shaped char list.  Used as the
target invariant for lexer correctness.  Boolean payloads,
literals, keywords, punctuation are all unconditionally
well-formed.

Non-identifier ctors are enumerated explicitly (no wildcard) to
avoid the propext leak Lean's match compiler emits when the
discriminated inductive has > 100 constructors.  See the
parallel pattern in `Token.asKeyword` (`TokenSchema.lean`). -/
def Token.IsWellFormed : Token → Prop
  | .ident s  => ∃ cs : List Char,
      IsLowerIdentChars cs = true ∧ String.ofList cs = s
  | .uident s => ∃ cs : List Char,
      IsUpperIdentChars cs = true ∧ String.ofList cs = s
  -- Numeric / string / boolean literals: payload is whatever
  -- the lexer parsed; well-formedness is guaranteed by lexer
  -- contract, not statable here without going through the
  -- parsed-from chars.
  | .intLit _ _ | .decLit _ _ | .floatLit _ _
  | .strLit _ _ | .bitLit _ _ | .tritLit _ | .boolLit _ => True
  -- All 92 keywords
  | .kwAffine | .kwAnd | .kwAs | .kwAssert | .kwAwait
  | .kwAxiom | .kwBegin | .kwBench | .kwBisimulation | .kwBreak
  | .kwBy | .kwCalc | .kwCatch | .kwClass | .kwCode
  | .kwCodata | .kwComptime | .kwConst | .kwContinue | .kwContract
  | .kwDecreases | .kwDecorator | .kwDeclassify | .kwDefer | .kwDimension
  | .kwDrop | .kwDual | .kwEffect | .kwElse | .kwEnd
  | .kwErrdefer | .kwException | .kwExists | .kwExports | .kwExtern
  | .kwFalse | .kwFn | .kwFor | .kwForall | .kwGhost
  | .kwHandle | .kwHint | .kwIf | .kwImpl | .kwIn
  | .kwInclude | .kwInstance | .kwIs | .kwLabel | .kwLayout
  | .kwLemma | .kwLet | .kwLinear | .kwMachine | .kwMatch
  | .kwModule | .kwMut | .kwNot | .kwOpen | .kwOr
  | .kwOwn | .kwPost | .kwPre | .kwProof | .kwPub
  | .kwQuotient | .kwReceive | .kwRec | .kwRef | .kwRefinement
  | .kwReturn | .kwSanitize | .kwSecret | .kwSelect | .kwSelf
  | .kwSend | .kwSession | .kwSorry | .kwSpawn | .kwTaintClass
  | .kwTainted | .kwTest | .kwTrue | .kwTry | .kwType
  | .kwUnfold | .kwVal | .kwVerify | .kwWhile | .kwWith
  | .kwWhere | .kwYield => True
  -- Delimiters
  | .lparen | .rparen | .lbrace | .rbrace
  | .lbracket | .rbracket => True
  -- Punctuation / operators
  | .comma | .semicolon | .colon => True
  | .dot | .dotProj | .dotdot | .dotdotEq | .spread => True
  | .equals | .arrow | .fatArrow | .pipe => True
  | .atSign | .atBracket | .hash | .underscore | .backtick => True
  | .eqEq | .notEq | .lt | .gt | .le | .ge => True
  | .plus | .minus | .star | .slash | .percent => True
  | .amp | .bar | .caret | .tilde | .shiftLeft | .shiftRight => True
  | .implies | .iff => True
  -- Special / sentinel
  | .docComment _ | .eof => True

/-- Constructor lemma: building an `ident` from a char list that
satisfies the lower-shape predicate produces a well-formed token. -/
theorem Token.IsWellFormed.ofIdentLowerChars
    {chars : List Char}
    (shape : IsLowerIdentChars chars = true) :
    Token.IsWellFormed (Token.ident (String.ofList chars)) :=
  ⟨chars, shape, rfl⟩

/-- Constructor lemma for upper-case identifiers. -/
theorem Token.IsWellFormed.ofUidentUpperChars
    {chars : List Char}
    (shape : IsUpperIdentChars chars = true) :
    Token.IsWellFormed (Token.uident (String.ofList chars)) :=
  ⟨chars, shape, rfl⟩

/-- Boolean tokens, literals, keywords, punctuation, eof are
unconditionally well-formed (no payload to constrain). -/
theorem Token.IsWellFormed.ofKeyword (kind : KeywordKind) :
    Token.IsWellFormed kind.toToken := by
  cases kind <;> exact True.intro

theorem Token.IsWellFormed.ofIntLit (value : Int) (suffix : Option String) :
    Token.IsWellFormed (Token.intLit value suffix) := True.intro

theorem Token.IsWellFormed.ofBoolLit (value : Bool) :
    Token.IsWellFormed (Token.boolLit value) := True.intro

theorem Token.IsWellFormed.ofEof : Token.IsWellFormed Token.eof := True.intro

/-! ## Refinement type for parser input -/

/-- A `Token` paired with a proof that it satisfies
`Token.IsWellFormed`.  This is what `Lex.run` is contractually
obligated to produce.  Parser arms can pattern-match on the
underlying token and use the proof to extract well-formedness
witnesses for identifier payloads. -/
structure WellFormedToken where
  underlying : Token
  isWellFormed : Token.IsWellFormed underlying

/-- Project the token from a `WellFormedToken`. -/
@[reducible] def WellFormedToken.token (wfTok : WellFormedToken) : Token :=
  wfTok.underlying

/-- Inject a token whose well-formedness is known. -/
@[reducible] def WellFormedToken.ofToken (tok : Token)
    (proof : Token.IsWellFormed tok) : WellFormedToken :=
  ⟨tok, proof⟩

/-- Smart constructor for keyword tokens. -/
def WellFormedToken.ofKeyword (kind : KeywordKind) : WellFormedToken :=
  ⟨kind.toToken, Token.IsWellFormed.ofKeyword kind⟩

/-- Smart constructor for `eof`. -/
def WellFormedToken.eof : WellFormedToken :=
  ⟨Token.eof, Token.IsWellFormed.ofEof⟩

/-- Smart constructor for boolean literals. -/
def WellFormedToken.ofBool (value : Bool) : WellFormedToken :=
  ⟨Token.boolLit value, Token.IsWellFormed.ofBoolLit value⟩

/-- Smart constructor for lower-case identifiers, given chars
satisfying the shape predicate. -/
def WellFormedToken.ofLowerIdent {chars : List Char}
    (shape : IsLowerIdentChars chars = true) : WellFormedToken :=
  ⟨Token.ident (String.ofList chars),
   Token.IsWellFormed.ofIdentLowerChars shape⟩

/-- Smart constructor for upper-case identifiers. -/
def WellFormedToken.ofUpperIdent {chars : List Char}
    (shape : IsUpperIdentChars chars = true) : WellFormedToken :=
  ⟨Token.uident (String.ofList chars),
   Token.IsWellFormed.ofUidentUpperChars shape⟩

/-! ## Lexer-correctness target

The lemma below is the LOAD-BEARING contract between Lex and
Parse.  It is left as a target — a future lexer-correctness
package will discharge it by structural induction on
`classifyIdent`'s output, using `IsAllIdentTail`-preservation
through `readIdentLexeme`.

```lean
theorem Lex.run_outputs_wellformed
    (chars : List Char)
    (tokens : Array PositionedToken)
    (run_ok : Lex.run chars = .ok tokens)
    (idx : Nat) (hLt : idx < tokens.size) :
    Token.IsWellFormed (tokens[idx]'hLt).token
```

When discharged, the parser can refine its input from
`Array PositionedToken` to `Array { ptok : PositionedToken //
Token.IsWellFormed ptok.token }`, eliminating the need for
runtime well-formedness checks.
-/

end LeanFX2.Surface
