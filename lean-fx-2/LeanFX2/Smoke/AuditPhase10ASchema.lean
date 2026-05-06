import LeanFX2.Surface.Lex
import LeanFX2.Surface.HostLex
import LeanFX2.Surface.TokenSchema
import LeanFX2.Surface.TokenInvariants
import LeanFX2.Surface.GrammarToken

/-! # Smoke/AuditPhase10ASchema — load-bearing relationship checks

End-to-end smoke verifying the surface-layer schema is internally
consistent and integrated with `Lex`.

## What this tests

1. **Keyword bijection** — `KeywordKind.toToken` and
   `Token.asKeyword` are mutual inverses on the keyword subset.
2. **Lexeme round-trip** — `KeywordKind.fromCharsExact` recovers
   the keyword from its canonical lexeme chars.
3. **Lex output uses the schema** — `classifyIdent` produces the
   token corresponding to the recognized keyword.
4. **TokenCategory dispatch** is total — every reachable Token
   classifies into exactly one category.
5. **BracketKind round-trip** — opener/closer recognition
   recovers the bracket flavor.
6. **OperatorKind precedence ladder** matches fx_grammar.md §3
   (16 levels, prefix above all infix).

All tests are `#print axioms`-clean (no propext, no
Classical.choice, no Quot.sound).
-/

namespace LeanFX2.Smoke

open LeanFX2.Surface

/-! ## Section 1 — Keyword bijection round-trip -/

/-- Spot-check: the keyword bijection is the identity for `fnK`. -/
example : Token.asKeyword (KeywordKind.fnK.toToken) = some KeywordKind.fnK := by rfl

/-- Spot-check: the bijection holds for `quotient`, which is one
of the keywords ADDED in this phase (not present in the legacy
Token enum). -/
example : Token.asKeyword (KeywordKind.quotient.toToken) = some KeywordKind.quotient := by rfl

/-- Universal round-trip from `TokenSchema.lean` — every
`KeywordKind` ctor's image in `Token` recovers via `asKeyword`. -/
example (kind : KeywordKind) :
    kind.toToken.asKeyword = some kind :=
  Keyword.toToken_asKeyword kind

/-! ## Section 2 — Lexeme recognition round-trip -/

example :
    KeywordKind.fromCharsExact ['f', 'n'] = some KeywordKind.fnK := by rfl

example :
    KeywordKind.fromCharsExact KeywordKind.bisimulation.toLexemeChars
      = some KeywordKind.bisimulation := by rfl

example :
    KeywordKind.fromCharsExact ['n', 'o', 'p', 'e'] = none := by rfl

/-! ## Section 3 — Lex integration

The lexer's `classifyIdent` now uses `KeywordKind.fromCharsExact`
as its source of truth.  These tests verify keyword tokens come
out correctly. -/

example : classifyIdent ['n', 'f'] = Token.kwFn := by rfl   -- reversed input
example : classifyIdent ['t', 'e', 'l'] = Token.kwLet := by rfl
example : classifyIdent ['n', 'o', 'i', 't', 'a', 'l', 'u', 'm', 'i', 's', 'i', 'b']
         = Token.kwBisimulation := by rfl
example : classifyIdent ['s', 's', 'a', 'l', 'c', '_', 't', 'n', 'i', 'a', 't']
         = Token.kwTaintClass := by rfl

/-- `true` and `false` are special — they're in the keyword table
AND in the literal payload set; the lexer prefers literal form. -/
example : classifyIdent ['e', 'u', 'r', 't'] = Token.boolLit true := by rfl
example : classifyIdent ['e', 's', 'l', 'a', 'f'] = Token.boolLit false := by rfl

/-- Non-keyword identifiers go to ident/uident. -/
example : classifyIdent ['o', 'o', 'f'] = Token.ident "foo" := by rfl
example : classifyIdent ['o', 'o', 'F'] = Token.uident "Foo" := by rfl

/-! ## Section 4 — TokenCategory dispatch totality -/

example : (Token.kwFn).category = TokenCategory.keyword := by rfl
example : (Token.ident "x").category = TokenCategory.identLower := by rfl
example : (Token.uident "Foo").category = TokenCategory.identUpper := by rfl
example : (Token.intLit 42 none).category = TokenCategory.literal := by rfl
example : (Token.lparen).category = TokenCategory.delimiterOpen := by rfl
example : (Token.rparen).category = TokenCategory.delimiterClose := by rfl
example : (Token.comma).category = TokenCategory.punctuation := by rfl
example : (Token.plus).category = TokenCategory.operator := by rfl
example : (Token.eof).category = TokenCategory.special := by rfl

/-! ## Section 5 — Bracket round-trip -/

example : (BracketKind.paren.opener).asBracketOpener = some BracketKind.paren := by rfl
example : (BracketKind.brace.closer).asBracketCloser = some BracketKind.brace := by rfl

/-- The bracket round-trip lemmas hold UNIVERSALLY. -/
example (kind : BracketKind) : kind.opener.asBracketOpener = some kind :=
  BracketKind.opener_asBracketOpener kind

example (kind : BracketKind) : kind.closer.asBracketCloser = some kind :=
  BracketKind.closer_asBracketCloser kind

/-! ## Section 6 — Operator precedence ladder -/

example : OperatorKind.arrow.precedenceLevel = 1 := by rfl
example : OperatorKind.pipe.precedenceLevel = 2 := by rfl
example : OperatorKind.logicalOr.precedenceLevel = 5 := by rfl
example : OperatorKind.logicalAnd.precedenceLevel = 6 := by rfl
example : OperatorKind.eqEq.precedenceLevel = 8 := by rfl
example : OperatorKind.plus.precedenceLevel = 15 := by rfl
example : OperatorKind.star.precedenceLevel = 16 := by rfl
example : OperatorKind.negate.precedenceLevel = 17 := by rfl

/-- Prefix operators bind TIGHTER than any infix.  Encoded as:
their precedence level exceeds the maximum infix level (16). -/
example : OperatorKind.negate.precedenceLevel > OperatorKind.star.precedenceLevel :=
  by decide

example : OperatorKind.bitNot.precedenceLevel > OperatorKind.percent.precedenceLevel :=
  by decide

/-- Comparison operators are non-associative (per fx_grammar.md
§3 — chains rejected at parse time). -/
example : OperatorKind.eqEq.assoc = OperatorAssoc.nonAssoc := by rfl
example : OperatorKind.lt.assoc = OperatorAssoc.nonAssoc := by rfl

/-- Function arrow is right-associative (`a -> b -> c` parses as
`a -> (b -> c)`). -/
example : OperatorKind.arrow.assoc = OperatorAssoc.rightA := by rfl

/-! ## Section 7 — BlockOpener typed-closer schema -/

example : BlockOpener.fnK.expectedClosers
        = [CloserKeyword.keyword KeywordKind.fnK] := by rfl
example : BlockOpener.matchK.expectedClosers
        = [CloserKeyword.keyword KeywordKind.matchK] := by rfl
example : BlockOpener.moduleType.expectedClosers
        = [CloserKeyword.keyword KeywordKind.moduleK,
           CloserKeyword.keyword KeywordKind.typeK] := by rfl

/-- After C01: contextual-keyword closers are now named precisely.
The `pipeline` block's typed closer is the contextual keyword
`pipeline`, not the surrogate `KeywordKind.codata` previously used. -/
example : BlockOpener.pipeline.expectedClosers
        = [CloserKeyword.contextualKeyword ContextualKeyword.pipelineK] := by rfl

example : BlockOpener.hardwareFn.expectedClosers
        = [CloserKeyword.contextualKeyword ContextualKeyword.hardwareK,
           CloserKeyword.keyword KeywordKind.fnK] := by rfl

example : BlockOpener.moduleFunctor.expectedClosers
        = [CloserKeyword.keyword KeywordKind.moduleK,
           CloserKeyword.contextualKeyword ContextualKeyword.functorK] := by rfl

example : BlockOpener.fnK.isSimple = true := by rfl
example : BlockOpener.moduleType.isSimple = false := by rfl

/-- Concrete typed-closer match check: `end fn` matches a `fnK`
opener when the lookahead has `[CloserKeyword.keyword .fnK]`. -/
example : BlockOpener.fnK.matchesEnd
            [CloserKeyword.keyword KeywordKind.fnK] = true := by rfl

example :
    BlockOpener.fnK.matchesEnd
      [CloserKeyword.keyword KeywordKind.matchK] = false := by rfl

example :
    BlockOpener.moduleType.matchesEnd
      [CloserKeyword.keyword KeywordKind.moduleK,
       CloserKeyword.keyword KeywordKind.typeK]
      = true := by rfl

/-- C01 correctness: the parser DISTINGUISHES `end pipeline` (closes
a `pipeline` block) from `end codata` (closes a `codata` block).
Pre-C01 these would both have matched a `pipeline` opener via the
`KeywordKind.codata` surrogate — a real bug. -/
example :
    BlockOpener.pipeline.matchesEnd
      [CloserKeyword.keyword KeywordKind.codata] = false := by rfl

example :
    BlockOpener.pipeline.matchesEnd
      [CloserKeyword.contextualKeyword ContextualKeyword.pipelineK]
      = true := by rfl

/-! ## Section 8 — Lex.run end-to-end

Lex a small piece of FX surface syntax with the new schema in
place.  We use the explicit host-boundary shim (which leaks 3 axioms via
`String.toList`) to check integration without putting that function in
the production `Surface.Lex` module. -/

#eval HostLex.runFromString "fn foo() : nat = 42;"
#eval HostLex.runFromString "let x = if true; 1 else 0 end if;"
#eval HostLex.runFromString "type quotient_thing = int;"
#eval HostLex.runFromString "with secret tainted ref mut"

/-! ## Section 9 — Cross-schema consistency

Lemmas connecting `KeywordKind` ↔ `Token.category` and
`BracketKind` ↔ `Token.category`.  These caught a real bug
during initial schema design: `Token.dotdot` and `Token.dotdotEq`
were misclassified as `punctuation`, but the OperatorKind
mapping requires them to be `operator` (per fx_grammar.md §3
range precedence level 14).  The
`OperatorKind.toToken_category_symbolOps` lemma failed to
typecheck until `Token.category` was corrected. -/

example : KeywordKind.fnK.toToken.category = TokenCategory.keyword :=
  KeywordKind.toToken_category KeywordKind.fnK

example : BracketKind.paren.opener.category = TokenCategory.delimiterOpen :=
  BracketKind.opener_category BracketKind.paren

example : BracketKind.brace.closer.category = TokenCategory.delimiterClose :=
  BracketKind.closer_category BracketKind.brace

/-- Range operators are in `operator` category — was a bug
caught by the consistency lemma. -/
example : Token.dotdot.category = TokenCategory.operator := by rfl
example : Token.dotdotEq.category = TokenCategory.operator := by rfl

/-- Universal bound on operator precedence. -/
example (op : OperatorKind) :
    1 ≤ op.precedenceLevel ∧ op.precedenceLevel ≤ 17 :=
  OperatorKind.precedenceLevel_bounded op

/-! ## Section 10 — Reserved-non-tokens audit -/

/-- The 9 token-spellings explicitly excluded from the FX alphabet
per fx_grammar.md §2.4: `:=`, `::`, `!`, `?`, `?.`, `&&`, `||`,
`<|`, `'`. -/
example : Token.spellingsOfReservedNonTokens.length = 9 := by decide

/-! ## Axiom audit gates

`#print axioms` on the schema's load-bearing functions / lemmas
must report "does not depend on any axioms".  See the comment
block at the top of `TokenSchema.lean`, `TokenInvariants.lean`,
`GrammarToken.lean` for the contract. -/

#print axioms KeywordKind.toToken
#print axioms Token.asKeyword
#print axioms Keyword.toToken_asKeyword
#print axioms KeywordKind.fromCharsExact
#print axioms Keyword.fromCharsExact_toLexemeChars
#print axioms Keyword.toLexemeChars_injective
#print axioms Keyword.fromCharsExact_injective
#print axioms KeywordKind.toLexemeChars
#print axioms KeywordKind.toLexemeChars_isLowerIdent
#print axioms KeywordKind.toLexeme
#print axioms KeywordKind.category
#print axioms BlockOpener.expectedClosers
#print axioms BlockOpener.matchesEnd
#print axioms ContextualKeyword
#print axioms ContextualKeyword.toLexemeChars
#print axioms ContextualKeyword.all
#print axioms CloserKeyword
#print axioms CloserKeyword.toLexemeChars
#print axioms Token.IsWellFormed
#print axioms Token.IsWellFormed.ofKeyword
#print axioms Token.IsWellFormed.ofIdentLowerChars
#print axioms WellFormedToken.ofKeyword
#print axioms Token.category
#print axioms OperatorKind.precedenceLevel
#print axioms OperatorKind.assoc
#print axioms OperatorKind.toToken
#print axioms Token.asInfixOperator
#print axioms Token.asPrefixOperator
#print axioms Token.asBracketOpener
#print axioms Token.asBracketCloser
#print axioms BracketKind.opener_asBracketOpener
#print axioms BracketKind.closer_asBracketCloser
#print axioms classifyIdent
#print axioms Lex.run
#print axioms List.concat_getLast?_eq
#print axioms Array.push_toList_getLast?_eq
#print axioms Lex.run_eof_terminated

/-! ## Section 11 — L03 Lex.run EOF-termination smoke

A concrete instance: lexing the empty input list (zero tokens
produced by the lexer) yields a single-element output containing
just the `eof` sentinel; `getLast?` recovers it. -/

example :
    let chars : List Char := []
    Lex.run chars = .ok #[{ token := Token.eof, startPos := { offset := 0 } }] := by
  rfl

/-- Direct application of `Lex.run_eof_terminated` to a concrete
empty input — verifies the witness extraction works end-to-end. -/
example :
    ∃ eofPos : PositionedToken,
      (#[{ token := Token.eof, startPos := { offset := 0 } } ] :
        Array PositionedToken).toList.getLast? = some eofPos ∧
      eofPos.token = Token.eof :=
  Lex.run_eof_terminated [] _ rfl

end LeanFX2.Smoke
