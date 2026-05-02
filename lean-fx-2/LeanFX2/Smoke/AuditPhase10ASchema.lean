import LeanFX2.Surface.Lex
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

example : BlockOpener.fnK.expectedClosers = [KeywordKind.fnK] := by rfl
example : BlockOpener.matchK.expectedClosers = [KeywordKind.matchK] := by rfl
example : BlockOpener.moduleType.expectedClosers
        = [KeywordKind.moduleK, KeywordKind.typeK] := by rfl

example : BlockOpener.fnK.isSimple = true := by rfl
example : BlockOpener.moduleType.isSimple = false := by rfl

/-- Concrete typed-closer match check: `end fn` matches a `fnK`
opener when the lookahead has `[KeywordKind.fnK]`. -/
example : BlockOpener.fnK.matchesEnd [KeywordKind.fnK] = true := by rfl

example :
    BlockOpener.fnK.matchesEnd [KeywordKind.matchK] = false := by rfl

example :
    BlockOpener.moduleType.matchesEnd [KeywordKind.moduleK, KeywordKind.typeK]
      = true := by rfl

/-! ## Section 8 — Lex.run end-to-end

Lex a small piece of FX surface syntax with the new schema in
place.  We use `runFromString` (which leaks 3 axioms via
`String.toList` — confined boundary) to check the integration. -/

#eval Lex.runFromString "fn foo() : nat = 42;"
#eval Lex.runFromString "let x = if true; 1 else 0 end if;"
#eval Lex.runFromString "type quotient_thing = int;"
#eval Lex.runFromString "with secret tainted ref mut"

/-! ## Section 9 — Reserved-non-tokens audit -/

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
#print axioms KeywordKind.toLexemeChars
#print axioms KeywordKind.toLexeme
#print axioms KeywordKind.category
#print axioms BlockOpener.expectedClosers
#print axioms BlockOpener.matchesEnd
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

end LeanFX2.Smoke
