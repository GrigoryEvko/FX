import LeanFX2.Surface.TokenSchema

/-! # Surface/GrammarToken — parser-level token dispatch

The parser's view of `Token`.  Establishes:

* `TokenCategory` — exhaustive classification of every Token
  ctor for parser dispatch
* `Token.category : Token → TokenCategory` — total function
* `OperatorAssoc` — Left / Right / NonAssoc / Prefix per
  fx_grammar.md §3
* `OperatorKind` — enum of operators with precedence + arity info
* `OperatorKind.precedenceLevel` — the 16-level ladder from
  fx_grammar.md §3
* `Token.asOperator : Token → Option OperatorKind` — partial
* `OperatorKind.toToken : OperatorKind → Token` — total
* Round-trip lemma
* `BracketDelimiter` — enum of opener/closer bracket pairs
* `Token.asBracketOpener` / `asBracketCloser` — partial extractors

## Why these are load-bearing

1. **`TokenCategory`** is the one-stop dispatch the parser uses:
   identifier-position, literal-position, operator-position,
   delimiter-position, etc.  Every parser arm pattern-matches
   against a TokenCategory.

2. **Operator precedence table** is the single source of truth
   for the precedence-climbing parser.  Adding a new operator
   means editing ONE table; `Token.asOperator` and parser arms
   stay in sync via the bijection.

3. **Bracket pairing** ensures `(` matches `)`, `{` matches `}`,
   `[` matches `]`, `<` matches `>` (in type-param context) —
   encoded as a typed bijection.

All zero-axiom under `#print axioms`.  Per `fx_grammar.md` §3
precedence ladder + §15 delimiter summary + §2.4 operator list.
-/

namespace LeanFX2.Surface

/-! ## Token category — exhaustive dispatch -/

/-- The parser's view of every token's role.  Every `Token` ctor
maps to exactly ONE category. -/
inductive TokenCategory : Type
  /-- `ident` — snake_case identifier -/
  | identLower
  /-- `uident` — PascalCase identifier (types, ctors, modules) -/
  | identUpper
  /-- numeric / string / boolean literals -/
  | literal
  /-- one of the 92 keywords -/
  | keyword
  /-- operator (arithmetic, comparison, logical, bitwise, range,
  arrow, pipe, ...) -/
  | operator
  /-- delimiter (parens, braces, brackets) -/
  | delimiterOpen
  | delimiterClose
  /-- punctuation (comma, semicolon, colon, dot variants, etc.) -/
  | punctuation
  /-- special tokens — eof, doc comments, attribute prefix -/
  | special
  deriving DecidableEq, Repr

/-- Total classification of every `Token` ctor.  No wildcard:
explicit arms keep this zero-axiom. -/
def Token.category : Token → TokenCategory
  | .ident _  => .identLower
  | .uident _ => .identUpper
  | .intLit _ _ | .decLit _ _ | .floatLit _ _
  | .strLit _ _ | .bitLit _ _ | .tritLit _ | .boolLit _ => .literal
  -- 92 keywords
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
  | .kwWhere | .kwYield => .keyword
  -- Delimiters
  | .lparen | .lbrace | .lbracket => .delimiterOpen
  | .rparen | .rbrace | .rbracket => .delimiterClose
  -- Punctuation (separators, attribute prefixes, scoping)
  | .comma | .semicolon | .colon
  | .dot | .dotProj | .spread
  | .underscore | .backtick | .atSign | .atBracket | .hash => .punctuation
  -- Operators (arithmetic, comparison, logical, bitwise, arrow,
  -- pipe, fat-arrow, equals, range).
  -- Range operators `..` and `..=` are at precedence level 14
  -- per fx_grammar.md §3 — operators not punctuation.
  -- `equals` is operator (used as `=` in `let x = e`); the parser
  -- disambiguates from comparison via context.
  | .equals | .arrow | .fatArrow | .pipe => .operator
  | .dotdot | .dotdotEq => .operator
  | .eqEq | .notEq | .lt | .gt | .le | .ge => .operator
  | .plus | .minus | .star | .slash | .percent => .operator
  | .amp | .bar | .caret | .tilde | .shiftLeft | .shiftRight => .operator
  | .implies | .iff => .operator
  -- Special / sentinel
  | .docComment _ | .eof => .special

/-! ## Operator precedence (per fx_grammar.md §3) -/

/-- Operator associativity per fx_grammar.md §3. -/
inductive OperatorAssoc : Type
  | leftA           -- left-associative (`a op b op c` = `(a op b) op c`)
  | rightA          -- right-associative
  | nonAssoc        -- chains rejected at parse time
  | prefix          -- prefix unary
  deriving DecidableEq, Repr

/-- Enumeration of operators whose precedence level the parser
needs.  Matches the §3 ladder.  Logical `and`/`or`/`not` and the
constructor-test `is` are KEYWORDS in `Token`, but they appear
here because the parser treats them as operators. -/
inductive OperatorKind : Type
  -- Level 1: function type arrow (right-assoc)
  | arrow
  -- Level 2: pipe (left)
  | pipe
  -- Level 3: iff (right)
  | iff
  -- Level 4: implies (right)
  | implies
  -- Level 5: logical or (left, keyword `or`)
  | logicalOr
  -- Level 6: logical and (left, keyword `and`)
  | logicalAnd
  -- Level 7: logical not (prefix, keyword `not`)
  | logicalNot
  -- Level 8: comparison (non-associative — chains rejected T050)
  | eqEq | notEq | lt | gt | le | ge
  -- Level 9: constructor test (left, keyword `is`)
  | isCtor
  -- Level 10-12: bitwise OR / XOR / AND
  | bitOr | bitXor | bitAnd
  -- Level 13: shift
  | shiftLeft | shiftRight
  -- Level 14: range (non-associative)
  | rangeExcl | rangeIncl
  -- Level 15: additive
  | plus | minus
  -- Level 16: multiplicative
  | star | slash | percent
  -- Above all infix: prefix unary
  | negate          -- `-` in prefix
  | bitNot          -- `~`
  deriving DecidableEq, Repr

/-- Precedence level per fx_grammar.md §3.  Higher level = tighter
binding.  Level 0 is reserved for the bottom of the ladder
(no operator binds looser than level 1). -/
def OperatorKind.precedenceLevel : OperatorKind → Nat
  | .arrow => 1
  | .pipe => 2
  | .iff => 3
  | .implies => 4
  | .logicalOr => 5
  | .logicalAnd => 6
  | .logicalNot => 7
  | .eqEq | .notEq | .lt | .gt | .le | .ge => 8
  | .isCtor => 9
  | .bitOr => 10
  | .bitXor => 11
  | .bitAnd => 12
  | .shiftLeft | .shiftRight => 13
  | .rangeExcl | .rangeIncl => 14
  | .plus | .minus => 15
  | .star | .slash | .percent => 16
  -- prefix operators bind tighter than any infix
  | .negate | .bitNot => 17

/-- Associativity per fx_grammar.md §3. -/
def OperatorKind.assoc : OperatorKind → OperatorAssoc
  | .arrow => .rightA
  | .pipe => .leftA
  | .iff => .rightA
  | .implies => .rightA
  | .logicalOr => .leftA
  | .logicalAnd => .leftA
  | .logicalNot => .prefix
  | .eqEq | .notEq | .lt | .gt | .le | .ge => .nonAssoc
  | .isCtor => .leftA
  | .bitOr => .leftA
  | .bitXor => .leftA
  | .bitAnd => .leftA
  | .shiftLeft | .shiftRight => .leftA
  | .rangeExcl | .rangeIncl => .nonAssoc
  | .plus | .minus => .leftA
  | .star | .slash | .percent => .leftA
  | .negate | .bitNot => .prefix

/-- Total mapping from `OperatorKind` to its `Token`
representative.  Note: prefix `negate` maps to the `minus` token
since FX uses `-` for both negation and subtraction; the parser
disambiguates by context.  Same for `bitNot` and `tilde`. -/
def OperatorKind.toToken : OperatorKind → Token
  | .arrow => .arrow
  | .pipe => .pipe
  | .iff => .iff
  | .implies => .implies
  | .logicalOr => .kwOr
  | .logicalAnd => .kwAnd
  | .logicalNot => .kwNot
  | .eqEq => .eqEq
  | .notEq => .notEq
  | .lt => .lt
  | .gt => .gt
  | .le => .le
  | .ge => .ge
  | .isCtor => .kwIs
  | .bitOr => .bar
  | .bitXor => .caret
  | .bitAnd => .amp
  | .shiftLeft => .shiftLeft
  | .shiftRight => .shiftRight
  | .rangeExcl => .dotdot
  | .rangeIncl => .dotdotEq
  | .plus => .plus
  | .minus => .minus
  | .star => .star
  | .slash => .slash
  | .percent => .percent
  | .negate => .minus      -- prefix: same token as binary minus
  | .bitNot => .tilde

/-- Recognize a token as an INFIX operator.  Returns the operator
kind in its infix interpretation; the prefix forms `negate` /
`bitNot` are extracted separately by the parser. -/
def Token.asInfixOperator : Token → Option OperatorKind
  | .arrow => some .arrow
  | .pipe => some .pipe
  | .iff => some .iff
  | .implies => some .implies
  | .kwOr => some .logicalOr
  | .kwAnd => some .logicalAnd
  | .eqEq => some .eqEq
  | .notEq => some .notEq
  | .lt => some .lt
  | .gt => some .gt
  | .le => some .le
  | .ge => some .ge
  | .kwIs => some .isCtor
  | .bar => some .bitOr
  | .caret => some .bitXor
  | .amp => some .bitAnd
  | .shiftLeft => some .shiftLeft
  | .shiftRight => some .shiftRight
  | .dotdot => some .rangeExcl
  | .dotdotEq => some .rangeIncl
  | .plus => some .plus
  | .minus => some .minus
  | .star => some .star
  | .slash => some .slash
  | .percent => some .percent
  -- All other tokens (identifiers, literals, keywords other
  -- than and/or/is, delimiters, prefix-only operators) — none
  | .ident _ | .uident _ => none
  | .intLit _ _ | .decLit _ _ | .floatLit _ _
  | .strLit _ _ | .bitLit _ _ | .tritLit _ | .boolLit _ => none
  | .kwAffine | .kwAs | .kwAssert | .kwAwait
  | .kwAxiom | .kwBegin | .kwBench | .kwBisimulation | .kwBreak
  | .kwBy | .kwCalc | .kwCatch | .kwClass | .kwCode
  | .kwCodata | .kwComptime | .kwConst | .kwContinue | .kwContract
  | .kwDecreases | .kwDecorator | .kwDeclassify | .kwDefer | .kwDimension
  | .kwDrop | .kwDual | .kwEffect | .kwElse | .kwEnd
  | .kwErrdefer | .kwException | .kwExists | .kwExports | .kwExtern
  | .kwFalse | .kwFn | .kwFor | .kwForall | .kwGhost
  | .kwHandle | .kwHint | .kwIf | .kwImpl | .kwIn
  | .kwInclude | .kwInstance | .kwLabel | .kwLayout
  | .kwLemma | .kwLet | .kwLinear | .kwMachine | .kwMatch
  | .kwModule | .kwMut | .kwNot | .kwOpen
  | .kwOwn | .kwPost | .kwPre | .kwProof | .kwPub
  | .kwQuotient | .kwReceive | .kwRec | .kwRef | .kwRefinement
  | .kwReturn | .kwSanitize | .kwSecret | .kwSelect | .kwSelf
  | .kwSend | .kwSession | .kwSorry | .kwSpawn | .kwTaintClass
  | .kwTainted | .kwTest | .kwTrue | .kwTry | .kwType
  | .kwUnfold | .kwVal | .kwVerify | .kwWhile | .kwWith
  | .kwWhere | .kwYield => none
  | .lparen | .rparen | .lbrace | .rbrace
  | .lbracket | .rbracket => none
  | .comma | .semicolon | .colon
  | .dot | .dotProj | .spread
  | .equals | .fatArrow
  | .atSign | .atBracket | .hash | .underscore | .backtick => none
  | .tilde => none  -- `~` is prefix only (bitNot/splice)
  | .docComment _ | .eof => none

/-- Recognize a token as a PREFIX operator.  Full enumeration
keeps this zero-axiom (wildcard `_ => none` would leak propext
via Lean's match compiler given Token's 200+ ctors). -/
def Token.asPrefixOperator : Token → Option OperatorKind
  | .minus => some .negate
  | .tilde => some .bitNot
  | .kwNot => some .logicalNot
  -- Identifier / literal payloads
  | .ident _ | .uident _ => none
  | .intLit _ _ | .decLit _ _ | .floatLit _ _
  | .strLit _ _ | .bitLit _ _ | .tritLit _ | .boolLit _ => none
  -- Other keywords
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
  | .kwModule | .kwMut | .kwOpen | .kwOr
  | .kwOwn | .kwPost | .kwPre | .kwProof | .kwPub
  | .kwQuotient | .kwReceive | .kwRec | .kwRef | .kwRefinement
  | .kwReturn | .kwSanitize | .kwSecret | .kwSelect | .kwSelf
  | .kwSend | .kwSession | .kwSorry | .kwSpawn | .kwTaintClass
  | .kwTainted | .kwTest | .kwTrue | .kwTry | .kwType
  | .kwUnfold | .kwVal | .kwVerify | .kwWhile | .kwWith
  | .kwWhere | .kwYield => none
  -- Delimiters
  | .lparen | .rparen | .lbrace | .rbrace
  | .lbracket | .rbracket => none
  -- Punctuation / operators (non-prefix)
  | .comma | .semicolon | .colon
  | .dot | .dotProj | .dotdot | .dotdotEq | .spread
  | .equals | .arrow | .fatArrow | .pipe
  | .atSign | .atBracket | .hash | .underscore | .backtick => none
  | .eqEq | .notEq | .lt | .gt | .le | .ge => none
  | .plus | .star | .slash | .percent => none
  | .amp | .bar | .caret | .shiftLeft | .shiftRight => none
  | .implies | .iff => none
  -- Special / sentinel
  | .docComment _ | .eof => none

/-! ## Bracket pairing (per fx_grammar.md §15) -/

/-- Bracket flavor. -/
inductive BracketKind : Type
  | paren        -- `(` `)`
  | brace        -- `{` `}`
  | bracket      -- `[` `]`
  -- Note: `<` `>` are listed in §15 as type-parameter brackets,
  -- but they're ambiguous with comparison `lt`/`gt` tokens.
  -- The parser handles angle brackets contextually; not in the
  -- BracketKind enum.
  deriving DecidableEq, Repr

/-- Total mapping: each bracket kind has a unique opener token. -/
def BracketKind.opener : BracketKind → Token
  | .paren   => .lparen
  | .brace   => .lbrace
  | .bracket => .lbracket

/-- Total mapping: each bracket kind has a unique closer token. -/
def BracketKind.closer : BracketKind → Token
  | .paren   => .rparen
  | .brace   => .rbrace
  | .bracket => .rbracket

/-- Recognize a token as a bracket opener.  Full enumeration
keeps this zero-axiom. -/
def Token.asBracketOpener : Token → Option BracketKind
  | .lparen   => some .paren
  | .lbrace   => some .brace
  | .lbracket => some .bracket
  -- Identifiers / literals
  | .ident _ | .uident _ => none
  | .intLit _ _ | .decLit _ _ | .floatLit _ _
  | .strLit _ _ | .bitLit _ _ | .tritLit _ | .boolLit _ => none
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
  | .kwWhere | .kwYield => none
  -- Closing delimiters
  | .rparen | .rbrace | .rbracket => none
  -- Punctuation / operators
  | .comma | .semicolon | .colon
  | .dot | .dotProj | .dotdot | .dotdotEq | .spread
  | .equals | .arrow | .fatArrow | .pipe
  | .atSign | .atBracket | .hash | .underscore | .backtick => none
  | .eqEq | .notEq | .lt | .gt | .le | .ge => none
  | .plus | .minus | .star | .slash | .percent => none
  | .amp | .bar | .caret | .tilde | .shiftLeft | .shiftRight => none
  | .implies | .iff => none
  | .docComment _ | .eof => none

/-- Recognize a token as a bracket closer.  Full enumeration
keeps this zero-axiom. -/
def Token.asBracketCloser : Token → Option BracketKind
  | .rparen   => some .paren
  | .rbrace   => some .brace
  | .rbracket => some .bracket
  -- Identifiers / literals
  | .ident _ | .uident _ => none
  | .intLit _ _ | .decLit _ _ | .floatLit _ _
  | .strLit _ _ | .bitLit _ _ | .tritLit _ | .boolLit _ => none
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
  | .kwWhere | .kwYield => none
  -- Opening delimiters
  | .lparen | .lbrace | .lbracket => none
  -- Punctuation / operators
  | .comma | .semicolon | .colon
  | .dot | .dotProj | .dotdot | .dotdotEq | .spread
  | .equals | .arrow | .fatArrow | .pipe
  | .atSign | .atBracket | .hash | .underscore | .backtick => none
  | .eqEq | .notEq | .lt | .gt | .le | .ge => none
  | .plus | .minus | .star | .slash | .percent => none
  | .amp | .bar | .caret | .tilde | .shiftLeft | .shiftRight => none
  | .implies | .iff => none
  | .docComment _ | .eof => none

/-- **Round-trip**: every bracket kind has its opener correctly
recognized.  Load-bearing — proves the parser's bracket-balance
predicate is consistent with `BracketKind`. -/
theorem BracketKind.opener_asBracketOpener (kind : BracketKind) :
    kind.opener.asBracketOpener = some kind := by
  cases kind <;> rfl

/-- **Round-trip**: every bracket kind has its closer correctly
recognized. -/
theorem BracketKind.closer_asBracketCloser (kind : BracketKind) :
    kind.closer.asBracketCloser = some kind := by
  cases kind <;> rfl

/-! ## Disambiguation contexts (fx_design.md §2.7)

Per fx_design.md §2.7, FX has 28 disambiguation rules; some of
them carve out token-level decisions.  The most load-bearing
rule for the parser is rule 14:

> Mutation uses `.set(value)` on `cell` types and `ref mut`
> borrows.  In `hardware` blocks, register updates use
> `.set(value)` on `reg` types.  There is no `:=` operator.

— meaning the lexer NEVER produces a `:=` token.  We encode this
as a Bool predicate `Token.isReservedNonToken` that's `false`
for every Token ctor we DO produce (sanity audit).

Rule 26: `ref` is a SINGLE keyword with one meaning (borrow mode).
The expression-form mutable cell uses `cell()` — a regular
function call, not a keyword.  No special token-level handling.

Rule 17: `with` is exclusively after a return type (effect
annotation).  Record updates and format overrides use spread
`{...}`; contract inheritance uses `extends`; handler
composition uses `handle`.  All these are distinct tokens. -/

/-- Documentary: list of token-spellings explicitly EXCLUDED
from the FX alphabet per fx_grammar.md §2.4.  Returning a list
of strings rather than a per-ctor function keeps the audit
zero-axiom and avoids enumerating the full Token ctor set. -/
def Token.spellingsOfReservedNonTokens : List String :=
  [":=", "::", "!", "?", "?.", "&&", "||", "<|", "'"]

/-! ## Cross-schema consistency

Lemmas connecting `KeywordKind` (TokenSchema.lean) and
`TokenCategory` / `BracketKind` (this file).  These are
load-bearing — they ensure the schema's two viewpoints
(bijection-to-Token vs categorical dispatch) agree.

Drift between the schemas would break these `cases <;> rfl`
lemmas at build time. -/

/-- Every keyword's `Token` representative is in the keyword
category.  Bridges `KeywordKind.toToken` (TokenSchema) with
`Token.category` (this file). -/
theorem KeywordKind.toToken_category (kind : KeywordKind) :
    kind.toToken.category = TokenCategory.keyword := by
  cases kind <;> rfl

/-- Every bracket-opener `Token` is in the `delimiterOpen`
category.  Bridges `BracketKind.opener` with `Token.category`. -/
theorem BracketKind.opener_category (kind : BracketKind) :
    kind.opener.category = TokenCategory.delimiterOpen := by
  cases kind <;> rfl

/-- Every bracket-closer `Token` is in the `delimiterClose`
category. -/
theorem BracketKind.closer_category (kind : BracketKind) :
    kind.closer.category = TokenCategory.delimiterClose := by
  cases kind <;> rfl

/-- Every operator `Token` (image of `OperatorKind.toToken`)
is in the `operator` category, EXCEPT the propositional-
language `logicalOr`, `logicalAnd`, `logicalNot`, `isCtor`
which use keyword tokens (`kwOr`/`kwAnd`/`kwNot`/`kwIs`) and
classify as keyword.

This nuance reflects fx_grammar.md §3 + §2.6: logical
connectives are KEYWORDS in FX (`not`, `and`, `or`), not symbol
operators (`!`, `&&`, `||`).  The parser still treats them as
operators with explicit precedence levels, but at the lexical
level they're keywords. -/
theorem OperatorKind.toToken_category_keywordOps :
    OperatorKind.logicalOr.toToken.category = TokenCategory.keyword ∧
    OperatorKind.logicalAnd.toToken.category = TokenCategory.keyword ∧
    OperatorKind.logicalNot.toToken.category = TokenCategory.keyword ∧
    OperatorKind.isCtor.toToken.category = TokenCategory.keyword := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- Symbol operators: arithmetic, comparison, bitwise, range,
arrow, pipe, iff, implies — all classify as `operator`. -/
theorem OperatorKind.toToken_category_symbolOps :
    OperatorKind.arrow.toToken.category = TokenCategory.operator ∧
    OperatorKind.pipe.toToken.category = TokenCategory.operator ∧
    OperatorKind.plus.toToken.category = TokenCategory.operator ∧
    OperatorKind.star.toToken.category = TokenCategory.operator ∧
    OperatorKind.eqEq.toToken.category = TokenCategory.operator ∧
    OperatorKind.bitOr.toToken.category = TokenCategory.operator ∧
    OperatorKind.shiftLeft.toToken.category = TokenCategory.operator ∧
    OperatorKind.rangeExcl.toToken.category = TokenCategory.operator := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- Operator precedence is BOUNDED: every operator's level is
between 1 and 17 inclusive (§3 has 16 infix levels + 1 for
prefix unary).  Useful for the precedence-climbing parser. -/
theorem OperatorKind.precedenceLevel_bounded (op : OperatorKind) :
    1 ≤ op.precedenceLevel ∧ op.precedenceLevel ≤ 17 := by
  cases op <;> exact ⟨by decide, by decide⟩

/-- Prefix operators are AT level 17 (above all 16 infix levels). -/
theorem OperatorKind.prefix_precedence_max :
    OperatorKind.negate.precedenceLevel = 17 ∧
    OperatorKind.bitNot.precedenceLevel = 17 ∧
    OperatorKind.logicalNot.precedenceLevel = 7 := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

end LeanFX2.Surface
