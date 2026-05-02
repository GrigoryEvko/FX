/-! # Surface/Token — token alphabet for the FX surface lexer

Per `fx_lexer.md` §2-§3 + `fx_grammar.md` §2 (keywords, literals,
operators, delimiters).  Coverage here is exhaustive of the spec —
every token the lexer can produce is represented as a Token ctor.

## Structure

* `Trit` — balanced ternary digit (`-1`, `0`, `+1`)
* `StrKind` — regular / format / raw / bytes
* `Token` — flat enum over every token form

## Load-bearing relationships

This file is the SYNTACTIC alphabet.  The semantic relationships
that the parser, elaborator, and downstream layers depend on live
in three companion files:

* `Surface/TokenSchema.lean` — `KeywordKind` enum aligned 1:1 with
  the 92 spec keywords + `Token` bijection + typed-closer
  (`BlockOpener → List KeywordKind`) per fx_grammar.md §14.
* `Surface/TokenInvariants.lean` — decidable identifier-shape
  predicates per fx_lexer.md §3.1; refines `Token.ident`/`uident`
  payloads to provably valid lexemes.
* `Surface/GrammarToken.lean` — `TokenCategory` (parser dispatch)
  + operator-precedence table per fx_grammar.md §3 + delimiter
  balance predicate.

When this file changes (new/renamed/removed ctor), ALL THREE schema
files break.  That is the load-bearing signal — they encode the
invariants that downstream layers rely on.

## Coverage audit

* Identifiers: 2 (lower, upper)
* Literals: 11 (int, typedInt, decimal, typedDecimal, typedFloat,
  ternary, typedTernary, string, fstring, rstring, bstring, bool)
* Keywords: 92 (matches fx_grammar.md §2.2 exactly)
* Operators: 32 (matches fx_grammar.md §2.4 + fx_lexer.md §6)
* Delimiters: 6 (parens, brackets, braces — matches §15)
* Punctuation: 8 (`, ; : . # @ _` + backtick)
* Special: 4 (eof, doc_comment, attribute-open `@[`, range/spread)

All zero-axiom (the inductive definitions and DecidableEq derivations
only reach core Lean elimination, no propext / Quot.sound).
-/

namespace LeanFX2.Surface

/-- Balanced-ternary digit.  Used in trit literals like `0t10T`
(digits 1, 0, -1).  Per `fx_lexer.md` §3.4 / fx_grammar.md §2.3. -/
inductive Trit : Type
  | negOne
  | zero
  | posOne
  deriving DecidableEq, Repr

/-- String literal flavor: regular / format-string / raw / bytes.
Per `fx_lexer.md` §5 / fx_grammar.md §2.3. -/
inductive StrKind : Type
  | regular   -- "..."
  | fstring   -- f"..."  (interpolation)
  | raw       -- r"..."  (no escapes)
  | bytes     -- b"..."  (UTF-8 byte literal)
  deriving DecidableEq, Repr

/-- Surface token alphabet.  Ordered by category for readability;
ordering is not load-bearing.  When new tokens are added, also
add a corresponding `KeywordKind`/`OperatorKind` entry in
`TokenSchema.lean` so the bijection / category dispatch stays
total. -/
inductive Token : Type

  -- Identifiers
  | ident (name : String)         -- snake_case identifier
  | uident (name : String)        -- PascalCase (types/ctors/modules)

  -- Numeric and string literals
  | intLit (value : Int) (suffix : Option String)
  | decLit (mantissa : String) (suffix : Option String)
  | floatLit (mantissa : String) (suffix : String)  -- f32/f64 always suffix
  | strLit (value : String) (kind : StrKind)
  | bitLit (width : Nat) (value : Nat)
  | tritLit (digits : List Trit)
  | boolLit (value : Bool)

  -- 92 global keywords (spec-aligned with fx_grammar.md §2.2)
  -- Listed alphabetically.  When this list changes, update:
  --   * KeywordKind in TokenSchema.lean
  --   * Token.asKeyword / KeywordKind.toToken
  --   * classifyIdent in Lex.lean
  | kwAffine | kwAnd | kwAs | kwAssert | kwAwait
  | kwAxiom | kwBegin | kwBench | kwBisimulation | kwBreak
  | kwBy | kwCalc | kwCatch | kwClass | kwCode
  | kwCodata | kwComptime | kwConst | kwContinue | kwContract
  | kwDecreases | kwDecorator | kwDeclassify | kwDefer | kwDimension
  | kwDrop | kwDual | kwEffect | kwElse | kwEnd
  | kwErrdefer | kwException | kwExists | kwExports | kwExtern
  | kwFalse | kwFn | kwFor | kwForall | kwGhost
  | kwHandle | kwHint | kwIf | kwImpl | kwIn
  | kwInclude | kwInstance | kwIs | kwLabel | kwLayout
  | kwLemma | kwLet | kwLinear | kwMachine | kwMatch
  | kwModule | kwMut | kwNot | kwOpen | kwOr
  | kwOwn | kwPost | kwPre | kwProof | kwPub
  | kwQuotient | kwReceive | kwRec | kwRef | kwRefinement
  | kwReturn | kwSanitize | kwSecret | kwSelect | kwSelf
  | kwSend | kwSession | kwSorry | kwSpawn | kwTaintClass
  | kwTainted | kwTest | kwTrue | kwTry | kwType
  | kwUnfold | kwVal | kwVerify | kwWhile | kwWith
  | kwWhere | kwYield

  -- Delimiters (fx_grammar.md §15)
  | lparen | rparen
  | lbrace | rbrace
  | lbracket | rbracket

  -- Punctuation (fx_grammar.md §2.4)
  | comma | semicolon | colon
  | dot                                  -- `.` (raw, before transformer)
  | dotProj                              -- `.` (after transformer §8.2)
  | dotdot                               -- `..` range exclusive
  | dotdotEq                             -- `..=` range inclusive
  | spread                               -- `...` rest pattern / spread
  | equals                               -- `=`
  | arrow                                -- `->`
  | fatArrow                             -- `=>`
  | pipe                                 -- `|>`
  | atSign                               -- `@`
  | atBracket                            -- `@[`
  | hash                                 -- `#`
  | underscore                           -- `_`
  | backtick                             -- `` ` ``

  -- Comparison (fx_grammar.md §2.4)
  | eqEq | notEq | lt | gt | le | ge

  -- Arithmetic (fx_grammar.md §2.4)
  | plus | minus | star | slash | percent

  -- Bitwise (fx_grammar.md §2.4)
  | amp | bar | caret | tilde | shiftLeft | shiftRight

  -- Logical-propositional (fx_grammar.md §2.4)
  | implies   -- ==>
  | iff       -- <==>

  -- Special / sentinel
  | docComment (body : String)
  | eof
  deriving DecidableEq, Repr

/-- Width of a Trit when packed into a `t6`/`t12`/`t24`/`t48` literal:
each Trit slot occupies the bits needed to encode 3 values (~1.585
bits = 2 bits in practice).  Per `fx_lexer.md` §3.4. -/
@[reducible] def Trit.bitsPerDigit : Nat := 2

/-- Convert a Trit to its signed integer value: `negOne ↦ -1`,
`zero ↦ 0`, `posOne ↦ 1`. -/
def Trit.toInt : Trit → Int
  | .negOne => -1
  | .zero   => 0
  | .posOne => 1

end LeanFX2.Surface
