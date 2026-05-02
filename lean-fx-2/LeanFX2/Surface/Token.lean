/-! # Surface/Token — token alphabet for the FX surface lexer

Token types per `fx_lexer.md` §2-§3.  All keywords are common English
words; punctuation is ASCII; literals cover integers, decimals,
booleans, strings, bit/trit literals, identifiers.

## Token enum (skeleton)

```lean
inductive Token
  -- Identifiers and literals
  | ident (name : String)
  | uident (name : String)        -- PascalCase (types/ctors)
  | intLit (value : Int) (suffix : Option String)
  | decLit (value : String) (suffix : Option String)  -- exact decimal
  | floatLit (value : Float) (suffix : Option String)
  | strLit (value : String) (kind : StrKind)
  | bitLit (width : Nat) (value : Nat)
  | tritLit (digits : List Trit)
  | charLit (codepoint : Nat)
  | boolLit (value : Bool)
  -- Keywords (92 global per fx_design.md Appendix A)
  | kwFn | kwLet | kwIf | kwElse | kwFor | kwWhile | kwReturn
  | kwType | kwVal | kwEffect | kwMachine | kwContract
  | kwHandle | kwSession | kwSelect | kwYield | kwAwait | kwSpawn
  -- ... (full list in implementation)
  -- Punctuation
  | lparen | rparen | lbrace | rbrace | lbracket | rbracket
  | comma | semi | colon | dot | dotdot | dotdotdot
  | arrow | fatArrow | pipe | at
  -- ... more
  | eof
```

## Token transformer pipeline

Per `fx_lexer.md` §6, certain token sequences need post-processing:
* `FSTRING` interpolation expansion
* `ELSE IF` → `ELIF` merge
* Trailing comma strip in collection literals
* `DOT` → `DOT_PROJ` disambiguation in pipe context

These transformers operate on the token stream after raw lexing.

## Dependencies

None (Layer 10 of Layer 10).

## Downstream

* `Surface/Lex.lean` — produces these tokens
* `Surface/Parse.lean` — consumes them

## Implementation plan (Layer 10)

1. Define `Token` enum (~120 cases)
2. Define `StrKind` (regular/format/raw/bytes), `Trit` enum
3. Pretty-printer for tokens (debug aid)
4. `DecidableEq Token`

Target: ~300 lines.
-/

namespace LeanFX2.Surface

-- TODO Layer 10: Token inductive
-- TODO Layer 10: token transformer pipeline

end LeanFX2.Surface
