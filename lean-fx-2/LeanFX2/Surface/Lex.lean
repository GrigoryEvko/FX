import LeanFX2.Surface.Token

/-! # Surface/Lex — string → token stream

```lean
def Lex.run (source : String) : Except LexError (Array Token)
```

Per `fx_lexer.md` §4-§5: UTF-8 source, ASCII identifiers, position
tracking, error recovery.

## Algorithm

Standard recursive-descent lexer:
* Skip whitespace + comments (line `//`, block `/* */`)
* Match keywords by longest match, then identifier
* Numeric literals with width/suffix parsing
* String literals with escape sequences
* Bit/trit literals with `Nb`/`Nt` prefix
* Position info attached to each token (line:col)

## Error recovery

Per `fx_lexer.md` §7: on lex error, skip to next whitespace, emit
diagnostic with position, continue.  Don't fail-fast — report all
errors in one pass.

## Comments and whitespace

* `//` to end of line
* `/* ... */` non-nesting (per fx_lexer.md decision)
* `///` doc comment — attaches to next decl (passed through to AST)

## Dependencies

* `Surface/Token.lean`

## Downstream

* `Surface/Parse.lean` — parser consumes the token array
* `Surface/Roundtrip.lean` — lex/print roundtrip

## Implementation plan (Layer 10)

1. Define `LexError` enum
2. `Lex.run` recursive descent
3. Token transformer pipeline post-pass
4. Smoke: hello-world FX file lexes without error

Target: ~600 lines.
-/

namespace LeanFX2.Surface

-- TODO Layer 10: LexError enum
-- TODO Layer 10: Lex.run recursive descent
-- TODO Layer 10: token transformer pass

end LeanFX2.Surface
