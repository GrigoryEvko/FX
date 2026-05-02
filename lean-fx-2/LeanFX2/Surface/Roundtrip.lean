import LeanFX2.Surface.Lex
import LeanFX2.Surface.Parse
import LeanFX2.Surface.Print

/-! # Surface/Roundtrip — lex/parse/print correctness theorems

The two load-bearing roundtrip theorems for the surface layer:

```lean
theorem lex_print_roundtrip (tokens : Array Token) :
    Lex.run (Print.runTokens tokens) = .ok tokens
```

Lex ∘ Print = id on token streams.

```lean
theorem parse_print_roundtrip (ast : SurfaceModule) :
    Parse.run (Lex.run (Print.run ast)) = .ok ast
```

(Lex ∘ Parse) ∘ Print = id on ASTs.

## Why both

* Lex roundtrip ensures the lexer doesn't lose info (whitespace,
  comments preserved or token-level accurate)
* Parse roundtrip ensures parser+printer are inverses on syntax
  trees

## Proof strategies

* **Lex roundtrip**: structural induction on token list, each ctor
  case shows that printing then re-lexing recovers it
* **Parse roundtrip**: structural induction on AST, each Expr/Decl
  ctor shows print produces a valid parseable form

## Dependencies

* `Surface/Lex.lean`, `Surface/Parse.lean`, `Surface/Print.lean`

## Downstream

* `Pipeline.lean` — composes lex+parse+elab pipeline; relies on
  these for round-trip correctness

## Implementation plan (Layer 10)

1. State both theorems
2. Prove by structural induction
3. Smoke: realistic FX code roundtrips

Target: ~400 lines.
-/

namespace LeanFX2.Surface

-- TODO Layer 10: lex_print + parse_print roundtrip theorems

end LeanFX2.Surface
