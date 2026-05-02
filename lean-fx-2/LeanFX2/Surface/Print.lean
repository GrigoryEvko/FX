import LeanFX2.Surface.AST

/-! # Surface/Print — AST → String pretty printer

```lean
def Print.run (ast : SurfaceModule) : String
```

Inverse of `Surface/Parse.lean`.  Produces FX source that, when
re-lexed and re-parsed, yields the same AST (verified by
`Surface/Roundtrip.lean`).

## Pretty-printing strategy

* Two-space indentation per nesting level
* Line breaks at logical boundaries (after `;`, before `else`)
* Operator precedence respects original grouping (insert parens
  only when needed for re-parse fidelity)
* Comments preserved (when AST tracks them)
* Doc comments (`///`) attached to following decl

## Roundtrip property

```lean
theorem roundtrip : Parse.run (Lex.run (Print.run ast)) = .ok ast
```

This is the load-bearing correctness contract for the printer.
Verified in `Surface/Roundtrip.lean`.

## Dependencies

* `Surface/AST.lean`

## Downstream

* `Surface/Roundtrip.lean` — roundtrip theorem
* User-facing error messages (re-print fragments of source)

## Implementation plan (Layer 10)

1. `Print.run` per AST node
2. Indentation discipline
3. Operator-parenthesization heuristic
4. Smoke: hello-world prints + roundtrips

Target: ~600 lines.
-/

namespace LeanFX2.Surface

-- TODO Layer 10: Print.run per AST node

end LeanFX2.Surface
