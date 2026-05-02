import LeanFX2.Surface.AST
import LeanFX2.Algo.Check
import LeanFX2.Algo.Infer

/-! # Surface/Elab — surface AST → kernel Term

Elaboration: bridges from human-readable surface syntax to the typed
kernel Term.

```lean
def Elab.elabExpr (ctx : Ctx mode level scope)
    (expectedType : Option (Ty level scope))
    (ast : Expr) : Except ElabError (Σ ty raw, Term ctx ty raw)
```

## Elaboration tasks

1. **Name resolution** — surface identifiers → de Bruijn indices /
   global decl references
2. **Implicit arg insertion** — `#`-prefixed type args + Lean-style
   unification fills missing implicits
3. **Type inference / checking** — bidirectional via `Algo/Infer` +
   `Algo/Check`
4. **Sugar desugaring** — pipe `|>`, dot-shorthand `.field`, `for`
   loops, comprehensions
5. **Error reporting** — produce ElabError with source position

## Bidirectional dispatch

Elaboration runs in either:
* **Synth mode** — type unknown, infer from term structure
* **Check mode** — expected type given, term must match

Surface forms map to one or the other:
* Variable, application, projection: synth
* Lambda, pair, refl: check
* Annotated expression `(e : T)`: switch from synth to check

## Sugar desugaring

* `x |> f(a)` → `f(a, x)` (pipe positional fill)
* `.field` → `fn(it) => it.field` (when in argument position)
* `for x in xs; body end for` → `xs.iter |> map(fn(x) => body)`
* `[expr for x in xs if cond]` → `xs |> filter(cond) |> map(fn(x) => expr)`

## Dependencies

* `Surface/AST.lean`
* `Algo/Check.lean`, `Algo/Infer.lean`

## Downstream

* `Surface/ElabSoundness.lean`, `Surface/ElabCompleteness.lean`
* `Pipeline.lean` — pipeline calls elab as the final compile step

## Implementation plan (Layer 10)

1. Define `ElabError` enum + position propagation
2. `Elab.elabExpr` per Expr ctor
3. `Elab.elabDecl` per Decl ctor
4. `Elab.elabModule` driver
5. Sugar desugaring helpers
6. Smoke: simple FX programs round-trip lex → parse → elab → kernel

Target: ~1500 lines.
-/

namespace LeanFX2.Surface

-- TODO Layer 10: Elab.elabExpr / elabDecl / elabModule
-- TODO Layer 10: sugar desugaring

end LeanFX2.Surface
