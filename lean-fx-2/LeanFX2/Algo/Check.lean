import LeanFX2.Algo.Infer

/-! # Algo/Check — type checking (bidirectional check mode)

```lean
def Term.check (ctx : Ctx mode level scope) (ty : Ty level scope)
    (raw : RawTerm scope) : Option (Term ctx ty raw)
```

Given a context + expected type + raw term, attempts to construct a
typed Term inhabiting `ty` whose raw form is `raw`.

## Algorithm

1. If `raw` is a synthesizable form (per `Algo/Infer.lean`), call
   `Term.infer` and verify the inferred type matches `ty` via Conv
2. Otherwise, dispatch on `raw`:
   * `lam body` — split `ty` into arrow domain/codomain, check body
   * `lamPi body` — split into piTy, check body in extended ctx
   * `pair fv sv` — split into sigmaTy, check both
   * `refl rawWitness` — split `ty` into id, verify endpoints
   * Modal intros — analogous

## Bidirectional discipline

Synthesis and checking complement each other:
* Synth: type discoverable from term
* Check: type provided, term filled in

The split avoids the need for full unification — checks are
syntactic Conv equality, not unification.

## Conv check fallthrough

When inferred type `ty_inf` differs from expected `ty`, attempt
`Conv ty_inf ty`.  If conv succeeds, accept; else reject.  This is
the "check fallthrough" pattern (lean-fx task #912).

## Dependencies

* `Algo/Infer.lean`

## Downstream

* `Surface/Elab.lean` — elaboration calls check at expected-type
  boundaries

## Implementation plan (Layer 9)

1. Define `Term.check` per raw form
2. Synth + Conv check fallthrough
3. Smoke: well-typed and ill-typed examples

Target: ~300 lines.
-/

namespace LeanFX2.Algo

-- TODO Layer 9: Term.check per RawTerm ctor
-- TODO Layer 9: synth-then-Conv-check fallthrough
-- TODO Layer 9: smoke tests for well-typed / ill-typed

end LeanFX2.Algo
