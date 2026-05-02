import LeanFX2.Surface.Elab

/-! # Surface/ElabSoundness — elaboration soundness

```lean
theorem Elab.elabExpr_sound (ctx ty raw t) :
    Elab.elabExpr ctx (some ty) ast = .ok ⟨ty', raw, t⟩ →
    -- t is well-typed (automatic from Term's intrinsic typing)
    Conv ty ty'  -- inferred type matches expected (modulo Conv)
```

Like `Algo/Soundness.lean`, soundness is mostly automatic in
lean-fx-2's intrinsic typing — if elaboration produces a Term, that
Term is by construction well-typed.

What soundness DOES guarantee:
* The Term's type matches the user's expected type (modulo Conv)
* Sugar desugaring preserves semantics
* Implicit-arg insertion doesn't change observable behavior

## Dependencies

* `Surface/Elab.lean`

## Downstream

* `Surface/ElabCompleteness.lean`
* End-user trust: when elab succeeds, the user can trust the
  resulting kernel Term

## Implementation plan (Layer 10)

1. State soundness theorem
2. Mostly automatic; document the contract
-/

namespace LeanFX2.Surface

-- TODO Layer 10: Elab.elabExpr_sound theorem

end LeanFX2.Surface
