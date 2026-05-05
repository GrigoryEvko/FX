/-! # Algo/Completeness — algorithmic completeness

Every well-typed Term has an inferable / checkable type:

```lean
theorem Term.infer_complete :
    -- For every typed Term t : Term ctx ty raw,
    -- the inference algorithm finds it (or a Conv-equivalent type)
    Term.infer ctx raw = some ⟨ty', t'⟩ ∧ Conv ty ty' ∧ HEq t t'
```

Completeness is the harder half — soundness is automatic from typing,
but completeness requires proving the algorithm doesn't *miss* valid
typings.

## Proof structure

By structural induction on the typed Term:
* `var i`: infer returns the var via varType
* `app fn arg`: infer fn → arrow type, check arg → matches, return
* `lam body`: needs check mode (synth doesn't infer abstractions
  without type ann)
* etc.

## Modulo Conv

Completeness is "up to Conv" because two Terms of Conv-equal types
are interchangeable.  The algorithm picks a canonical type from the
synth-then-Conv discipline; the user's expected type may differ
modulo Conv.

## Dependencies

* `Algo/Soundness.lean`

## Downstream

* `Pipeline.lean` — pipeline composes infer + check + Conv
* `Surface/Elab.lean` — completeness underwrites elaboration's
  guarantee that valid surface terms produce typed kernel Terms

## Implementation plan (Layer 9)

1. State completeness theorem
2. Structural induction on Term
3. Each case: invoke synth/check, verify result agrees up to Conv
-/

namespace LeanFX2.Algo

-- TODO Layer 9: infer_complete + check_complete theorems

end LeanFX2.Algo
