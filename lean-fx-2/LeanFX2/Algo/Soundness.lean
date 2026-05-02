import LeanFX2.Algo.Check
import LeanFX2.Algo.Infer

/-! # Algo/Soundness — algorithmic content soundness

Whatever the algorithm produces, it produces correct output:

```lean
theorem Term.infer_sound :
    Term.infer ctx raw = some ⟨ty, t⟩ →
    -- Result: t is a well-typed Term in ty (built from raw)
    ...

theorem Term.check_sound :
    Term.check ctx ty raw = some t →
    -- Result: t : Term ctx ty raw
    ...
```

Soundness is *automatic* in lean-fx-2's design because:
* The result is a Term value; Lean's type checker verifies its
  type at construction
* If `Term.infer` returns `some ⟨ty, t⟩`, Lean has already accepted
  `t : Term ctx ty raw` — soundness is the type signature

## What soundness theorems still add

* Witness extraction (when infer returns Some, the typed Term is
  constructively present)
* Documentation of the contract (types vs runtime values)
* Foundation for completeness (Layer 9's other half)

## Dependencies

* `Algo/Check.lean`
* `Algo/Infer.lean`

## Downstream

* `Algo/Completeness.lean` — completeness builds on soundness
* `Pipeline.lean` — pipeline composition needs both

## Implementation plan (Layer 9)

1. State soundness theorems
2. Most cases: trivial via Lean's type checker
3. Smoke: round-trip
-/

namespace LeanFX2.Algo

-- TODO Layer 9: soundness theorems for infer + check

end LeanFX2.Algo
