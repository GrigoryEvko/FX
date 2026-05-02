import LeanFX2.Confluence.ChurchRosser
import LeanFX2.Confluence.CanonicalForm

/-! # Smoke/Confluence — diamond + Church-Rosser on representative terms.

```lean
-- Step.par.diamond on a simple branching term
example (t1 t2 : Term ctx ty raw1) (t3 : Term ctx ty raw2)
    (s1 : Step.par t1 t2) (s2 : Step.par t1 t3) :
    ∃ t', Step.par t2 t' ∧ Step.par t3 t' :=
  Step.par.diamond s1 s2

-- Conv canonical form: convertible terms reach a common reduct
example (h : Conv t1 t2) :
    ∃ t', StepStar t1 t' ∧ StepStar t2 t' :=
  Conv.canonical_form h
```

## Dependencies

* `Confluence/ChurchRosser.lean`, `Confluence/CanonicalForm.lean`

## Implementation plan (Layer 14)

1. Diamond on simple β-redex branching
2. Multi-step confluence on a 3-arm fan
3. Conv canonical form on identity, β-conversion examples
4. Identity-type-bearing examples (the bridge edge case)
-/

namespace LeanFX2.Smoke

-- TODO: confluence smoke examples

end LeanFX2.Smoke
