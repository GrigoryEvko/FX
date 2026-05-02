import LeanFX2.Reduction.Step
import LeanFX2.Reduction.StepStar

/-! # Smoke/Reduction — β/ι reduction examples.

```lean
-- (λx. x) () → ()
example : Step (Term.app (Term.lam (Term.var ⟨0, _⟩)) Term.unit) Term.unit :=
  Step.betaApp _ _

-- if true then a else b → a
example : Step (Term.boolElim Term.boolTrue a b) a :=
  Step.iotaBoolElimTrue ...

-- (succ 0) becomes itself by refl (already in NF)
example : StepStar (Term.natSucc Term.natZero) (Term.natSucc Term.natZero) :=
  StepStar.refl _
```

## Dependencies

* `Reduction/Step.lean`, `Reduction/StepStar.lean`

## Implementation plan (Layer 14)

1. β-app, β-pair, β-arrow examples
2. ι-bool, ι-nat, ι-list, ι-option, ι-either examples
3. ι-idJ on refl
4. Multi-step chain examples
-/

namespace LeanFX2.Smoke

-- TODO: reduction examples

end LeanFX2.Smoke
