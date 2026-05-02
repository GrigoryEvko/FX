import LeanFX2.Modal.Foundation

/-! # Smoke/Modal — modal computation rules.

```lean
-- modElim of modIntro reduces (iota for modal)
example {term : Term ctx ty raw} :
    Step (Term.modElim (Term.modIntro modality term) cont) ... :=
  Step.iotaModal ...

-- subsume by refl 2-cell is identity
example {term : Term ctx (Ty.modal m ty) raw} :
    Step (Term.subsume (TwoCell.refl m) term) term :=
  Step.iotaSubsumeId ...

-- Subsume composition: subsume α (subsume β t) = subsume (α ∘ β) t
example : Step.iotaSubsumeComp ...
```

## Dependencies

* `Modal/Foundation.lean`

## Implementation plan (Layer 14)

1. iotaModal: modElim of modIntro
2. iotaSubsumeId: refl-subsume identity
3. iotaSubsumeComp: subsume composition
4. Concrete modality examples (Later, Bridge, Cap, Ghost)
-/

namespace LeanFX2.Smoke

-- TODO: modal smoke examples

end LeanFX2.Smoke
