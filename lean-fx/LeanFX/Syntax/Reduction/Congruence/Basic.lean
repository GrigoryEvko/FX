import LeanFX.Syntax.Reduction.Conv

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}


/-- Append a single step to an existing multi-step path — companion
to `StepStar.step` (which prepends).  Both directions are useful for
trace manipulation in conversion algorithms. -/
theorem StepStar.append
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ t₃ : Term ctx T} :
    StepStar t₁ t₂ → Step t₂ t₃ → StepStar t₁ t₃ :=
  fun stars step =>
    StepStar.trans stars (Step.toStar step)

/-- Lift a multi-step reduction through a term context that preserves
single-step reduction.  This is the generic proof pattern behind the
constructor-specific `StepStar.*_cong` lemmas. -/
theorem StepStar.mapStep
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    (mapTerm : Term ctx sourceType → Term ctx targetType)
    (mapSingleStep :
      ∀ {beforeTerm afterTerm : Term ctx sourceType},
        Step beforeTerm afterTerm →
        Step (mapTerm beforeTerm) (mapTerm afterTerm)) :
    ∀ {beforeTerm afterTerm : Term ctx sourceType},
      StepStar beforeTerm afterTerm →
      StepStar (mapTerm beforeTerm) (mapTerm afterTerm)
  | _, _, .refl _ => StepStar.refl _
  | _, _, .step singleStep remainingSteps =>
      StepStar.step (mapSingleStep singleStep)
        (StepStar.mapStep mapTerm mapSingleStep remainingSteps)

end LeanFX.Syntax
