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


end LeanFX.Syntax
