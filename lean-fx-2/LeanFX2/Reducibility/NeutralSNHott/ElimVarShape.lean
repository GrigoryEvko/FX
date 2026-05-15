import LeanFX2.Reducibility.NeutralSNHott.HottJ

/-! # LeanFX2.Reducibility.NeutralSNHott.ElimVarShape

`natSucc` SN preservation — sole live atom remaining after the
Tait IsNeutral cascade was retired in favour of Kripke step-
indexed reducibility.  The Term-SN.DirectCases consumer needs the
unary cong-only closure for `natSucc`. -/

namespace LeanFX2

/-- `RawTerm.natSucc predecessor` is SN when predecessor is.
Structural induction on predecessor's SN witness + step inversion
via `natSucc_inv` + ctor-injectivity for the disequality. -/
theorem RawTerm.natSucc_isStronglyNormalizing {scope : Nat}
    {predecessor : RawTerm scope}
    (predecessorIsSN : RawTerm.isStronglyNormalizing predecessor) :
    RawTerm.isStronglyNormalizing (RawTerm.natSucc predecessor) := by
  induction predecessorIsSN with
  | intro currentPredecessor _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.natSucc currentPredecessor) ?_
    intro target progressStep
    obtain ⟨predecessorTarget, targetEq, predecessorStep⟩ :=
      RawStep.par.natSucc_inv progressStep.1
    subst targetEq
    have predecessorDistinct :
        currentPredecessor ≠ predecessorTarget := fun predecessorEq =>
      progressStep.2 (congrArg RawTerm.natSucc predecessorEq)
    exact inductiveHypothesis predecessorTarget
      ⟨predecessorStep, predecessorDistinct⟩

end LeanFX2
