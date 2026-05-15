import LeanFX2.Reducibility.NeutralSNHott.NatRecAndOption

/-! # LeanFX2.Reducibility.NeutralSNIntro.Sums

`eitherInl` / `eitherInr` SN preservation.  The binary
`eitherMatch_eitherInl` / `eitherMatch_eitherInr` head-β ι-witnesses
were retired alongside the Tait-era `IsNeutral` cascade — the surviving
Kripke step-indexed reducibility chain consumes only the constructor-
introduction lemmas.
-/

namespace LeanFX2


/-- **eitherInl SN preservation**.  Unary cong-only ctor at the left
injection of Ty.eitherType. -/
theorem RawTerm.eitherInl_isStronglyNormalizing {scope : Nat}
    {valueTerm : RawTerm scope}
    (valueIsSN : RawTerm.isStronglyNormalizing valueTerm) :
    RawTerm.isStronglyNormalizing (RawTerm.eitherInl valueTerm) := by
  induction valueIsSN with
  | intro currentValue _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.eitherInl currentValue) ?_
    intro target progressStep
    obtain ⟨valueTarget, targetEq, valueStep⟩ :=
      RawStep.par.eitherInl_inv progressStep.1
    subst targetEq
    have valueDistinct :
        currentValue ≠ valueTarget := fun valueEq =>
      progressStep.2 (congrArg RawTerm.eitherInl valueEq)
    exact inductiveHypothesis valueTarget
      ⟨valueStep, valueDistinct⟩

/-- **eitherInr SN preservation**.  Mirror of
`eitherInl_isStronglyNormalizing` — same template, right injection. -/
theorem RawTerm.eitherInr_isStronglyNormalizing {scope : Nat}
    {valueTerm : RawTerm scope}
    (valueIsSN : RawTerm.isStronglyNormalizing valueTerm) :
    RawTerm.isStronglyNormalizing (RawTerm.eitherInr valueTerm) := by
  induction valueIsSN with
  | intro currentValue _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.eitherInr currentValue) ?_
    intro target progressStep
    obtain ⟨valueTarget, targetEq, valueStep⟩ :=
      RawStep.par.eitherInr_inv progressStep.1
    subst targetEq
    have valueDistinct :
        currentValue ≠ valueTarget := fun valueEq =>
      progressStep.2 (congrArg RawTerm.eitherInr valueEq)
    exact inductiveHypothesis valueTarget
      ⟨valueStep, valueDistinct⟩


end LeanFX2
