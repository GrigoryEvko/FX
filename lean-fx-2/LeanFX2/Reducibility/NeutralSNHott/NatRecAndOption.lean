import LeanFX2.Reducibility.NeutralSNHott.NatElim

/-! # LeanFX2.Reducibility.NeutralSNHott.NatRecAndOption

The general `natRec` SN preservation theorems formerly shipped from
this file (`RawTerm.natRec_isStronglyNormalizing` and
`Term.natRec_isStronglyNormalizing`) carried a universally-quantified
`contractumIsSN : ∀ {predecessor zeroTarget succTarget}, ... → SN
(app (app succTarget predecessor) (natRec predecessor zeroTarget
succTarget))` Pi-type hypothesis over the raw successor ι contractum.
At the raw layer the hypothesis is not provable in general; it was a
hypothesis-as-postulate banned by `CLAUDE.md` "Forbidden reasoning
patterns".  Both theorems have been DELETED — they will return as
genuine consequences of the M04 fundamental theorem once it lands.

The `optionSome` unary cong-only closure (pure structural induction
over SN witness + ctor-injectivity) is clean and remains shipped. -/

namespace LeanFX2

/-- `optionSome` unary cong-only SN preservation.  Structural induction
on the value's SN witness + `optionSome_inv` for step inversion +
`RawTerm.optionSome` injectivity for the parProgress disequality. -/
theorem RawTerm.optionSome_isStronglyNormalizing {scope : Nat}
    {valueTerm : RawTerm scope}
    (valueIsSN : RawTerm.isStronglyNormalizing valueTerm) :
    RawTerm.isStronglyNormalizing (RawTerm.optionSome valueTerm) := by
  induction valueIsSN with
  | intro currentValue _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.optionSome currentValue) ?_
    intro target progressStep
    obtain ⟨valueTarget, targetEq, valueStep⟩ :=
      RawStep.par.optionSome_inv progressStep.1
    subst targetEq
    have valueDistinct :
        currentValue ≠ valueTarget := fun valueEq =>
      progressStep.2 (congrArg RawTerm.optionSome valueEq)
    exact inductiveHypothesis valueTarget
      ⟨valueStep, valueDistinct⟩

end LeanFX2
