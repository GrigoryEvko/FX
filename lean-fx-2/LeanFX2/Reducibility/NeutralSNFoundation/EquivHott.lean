import LeanFX2.Reducibility.SN.Helpers

/-! # LeanFX2.Reducibility.NeutralSNFoundation.EquivHott

Equivalence application + univalent application SN preservation.
Surviving live theorems after the Tait `IsNeutral` cascade was
retired in favour of Kripke step-indexed reducibility:
`equivApp_isStronglyNormalizing` (cong-only at raw layer) and
`equivApply_isStronglyNormalizing` (cong + two refl-β arms), each
shipped with a typed wrapper consumed by Kripke fundamental. -/

namespace LeanFX2

/-- Equivalence application is strongly normalizing when both subterms are.

Unlike raw application, `equivApp` has no β arm at the raw layer; every
parallel reduct is a congruent reduct of the equivalence term and
argument. -/
theorem RawTerm.equivApp_isStronglyNormalizing {scope : Nat}
    {equivRaw argumentRaw : RawTerm scope}
    (equivIsSN : RawTerm.isStronglyNormalizing equivRaw)
    (argumentIsSN : RawTerm.isStronglyNormalizing argumentRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.equivApp equivRaw argumentRaw) := by
  induction equivIsSN generalizing argumentRaw with
  | intro currentEquiv _ equivIH =>
    induction argumentIsSN with
    | intro currentArgument argumentClosure argumentIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.equivApp currentEquiv currentArgument) ?_
      intro target progressStep
      obtain ⟨equivTarget, argumentTarget, targetEq,
          equivStep, argumentStep⟩ :=
        RawStep.par.equivApp_inv progressStep.1
      subst targetEq
      have argumentTargetIsSN :
          RawTerm.isStronglyNormalizing argumentTarget := by
        by_cases argumentEq : currentArgument = argumentTarget
        · subst argumentEq
          exact RawTerm.isStronglyNormalizing.intro
            currentArgument argumentClosure
        · exact argumentClosure argumentTarget
            ⟨argumentStep, argumentEq⟩
      by_cases equivEq : currentEquiv = equivTarget
      · subst equivEq
        by_cases argumentEq : currentArgument = argumentTarget
        · subst argumentEq
          exact (progressStep.2 rfl).elim
        · exact argumentIH argumentTarget
            ⟨argumentStep, argumentEq⟩
      · exact equivIH equivTarget
          ⟨equivStep, equivEq⟩ argumentTargetIsSN

/-- Typed wrapper for congruence-only equivalence application SN. -/
theorem Term.equivApp_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term context carrierA argumentRaw}
    (equivIsSN : Term.isStronglyNormalizing equivTerm)
    (argumentIsSN : Term.isStronglyNormalizing argumentTerm) :
    Term.isStronglyNormalizing
      (Term.equivApp equivTerm argumentTerm) :=
  RawTerm.equivApp_isStronglyNormalizing equivIsSN argumentIsSN

/-- Univalent equivalence application is strongly normalizing when both
subterms are.  `RawTerm.equivApply`'s raw parallel reduction is mostly
binary congruence, with ua-refl β arms that return a reduct of the
source argument. -/
theorem RawTerm.equivApply_isStronglyNormalizing {scope : Nat}
    {equivRaw argumentRaw : RawTerm scope}
    (equivIsSN : RawTerm.isStronglyNormalizing equivRaw)
    (argumentIsSN : RawTerm.isStronglyNormalizing argumentRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.equivApply equivRaw argumentRaw) := by
  induction equivIsSN generalizing argumentRaw with
  | intro currentEquiv _ equivInduction =>
    induction argumentIsSN with
    | intro currentArgument argumentClosure argumentInduction =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.equivApply currentEquiv currentArgument) ?_
      intro target progressStep
      rcases RawStep.par.equivApply_inv progressStep.1 with
        ⟨equivTarget, argumentTarget, targetEq, equivStep, argumentStep⟩
        | ⟨_witnessSource, _witnessTarget, sourceTarget, _equivEq,
            targetEq, _witnessStep, argumentStep⟩
        | ⟨_witnessTarget, sourceTarget, targetEq, _equivStep,
            argumentStep⟩
      · subst targetEq
        have argumentTargetIsSN :
            RawTerm.isStronglyNormalizing argumentTarget := by
          by_cases argumentEq : currentArgument = argumentTarget
          · subst argumentEq
            exact RawTerm.isStronglyNormalizing.intro
              currentArgument argumentClosure
          · exact argumentClosure argumentTarget
              ⟨argumentStep, argumentEq⟩
        by_cases equivEq : currentEquiv = equivTarget
        · subst equivEq
          by_cases argumentEq : currentArgument = argumentTarget
          · subst argumentEq
            exact (progressStep.2 rfl).elim
          · exact argumentInduction argumentTarget
              ⟨argumentStep, argumentEq⟩
        · exact equivInduction equivTarget
            ⟨equivStep, equivEq⟩ argumentTargetIsSN
      · rw [targetEq]
        by_cases argumentEq : currentArgument = sourceTarget
        · rw [← argumentEq]
          exact RawTerm.isStronglyNormalizing.intro
            currentArgument argumentClosure
        · exact argumentClosure sourceTarget
            ⟨argumentStep, argumentEq⟩
      · rw [targetEq]
        by_cases argumentEq : currentArgument = sourceTarget
        · rw [← argumentEq]
          exact RawTerm.isStronglyNormalizing.intro
            currentArgument argumentClosure
        · exact argumentClosure sourceTarget
            ⟨argumentStep, argumentEq⟩

/-- Typed wrapper for `RawTerm.equivApply_isStronglyNormalizing`. -/
theorem Term.equivApply_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term context carrierA argumentRaw}
    (equivIsSN : Term.isStronglyNormalizing equivTerm)
    (argumentIsSN : Term.isStronglyNormalizing argumentTerm) :
    Term.isStronglyNormalizing
      (Term.equivApply equivTerm argumentTerm) :=
  RawTerm.equivApply_isStronglyNormalizing equivIsSN argumentIsSN

end LeanFX2
