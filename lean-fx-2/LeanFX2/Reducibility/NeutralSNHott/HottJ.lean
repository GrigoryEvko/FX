import LeanFX2.Reducibility.NeutralSNFoundation.EquivHott

/-! # LeanFX2.Reducibility.NeutralSNHott.HottJ

HoTT-J family SN preservation.  Surviving live theorems after the
Tait `IsNeutral` cascade was retired in favour of Kripke step-
indexed reducibility: generic SN closures for `oeqJ`, `idJ`, and
`idStrictRec`.  Each ships with cong + (where applicable) refl-ι
arms following the nested-SN induction pattern. -/

namespace LeanFX2

/-- Observational-equality eliminator SN preservation.  Unlike
`idJ` and `idStrictRec`, the current raw `oeqJ` fragment has no
refl-ι firing rule; `RawStep.par.oeqJ_inv` is pure congruence over
the base case and witness. -/
theorem RawTerm.oeqJ_isStronglyNormalizing {scope : Nat}
    {baseCaseRaw : RawTerm scope}
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    ∀ {witnessRaw : RawTerm scope},
      RawTerm.isStronglyNormalizing witnessRaw →
      RawTerm.isStronglyNormalizing
        (RawTerm.oeqJ baseCaseRaw witnessRaw) := by
  induction baseCaseIsSN with
  | intro currentBase _ baseIH =>
    intro witnessRaw witnessIsSN
    induction witnessIsSN with
    | intro currentWitness witnessClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.oeqJ currentBase currentWitness) ?_
      intro target progressStep
      obtain ⟨baseTarget, witnessTarget, targetEq,
              baseStep, witnessStep⟩ :=
        RawStep.par.oeqJ_inv progressStep.1
      subst targetEq
      by_cases baseEq : currentBase = baseTarget
      · subst baseEq
        have witnessDistinct :
            currentWitness ≠ witnessTarget := fun witnessEq =>
          progressStep.2
            (congrArg (RawTerm.oeqJ currentBase) witnessEq)
        exact innerIH witnessTarget ⟨witnessStep, witnessDistinct⟩
      · have baseProgress :
            RawStep.parProgress currentBase baseTarget :=
          ⟨baseStep, baseEq⟩
        by_cases witnessEq : currentWitness = witnessTarget
        · subst witnessEq
          exact baseIH baseTarget baseProgress
            (RawTerm.isStronglyNormalizing.intro currentWitness
              witnessClosure)
        · exact baseIH baseTarget baseProgress
            (witnessClosure witnessTarget ⟨witnessStep, witnessEq⟩)

/-- Identity eliminator SN preservation.  Unlike `oeqJ`, `idJ` has
refl-ι rules, so the iota arm returns the reduced base case directly.
The congruence arm follows the same nested-SN induction pattern as
`RawTerm.oeqJ_isStronglyNormalizing`. -/
theorem RawTerm.idJ_isStronglyNormalizing {scope : Nat}
    {baseCaseRaw : RawTerm scope}
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    ∀ {witnessRaw : RawTerm scope},
      RawTerm.isStronglyNormalizing witnessRaw →
      RawTerm.isStronglyNormalizing
        (RawTerm.idJ baseCaseRaw witnessRaw) := by
  induction baseCaseIsSN with
  | intro currentBase baseClosure baseIH =>
    intro witnessRaw witnessIsSN
    induction witnessIsSN with
    | intro currentWitness witnessClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.idJ currentBase currentWitness) ?_
      intro target progressStep
      cases RawStep.par.idJ_inv progressStep.1 with
      | inl congruentStep =>
        rcases congruentStep with
          ⟨baseTarget, witnessTarget, targetEq, baseStep, witnessStep⟩
        subst targetEq
        by_cases baseEq : currentBase = baseTarget
        · subst baseEq
          have witnessDistinct :
              currentWitness ≠ witnessTarget := fun witnessEq =>
            progressStep.2
              (congrArg (RawTerm.idJ currentBase) witnessEq)
          exact innerIH witnessTarget ⟨witnessStep, witnessDistinct⟩
        · have baseProgress :
              RawStep.parProgress currentBase baseTarget :=
            ⟨baseStep, baseEq⟩
          by_cases witnessEq : currentWitness = witnessTarget
          · subst witnessEq
            exact baseIH baseTarget baseProgress
              (RawTerm.isStronglyNormalizing.intro currentWitness
                witnessClosure)
          · exact baseIH baseTarget baseProgress
              (witnessClosure witnessTarget ⟨witnessStep, witnessEq⟩)
      | inr iotaStep =>
        rcases iotaStep with
          ⟨_witnessRaw, baseTarget, targetEq, _witnessStep, baseStep⟩
        rw [targetEq]
        by_cases baseEq : currentBase = baseTarget
        · subst baseEq
          exact RawTerm.isStronglyNormalizing.intro currentBase baseClosure
        · exact baseClosure baseTarget ⟨baseStep, baseEq⟩

/-- Strict identity recursor SN preservation.  This mirrors
`RawTerm.idJ_isStronglyNormalizing`, with the strict reflexivity
constructor in the iota arm. -/
theorem RawTerm.idStrictRec_isStronglyNormalizing {scope : Nat}
    {baseCaseRaw : RawTerm scope}
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    ∀ {witnessRaw : RawTerm scope},
      RawTerm.isStronglyNormalizing witnessRaw →
      RawTerm.isStronglyNormalizing
        (RawTerm.idStrictRec baseCaseRaw witnessRaw) := by
  induction baseCaseIsSN with
  | intro currentBase baseClosure baseIH =>
    intro witnessRaw witnessIsSN
    induction witnessIsSN with
    | intro currentWitness witnessClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.idStrictRec currentBase currentWitness) ?_
      intro target progressStep
      cases RawStep.par.idStrictRec_inv progressStep.1 with
      | inl congruentStep =>
        rcases congruentStep with
          ⟨baseTarget, witnessTarget, targetEq, baseStep, witnessStep⟩
        subst targetEq
        by_cases baseEq : currentBase = baseTarget
        · subst baseEq
          have witnessDistinct :
              currentWitness ≠ witnessTarget := fun witnessEq =>
            progressStep.2
              (congrArg (RawTerm.idStrictRec currentBase) witnessEq)
          exact innerIH witnessTarget ⟨witnessStep, witnessDistinct⟩
        · have baseProgress :
              RawStep.parProgress currentBase baseTarget :=
            ⟨baseStep, baseEq⟩
          by_cases witnessEq : currentWitness = witnessTarget
          · subst witnessEq
            exact baseIH baseTarget baseProgress
              (RawTerm.isStronglyNormalizing.intro currentWitness
                witnessClosure)
          · exact baseIH baseTarget baseProgress
              (witnessClosure witnessTarget ⟨witnessStep, witnessEq⟩)
      | inr iotaStep =>
        rcases iotaStep with
          ⟨_reflRawArgument, baseTarget, targetEq, _witnessStep, baseStep⟩
        rw [targetEq]
        by_cases baseEq : currentBase = baseTarget
        · subst baseEq
          exact RawTerm.isStronglyNormalizing.intro currentBase baseClosure
        · exact baseClosure baseTarget ⟨baseStep, baseEq⟩

end LeanFX2
