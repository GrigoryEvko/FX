import LeanFX2.Reducibility.NeutralSNClosure.HottCompose

/-! # LeanFX2.Reducibility.NeutralSNClosure.GlueEquiv

K12.20.AM Glue SN preservation: `glueIntro`,
`glueElim_glueIntro`, `glueElim` (raw + Term wrappers); plus the
K12.20.AQ equivalence-type intro: `equivIntro` (raw),
`equivIntroHet` (Term).

## Root status

Layer 3 metatheory leaf.  Fifth and final slice of NeutralSNClosure. -/

namespace LeanFX2


/-- **K12.20.AM glueIntro SN preservation** — cubical Glue
introduction bundles a base value with a partial-element witness.
Pure binary cong; pair-style universal-in-conclusion.  Closes
the cubical/HoTT intro slice of the SN-helper rail. -/
theorem RawTerm.glueIntro_isStronglyNormalizing {scope : Nat}
    {baseValue : RawTerm scope}
    (baseIsSN : RawTerm.isStronglyNormalizing baseValue) :
    ∀ {partialValue : RawTerm scope},
      RawTerm.isStronglyNormalizing partialValue →
      RawTerm.isStronglyNormalizing
        (RawTerm.glueIntro baseValue partialValue) := by
  induction baseIsSN with
  | intro currentBase _ baseIH =>
    intro partialValue partialIsSN
    induction partialIsSN with
    | intro currentPartial partialClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.glueIntro currentBase currentPartial) ?_
      intro target progressStep
      obtain ⟨baseTarget, partialTarget, targetEq,
              baseStep, partialStep⟩ :=
        RawStep.par.glueIntro_inv progressStep.1
      subst targetEq
      by_cases baseEq : currentBase = baseTarget
      · subst baseEq
        have partialDistinct :
            currentPartial ≠ partialTarget := fun partialEq =>
          progressStep.2
            (congrArg (RawTerm.glueIntro currentBase) partialEq)
        exact innerIH partialTarget ⟨partialStep, partialDistinct⟩
      · have baseProgress :
            RawStep.parProgress currentBase baseTarget :=
          ⟨baseStep, baseEq⟩
        by_cases partialEq : currentPartial = partialTarget
        · subst partialEq
          exact baseIH baseTarget baseProgress
            (RawTerm.isStronglyNormalizing.intro currentPartial
              partialClosure)
        · exact baseIH baseTarget baseProgress
            (partialClosure partialTarget
              ⟨partialStep, partialEq⟩)

/-- Typed wrapper for cubical Glue-introduction SN preservation.

This exposes SN for `Term.glueIntro` from SN of its base and partial
payloads.  It deliberately does not claim the full Glue Reducible
introduction closure. -/
theorem Term.glueIntro_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level scope)
    (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    {baseValue : Term context baseType baseRaw}
    {partialValue : Term context baseType partialRaw}
    (baseIsSN : Term.isStronglyNormalizing baseValue)
    (partialIsSN : Term.isStronglyNormalizing partialValue) :
    Term.isStronglyNormalizing
      (Term.glueIntro modeIsUnivalent baseType boundaryWitness
        baseValue partialValue) :=
  RawTerm.glueIntro_isStronglyNormalizing baseIsSN partialIsSN

/-- Head-β SN expansion for cubical Glue elimination.

If the Glue base value and partial value are strongly normalizing, then
`glueElim (glueIntro base partial)` is strongly normalizing.  Congruence
reducts recurse through both payloads; β reducts land on a reduct of the
base payload. -/
theorem RawTerm.glueElim_glueIntro_isStronglyNormalizing
    {scope : Nat}
    {baseValue : RawTerm scope}
    (baseIsSN : RawTerm.isStronglyNormalizing baseValue) :
    ∀ {partialValue : RawTerm scope},
      RawTerm.isStronglyNormalizing partialValue →
      RawTerm.isStronglyNormalizing
        (RawTerm.glueElim
          (RawTerm.glueIntro baseValue partialValue)) := by
  induction baseIsSN with
  | intro currentBase baseClosure baseIH =>
    intro partialValue partialIsSN
    induction partialIsSN with
    | intro currentPartial partialClosure partialIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.glueElim
          (RawTerm.glueIntro currentBase currentPartial)) ?_
      intro target progressStep
      rcases RawStep.par.glueElim_inv progressStep.1 with
        ⟨gluedTarget, targetEq, gluedStep⟩
        | ⟨baseTarget, partialTarget, targetEq, gluedStep⟩
      · obtain ⟨baseTarget, partialTarget, gluedTargetEq,
            baseStep, partialStep⟩ :=
          RawStep.par.glueIntro_inv gluedStep
        subst gluedTargetEq
        subst targetEq
        by_cases baseEq : currentBase = baseTarget
        · subst baseEq
          by_cases partialEq : currentPartial = partialTarget
          · subst partialEq
            exact False.elim (progressStep.2 rfl)
          · exact partialIH partialTarget
              ⟨partialStep, partialEq⟩
        · have baseProgress :
              RawStep.parProgress currentBase baseTarget :=
            ⟨baseStep, baseEq⟩
          by_cases partialEq : currentPartial = partialTarget
          · subst partialEq
            exact baseIH baseTarget baseProgress
              (RawTerm.isStronglyNormalizing.intro currentPartial
                partialClosure)
          · exact baseIH baseTarget baseProgress
              (partialClosure partialTarget
                ⟨partialStep, partialEq⟩)
      · obtain ⟨gluedBaseTarget, _gluedPartialTarget,
            gluedTargetEq, baseStep, _partialStep⟩ :=
          RawStep.par.glueIntro_inv gluedStep
        injection gluedTargetEq with _scopeEq baseTargetEq
          _partialTargetEq
        rw [targetEq]
        have baseStepToTarget :
            RawStep.par currentBase baseTarget := by
          rw [baseTargetEq]
          exact baseStep
        by_cases baseEq : currentBase = baseTarget
        · subst baseEq
          exact RawTerm.isStronglyNormalizing.intro
            currentBase baseClosure
        · exact baseClosure baseTarget
            ⟨baseStepToTarget, baseEq⟩

/-- Typed wrapper for `glueElim (glueIntro base partial)` SN expansion.

This is an SN bridge only.  It does not claim the full `Reducible`
backward closure for Glue introduction. -/
theorem Term.glueElim_glueIntro_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level scope)
    (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    {baseValue : Term context baseType baseRaw}
    {partialValue : Term context baseType partialRaw}
    (baseIsSN : Term.isStronglyNormalizing baseValue)
    (partialIsSN : Term.isStronglyNormalizing partialValue) :
    Term.isStronglyNormalizing
      (Term.glueElim modeIsUnivalent
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness
          baseValue partialValue)) :=
  RawTerm.glueElim_glueIntro_isStronglyNormalizing
    baseIsSN partialIsSN

/-- Generic Glue-elimination SN preservation.

Congruent reducts recurse through the glued term.  A β reduct first
develops the glued term into a `glueIntro`; the eliminated base value is
SN by the Glue-intro base inversion lemma. -/
theorem RawTerm.glueElim_isStronglyNormalizing {scope : Nat}
    {gluedRaw : RawTerm scope}
    (gluedIsSN : RawTerm.isStronglyNormalizing gluedRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.glueElim gluedRaw) := by
  induction gluedIsSN with
  | intro currentGlued gluedClosure gluedIH =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.glueElim currentGlued) ?_
    intro target progressStep
    rcases RawStep.par.glueElim_inv progressStep.1 with
      ⟨gluedTarget, targetEq, gluedStep⟩
      | ⟨baseTarget, partialTarget, targetEq, gluedStep⟩
    · subst targetEq
      by_cases gluedEq : currentGlued = gluedTarget
      · subst gluedEq
        exact (progressStep.2 rfl).elim
      · exact gluedIH gluedTarget ⟨gluedStep, gluedEq⟩
    · rw [targetEq]
      have developedGluedIsSN :
          RawTerm.isStronglyNormalizing
            (RawTerm.glueIntro baseTarget partialTarget) := by
        by_cases gluedEq :
            currentGlued =
              RawTerm.glueIntro baseTarget partialTarget
        · rw [← gluedEq]
          exact RawTerm.isStronglyNormalizing.intro
            currentGlued gluedClosure
        · exact gluedClosure
            (RawTerm.glueIntro baseTarget partialTarget)
            ⟨gluedStep, gluedEq⟩
      exact RawTerm.glueIntro_base_isStronglyNormalizing
        developedGluedIsSN

/-- Direct M04 SN case for Glue elimination from any SN glued term. -/
theorem Term.glueElim_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    {gluedValue : Term context
        (Ty.glue baseType boundaryWitness) gluedRaw}
    (gluedIsSN : Term.isStronglyNormalizing gluedValue) :
    Term.isStronglyNormalizing
      (Term.glueElim modeIsUnivalent gluedValue) :=
  RawTerm.glueElim_isStronglyNormalizing gluedIsSN

/-- **K12.20.AH equivIntro SN preservation** — equivalence intro
bundles a forward and backward function.  Binary cong; uses the
pair-style universal-in-conclusion pattern to keep the backward
IH universal under outer induction on the forward SN witness. -/
theorem RawTerm.equivIntro_isStronglyNormalizing {scope : Nat}
    {forwardFn : RawTerm scope}
    (forwardIsSN : RawTerm.isStronglyNormalizing forwardFn) :
    ∀ {backwardFn : RawTerm scope},
      RawTerm.isStronglyNormalizing backwardFn →
      RawTerm.isStronglyNormalizing
        (RawTerm.equivIntro forwardFn backwardFn) := by
  induction forwardIsSN with
  | intro currentForward _ forwardIH =>
    intro backwardFn backwardIsSN
    induction backwardIsSN with
    | intro currentBackward backwardClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.equivIntro currentForward currentBackward) ?_
      intro target progressStep
      obtain ⟨forwardTarget, backwardTarget, targetEq,
              forwardStep, backwardStep⟩ :=
        RawStep.par.equivIntro_inv progressStep.1
      subst targetEq
      by_cases forwardEq : currentForward = forwardTarget
      · subst forwardEq
        have backwardDistinct :
            currentBackward ≠ backwardTarget := fun backwardEq =>
          progressStep.2
            (congrArg (RawTerm.equivIntro currentForward) backwardEq)
        exact innerIH backwardTarget ⟨backwardStep, backwardDistinct⟩
      · have forwardProgress :
            RawStep.parProgress currentForward forwardTarget :=
          ⟨forwardStep, forwardEq⟩
        by_cases backwardEq : currentBackward = backwardTarget
        · subst backwardEq
          exact forwardIH forwardTarget forwardProgress
            (RawTerm.isStronglyNormalizing.intro currentBackward
              backwardClosure)
        · exact forwardIH forwardTarget forwardProgress
            (backwardClosure backwardTarget ⟨backwardStep, backwardEq⟩)

/-- Typed wrapper for heterogeneous equivalence-introduction SN.

`Term.equivIntroHet` has raw shape `RawTerm.equivIntro forward backward`;
the proof witnesses are typed obligations and do not occur in the raw
computational payload.  Thus SN depends only on the forward and backward
functions.  This is an SN bridge, not the full `Ty.equiv` Reducible
introduction closure. -/
theorem Term.equivIntroHet_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    {forward :
      Term context (Ty.arrow carrierA carrierB) forwardRaw}
    {backward :
      Term context (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
      Term context
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw}
    {rightInv :
      Term context
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw}
    (forwardIsSN : Term.isStronglyNormalizing forward)
    (backwardIsSN : Term.isStronglyNormalizing backward) :
    Term.isStronglyNormalizing
      (Term.equivIntroHet forward backward leftInv rightInv) :=
  RawTerm.equivIntro_isStronglyNormalizing forwardIsSN backwardIsSN



end LeanFX2
