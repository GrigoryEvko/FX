import LeanFX2.Reducibility.SNHelpers
import LeanFX2.Reducibility.Neutral.ModalAdvancedPreservation

/-! # LeanFX2.Reducibility.NeutralSNFoundation.EquivHott

Equivalence + HoTT-J SN preservation.  Covers `equivApp` family
(`_neutral` / `_var` / unrestricted + typed mirror), `equivApply`
(raw + typed), and `idJ_var` / `idJ_neutral`.

## Root status

Layer 3 metatheory leaf.  Fifth slice of NeutralSNFoundation. -/

namespace LeanFX2

/-- Equivalence application with a neutral equivalence head is strongly
normalizing when both the equivalence head and argument are strongly
normalizing.

Unlike raw application, `equivApp` has no beta arm at the raw layer;
`RawStep.par.equivApp_inv` is congruence-only.  The proof therefore
recurses on head progress or argument progress, with the no-progress
case discharged by the strict progress witness. -/
theorem RawTerm.equivApp_neutral_isStronglyNormalizing {scope : Nat}
    {equivRaw argumentRaw : RawTerm scope}
    (equivIsNeutral : RawTerm.IsNeutral equivRaw)
    (equivIsSN : RawTerm.isStronglyNormalizing equivRaw)
    (argumentIsSN : RawTerm.isStronglyNormalizing argumentRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.equivApp equivRaw argumentRaw) := by
  induction equivIsSN generalizing argumentRaw with
  | intro currentEquiv _ equivInduction =>
    induction argumentIsSN with
    | intro currentArgument argumentClosure argumentInduction =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.equivApp currentEquiv currentArgument) ?_
      intro target progressStep
      obtain ⟨equivTarget, argumentTarget, targetEq,
          equivStep, argumentStep⟩ :=
        RawStep.par.equivApp_inv progressStep.1
      subst targetEq
      have equivTargetIsNeutral :
          RawTerm.IsNeutral equivTarget :=
        RawTerm.IsNeutral.par_preserves equivIsNeutral equivStep
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
          ⟨equivStep, equivEq⟩
          equivTargetIsNeutral
          argumentTargetIsSN

/-- **K12.20.AX.2 neutral equivApp SN preservation**.  Sister to
`pathApp_var`; var sits in the equiv-term slot, argument is the SN
witness.  `equivApp_inv` is cong-only (no β rule at raw layer yet),
so no nomatch defense needed — the cong arm alone preserves SN
via inductive hypothesis. -/
theorem RawTerm.equivApp_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {argumentRaw : RawTerm scope}
    (argumentIsSN : RawTerm.isStronglyNormalizing argumentRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.equivApp (RawTerm.var position) argumentRaw) := by
  induction argumentIsSN with
  | intro currentArgument _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.equivApp (RawTerm.var position) currentArgument) ?_
    intro target progressStep
    obtain ⟨equivTarget, argumentTarget, targetEq, equivStep, argumentStep⟩ :=
      RawStep.par.equivApp_inv progressStep.1
    have equivEq : equivTarget = RawTerm.var position :=
      (RawStep.par.var_inv equivStep)
    subst equivEq
    subst targetEq
    have argumentDistinct :
        currentArgument ≠ argumentTarget := fun argumentEq =>
      progressStep.2
        (congrArg (RawTerm.equivApp (RawTerm.var position)) argumentEq)
    exact inductiveHypothesis argumentTarget
      ⟨argumentStep, argumentDistinct⟩

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

/-- Equivalence application is strongly normalizing when both subterms are.

`RawTerm.equivApply` is the univalence-target application form.  Its raw
parallel reduction is mostly binary congruence, with ua-refl beta arms that
return a reduct of the source argument.  Thus the proof is the same binary
SN induction as `hcomp`, except the beta arms discharge directly from the
argument SN witness. -/
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

/-- **K12.20.AX.3 neutral idJ SN preservation**.  HOTT J eliminator
with variable witness (the equality being eliminated).  `idJ_inv`
gives 2 arms (cong + iotaIdJRefl); ι arm requires
`witness → refl _`, defeated by `var_inv` + nomatch on
`var = refl _`.  Variable sits in the SECOND slot since
`Term.idJ baseCase witness` destructs `witness`. -/
theorem RawTerm.idJ_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {baseCaseRaw : RawTerm scope}
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.idJ baseCaseRaw (RawTerm.var position)) := by
  induction baseCaseIsSN with
  | intro currentBase _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.idJ currentBase (RawTerm.var position)) ?_
    intro target progressStep
    rcases RawStep.par.idJ_inv progressStep.1 with
      ⟨baseTarget, witnessTarget, targetEq, baseStep, witnessStep⟩
      | ⟨witnessRaw, _baseTarget, _targetEq, witnessStep, _baseStep⟩
    · have witnessEq : witnessTarget = RawTerm.var position :=
        (RawStep.par.var_inv witnessStep)
      subst witnessEq
      subst targetEq
      have baseDistinct :
          currentBase ≠ baseTarget := fun baseEq =>
        progressStep.2
          (congrArg (fun base => RawTerm.idJ base (RawTerm.var position))
            baseEq)
      exact inductiveHypothesis baseTarget
        ⟨baseStep, baseDistinct⟩
    · exact (by
        have varEqRefl :
            RawTerm.var position = RawTerm.refl witnessRaw :=
          (RawStep.par.var_inv witnessStep).symm
        nomatch varEqRefl)

/-- Identity eliminator with a neutral witness is strongly normalizing
when the witness and base case are strongly normalizing.

The refl-ι arm is impossible because every parallel reduct of the
neutral witness stays neutral, and neutral terms are never `refl`
shaped.  The congruence arm recurses on witness progress or base-case
progress. -/
theorem RawTerm.idJ_neutral_isStronglyNormalizing {scope : Nat}
    {baseCaseRaw witnessRaw : RawTerm scope}
    (witnessIsNeutral : RawTerm.IsNeutral witnessRaw)
    (witnessIsSN : RawTerm.isStronglyNormalizing witnessRaw)
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.idJ baseCaseRaw witnessRaw) := by
  induction witnessIsSN generalizing baseCaseRaw with
  | intro currentWitness _ witnessInduction =>
    induction baseCaseIsSN with
    | intro currentBase baseClosure baseInduction =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.idJ currentBase currentWitness) ?_
      intro target progressStep
      rcases RawStep.par.idJ_inv progressStep.1 with
        ⟨baseTarget, witnessTarget, targetEq,
          baseStep, witnessStep⟩
        | ⟨witnessReflRaw, _baseTarget, _targetEq,
            witnessStep, _baseStep⟩
      · subst targetEq
        have witnessTargetIsNeutral :
            RawTerm.IsNeutral witnessTarget :=
          RawTerm.IsNeutral.par_preserves witnessIsNeutral witnessStep
        have baseTargetIsSN :
            RawTerm.isStronglyNormalizing baseTarget := by
          by_cases baseEq : currentBase = baseTarget
          · subst baseEq
            exact RawTerm.isStronglyNormalizing.intro
              currentBase baseClosure
          · exact baseClosure baseTarget ⟨baseStep, baseEq⟩
        by_cases witnessEq : currentWitness = witnessTarget
        · subst witnessEq
          by_cases baseEq : currentBase = baseTarget
          · subst baseEq
            exact (progressStep.2 rfl).elim
          · exact baseInduction baseTarget ⟨baseStep, baseEq⟩
        · exact witnessInduction witnessTarget
            ⟨witnessStep, witnessEq⟩
            witnessTargetIsNeutral baseTargetIsSN
      · exact (RawTerm.IsNeutral.not_refl
          (RawTerm.IsNeutral.par_preserves witnessIsNeutral witnessStep)
          (witnessRaw := witnessReflRaw) rfl).elim


end LeanFX2
