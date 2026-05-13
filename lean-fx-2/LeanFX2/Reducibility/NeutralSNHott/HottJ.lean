import LeanFX2.Reducibility.NeutralSNFoundation

/-! # LeanFX2.Reducibility.NeutralSNHott.HottJ

K12.20.AX HoTT-J recursor SN preservation:
`oeqJ_var` / `oeqJ` / `oeqJ_neutral`, `idJ`,
`idStrictRec_var` / `idStrictRec` / `idStrictRec_neutral`,
plus the `weaken_id` / `weaken_oeq` / `weaken_idStrict` future-
world weakening lemmas for the three identity-type families.

## Root status

Layer 3 metatheory leaf.  First slice of NeutralSNHott. -/

namespace LeanFX2


/-- **K12.20.AX.4 neutral oeqJ SN preservation**.  Observational
equality J eliminator with variable witness.  `oeqJ_inv` is
cong-only (no ι rule at raw layer yet; oeq-style witness elimination
deferred), so no nomatch defense needed.  Same proof pattern as
`equivApp_var` but with var in the SECOND slot. -/
theorem RawTerm.oeqJ_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {baseCaseRaw : RawTerm scope}
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.oeqJ baseCaseRaw (RawTerm.var position)) := by
  induction baseCaseIsSN with
  | intro currentBase _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.oeqJ currentBase (RawTerm.var position)) ?_
    intro target progressStep
    obtain ⟨baseTarget, witnessTarget, targetEq, baseStep, witnessStep⟩ :=
      RawStep.par.oeqJ_inv progressStep.1
    have witnessEq : witnessTarget = RawTerm.var position :=
      (RawStep.par.var_inv witnessStep)
    subst witnessEq
    subst targetEq
    have baseDistinct :
        currentBase ≠ baseTarget := fun baseEq =>
      progressStep.2
        (congrArg (fun base => RawTerm.oeqJ base (RawTerm.var position))
          baseEq)
    exact inductiveHypothesis baseTarget
      ⟨baseStep, baseDistinct⟩

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

/-- Observational-equality eliminator with a neutral witness is
strongly normalizing when the witness and base case are strongly
normalizing.

The current raw `oeqJ` fragment is congruence-only, so this helper
records the neutral CR3 shape without a canonical-exclusion branch. -/
theorem RawTerm.oeqJ_neutral_isStronglyNormalizing {scope : Nat}
    {baseCaseRaw witnessRaw : RawTerm scope}
    (witnessIsNeutral : RawTerm.IsNeutral witnessRaw)
    (witnessIsSN : RawTerm.isStronglyNormalizing witnessRaw)
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.oeqJ baseCaseRaw witnessRaw) := by
  induction witnessIsSN generalizing baseCaseRaw with
  | intro currentWitness _ witnessInduction =>
    induction baseCaseIsSN with
    | intro currentBase baseClosure baseInduction =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.oeqJ currentBase currentWitness) ?_
      intro target progressStep
      obtain ⟨baseTarget, witnessTarget, targetEq,
              baseStep, witnessStep⟩ :=
        RawStep.par.oeqJ_inv progressStep.1
      subst targetEq
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

/-- **K12.20.AX.5 neutral idStrictRec SN preservation**.  Strict-id
recursor with variable witness.  `idStrictRec_inv` gives 2 arms
(cong + iotaIdStrictRecRefl); ι arm requires
`witness → idStrictRefl _`, defeated by `var_inv` + nomatch on
`var = idStrictRefl _`. -/
theorem RawTerm.idStrictRec_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {baseCaseRaw : RawTerm scope}
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.idStrictRec baseCaseRaw (RawTerm.var position)) := by
  induction baseCaseIsSN with
  | intro currentBase _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.idStrictRec currentBase (RawTerm.var position)) ?_
    intro target progressStep
    rcases RawStep.par.idStrictRec_inv progressStep.1 with
      ⟨baseTarget, witnessTarget, targetEq, baseStep, witnessStep⟩
      | ⟨reflRawArgument, _baseTarget, _targetEq, witnessStep, _baseStep⟩
    · have witnessEq : witnessTarget = RawTerm.var position :=
        (RawStep.par.var_inv witnessStep)
      subst witnessEq
      subst targetEq
      have baseDistinct :
          currentBase ≠ baseTarget := fun baseEq =>
        progressStep.2
          (congrArg
            (fun base => RawTerm.idStrictRec base (RawTerm.var position))
            baseEq)
      exact inductiveHypothesis baseTarget
        ⟨baseStep, baseDistinct⟩
    · exact (by
        have varEqIdStrictRefl :
            RawTerm.var position = RawTerm.idStrictRefl reflRawArgument :=
          (RawStep.par.var_inv witnessStep).symm
        nomatch varEqIdStrictRefl)

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

/-- Strict identity recursor with a neutral witness is strongly
normalizing when the witness and base case are strongly normalizing.

The strict-refl ι arm is impossible because every parallel reduct of
the neutral witness stays neutral, and neutral terms are never
`idStrictRefl` shaped.  The typed mode witness for `Term.idStrictRec`
is absent at the raw layer; this helper tracks only the computational
base case and identity witness. -/
theorem RawTerm.idStrictRec_neutral_isStronglyNormalizing {scope : Nat}
    {baseCaseRaw witnessRaw : RawTerm scope}
    (witnessIsNeutral : RawTerm.IsNeutral witnessRaw)
    (witnessIsSN : RawTerm.isStronglyNormalizing witnessRaw)
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.idStrictRec baseCaseRaw witnessRaw) := by
  induction witnessIsSN generalizing baseCaseRaw with
  | intro currentWitness _ witnessInduction =>
    induction baseCaseIsSN with
    | intro currentBase baseClosure baseInduction =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.idStrictRec currentBase currentWitness) ?_
      intro target progressStep
      rcases RawStep.par.idStrictRec_inv progressStep.1 with
        ⟨baseTarget, witnessTarget, targetEq,
          baseStep, witnessStep⟩
        | ⟨reflRawArgument, _baseTarget, _targetEq,
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
      · exact (RawTerm.IsNeutral.not_idStrictRefl
          (RawTerm.IsNeutral.par_preserves witnessIsNeutral witnessStep)
          (witnessRaw := reflRawArgument) rfl).elim

/-- **K12.20.U3.monotone weak-J arm**: HoTT identity
reducibility weakens without a full world-monotone recursive
candidate.  The closure output is SN, so the extended-context J
case is rebuilt from raw `idJ` SN preservation. -/
theorem Reducible.weaken_id
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType carrierType : Ty level scope}
    {leftEndpoint rightEndpoint sourceRaw : RawTerm scope}
    {sourceTerm :
      Term context (Ty.id carrierType leftEndpoint rightEndpoint) sourceRaw}
    (sourceReducible :
      Reducible (Ty.id carrierType leftEndpoint rightEndpoint) sourceTerm) :
    Reducible ((Ty.id carrierType leftEndpoint rightEndpoint).weaken)
      (Term.weaken newType sourceTerm) := by
  refine
    ⟨Term.isStronglyNormalizing_weaken (newType := newType)
      sourceReducible.1, ?_⟩
  intro _motiveType _baseRaw _baseCase baseIsSN
  exact RawTerm.idJ_isStronglyNormalizing baseIsSN
    (Term.isStronglyNormalizing_weaken (newType := newType)
      sourceReducible.1)

/-- **K12.20.U3.monotone weak-J arm**: observational equality
reducibility weakens by rebuilding the SN-output eliminator closure
from raw `oeqJ` SN preservation. -/
theorem Reducible.weaken_oeq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType carrierType : Ty level scope}
    {leftEndpoint rightEndpoint sourceRaw : RawTerm scope}
    {sourceTerm :
      Term context (Ty.oeq carrierType leftEndpoint rightEndpoint) sourceRaw}
    (sourceReducible :
      Reducible (Ty.oeq carrierType leftEndpoint rightEndpoint) sourceTerm) :
    Reducible ((Ty.oeq carrierType leftEndpoint rightEndpoint).weaken)
      (Term.weaken newType sourceTerm) := by
  refine
    ⟨Term.isStronglyNormalizing_weaken (newType := newType)
      sourceReducible.1, ?_⟩
  intro _motiveType _baseRaw _baseCase baseIsSN
  exact RawTerm.oeqJ_isStronglyNormalizing baseIsSN
    (Term.isStronglyNormalizing_weaken (newType := newType)
      sourceReducible.1)

/-- **K12.20.U3.monotone weak-J arm**: strict identity
reducibility weakens by rebuilding the strict recursor's SN-output
closure from raw `idStrictRec` SN preservation. -/
theorem Reducible.weaken_idStrict
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType carrierType : Ty level scope}
    {leftEndpoint rightEndpoint sourceRaw : RawTerm scope}
    {sourceTerm :
      Term context (Ty.idStrict carrierType leftEndpoint rightEndpoint) sourceRaw}
    (sourceReducible :
      Reducible (Ty.idStrict carrierType leftEndpoint rightEndpoint) sourceTerm) :
    Reducible ((Ty.idStrict carrierType leftEndpoint rightEndpoint).weaken)
      (Term.weaken newType sourceTerm) := by
  refine
    ⟨Term.isStronglyNormalizing_weaken (newType := newType)
      sourceReducible.1, ?_⟩
  intro _modeIsStrict _motiveType _baseRaw _baseCase baseIsSN
  exact RawTerm.idStrictRec_isStronglyNormalizing baseIsSN
    (Term.isStronglyNormalizing_weaken (newType := newType)
      sourceReducible.1)


end LeanFX2
