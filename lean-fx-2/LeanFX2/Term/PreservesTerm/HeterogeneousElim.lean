import LeanFX2.Term.PreservesTerm.BetaCastWallDemolition
import LeanFX2.Term.PreservesTerm.InlineDestructors
import LeanFX2.Term.PreservesTerm.TwoTyAtomsAndCong
import LeanFX2.Reduction.RawParInversion.AtomicCtors
import LeanFX2.Reduction.RawParInversion.CubicalAndIdentity
import LeanFX2.Reduction.RawParInversion.RedexParents
import LeanFX2.Foundation.IsClosedTyAtBinder
import LeanFX2.Foundation.TermPathLamExcludes

/-! # LeanFX2.Term.PreservesTerm.HeterogeneousElim

Full lifts for ctors whose β/ι rules cross type boundaries:
Σ-type fst/snd via two-Ty existential, identity-type elimination
(idJ / oeqJ / idStrictRec) where the witness type itself reduces,
and the type-changing motive for boolElim.

Covers 5 full lifts (fst, snd, idJ, oeqJ, idStrictRec, boolElim)
plus the destructor idStrictReflDestruct.

## Root status

Zero-axiom; carved from `Term/PreservesTerm.lean`. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}


/-! ## Σ-type ctors — fst, snd, pair (heterogeneous via two-Ty existential) -/

/-- **β cast wall demolition — Term.fst full lift.**  The fst target
type is `firstType` (constant); two-Ty form chosen for headline
parity.  Two-arm raw inversion: cong + β-deep (pair). -/
theorem RawStep.par.lift_full_fst
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw)
    (pairLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par pairRaw targetRawIH →
      ∃ pairTarget : Term context (Ty.sigmaTy firstType secondType) targetRawIH,
        Step.par pairTerm pairTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.fst pairRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.fst (secondType := secondType) pairTerm) targetTerm := by
  rcases RawStep.par.fst_inv rawStep with
    ⟨pairTargetRaw, eq, pairStep⟩
    | ⟨firstTargetRaw, secondTargetRaw, eq, pairToPair⟩
  · -- cong arm
    obtain ⟨pairTarget, pairStepTyped⟩ := pairLift pairStep
    cases eq
    refine ⟨firstType, Term.fst (secondType := secondType) pairTarget, ?_⟩
    exact Step.par.fst pairStepTyped
  · -- β-deep arm: pair raw-reduces to RawTerm.pair firstTargetRaw secondTargetRaw
    obtain ⟨pairCanonical, pairStepTyped⟩ := pairLift pairToPair
    obtain ⟨firstValue, secondValue, pairHeq⟩ := Term.pairDestruct pairCanonical
    have pairEq : pairCanonical = Term.pair firstValue secondValue := eq_of_heq pairHeq
    rw [pairEq] at pairStepTyped
    cases eq
    refine ⟨firstType, firstValue, ?_⟩
    exact Step.par.betaFstPairDeep pairStepTyped

/-- **β cast wall demolition — Term.snd full lift.**  The snd target
type is `secondType.subst0 firstType (RawTerm.fst pairRaw)`, then
after the cong arm, becomes `secondType.subst0 firstType (RawTerm.fst
pairTargetRaw)`; the two-Ty existential absorbs this gap.  In the β
arm, the snd target is the second component of the pair, at type
`secondType.subst0 firstType firstRawTarget` — different from
`secondType.subst0 firstType (RawTerm.fst pairRaw)` propositionally
but the existential lets us state the lift uniformly. -/
theorem RawStep.par.lift_full_snd
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw)
    (pairLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par pairRaw targetRawIH →
      ∃ pairTarget : Term context (Ty.sigmaTy firstType secondType) targetRawIH,
        Step.par pairTerm pairTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.snd pairRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.snd (secondType := secondType) pairTerm) targetTerm := by
  rcases RawStep.par.snd_inv rawStep with
    ⟨pairTargetRaw, eq, pairStep⟩
    | ⟨firstTargetRaw, secondTargetRaw, eq, pairToPair⟩
  · -- cong arm
    obtain ⟨pairTarget, pairStepTyped⟩ := pairLift pairStep
    cases eq
    refine ⟨secondType.subst0 firstType (RawTerm.fst pairTargetRaw),
            Term.snd (secondType := secondType) pairTarget, ?_⟩
    exact Step.par.snd pairStepTyped
  · -- β-deep arm: pair raw-reduces to RawTerm.pair firstTargetRaw secondTargetRaw
    obtain ⟨pairCanonical, pairStepTyped⟩ := pairLift pairToPair
    obtain ⟨firstValue, secondValue, pairHeq⟩ := Term.pairDestruct pairCanonical
    have pairEq : pairCanonical = Term.pair firstValue secondValue := eq_of_heq pairHeq
    rw [pairEq] at pairStepTyped
    cases eq
    refine ⟨secondType.subst0 firstType firstTargetRaw, secondValue, ?_⟩
    exact Step.par.betaSndPairDeep pairStepTyped

/-! ## Identity-type elimination — idJ, oeqJ, idStrictRec via two-Ty existential

These eliminators have a constant `motiveType` (at scope, NOT scope+1),
so the cong arm produces a target at `motiveType` directly.  The
iota-refl arm requires the witness to typed-reduce to a `Term.refl
carrier endpoint`, which forces `leftEndpoint = rightEndpoint`
(`Term.refl c w : Ty.id c w w`).  We extract this equality via the
witness IH + reflDestruct, then dispatch through the deep iota rule. -/

/-- **β cast wall demolition — Term.idJ full lift.**  Two-arm raw
inversion: cong + iotaIdJReflDeep.  In the iota arm, the witness IH
produces a Term at `Ty.id carrier leftEndpoint rightEndpoint` with raw
`RawTerm.refl witnessRaw'`.  By Term.refl's typing, this forces
`leftEndpoint = rightEndpoint = witnessRaw'`.  We then apply
`Step.par.iotaIdJReflDeep`. -/
theorem RawStep.par.lift_full_idJ
    {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw)
    (baseLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par baseRaw targetRawIH →
      ∃ baseTarget : Term context motiveType targetRawIH,
        Step.par baseCase baseTarget)
    (witnessLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par witnessRaw targetRawIH →
      ∃ witnessTarget :
          Term context (Ty.id carrier leftEndpoint rightEndpoint) targetRawIH,
        Step.par witness witnessTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.idJ baseRaw witnessRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.idJ baseCase witness) targetTerm := by
  rcases RawStep.par.idJ_inv rawStep with
    ⟨baseTargetRaw, witnessTargetRaw, eq, baseStep, witnessStep⟩
    | ⟨witnessRaw', baseTargetRaw, eq, witnessToRefl, baseStep⟩
  · -- cong arm
    obtain ⟨baseTarget, baseStepTyped⟩ := baseLift baseStep
    obtain ⟨witnessTarget, witnessStepTyped⟩ := witnessLift witnessStep
    cases eq
    refine ⟨motiveType, Term.idJ baseTarget witnessTarget, ?_⟩
    exact Step.par.idJ baseStepTyped witnessStepTyped
  · -- iota arm: witness raw-reduces to RawTerm.refl witnessRaw'
    obtain ⟨witnessCanonical, witnessStepTyped⟩ := witnessLift witnessToRefl
    obtain ⟨baseTarget, baseStepTyped⟩ := baseLift baseStep
    cases eq
    refine ⟨motiveType, baseTarget, ?_⟩
    -- The typed IH gives witnessCanonical : Term ctx (Ty.id carrier left right)
    --                                              (RawTerm.refl witnessRaw').
    -- Term.refl_ty_inv says the type-shape forces witnessRaw' = left = right.
    -- We extract this via a destructor that returns a fresh Term.refl-shape
    -- target along with HEq alignment.
    --
    -- The cleanest approach: use a destructor that yields directly a
    -- Step.par witness (Term.refl carrier endpoint) for some endpoint
    -- = leftEndpoint = rightEndpoint.
    --
    -- We use a pre-extraction lemma `Term.idReflDestruct` that takes
    -- a Term at Ty.id with refl-raw and returns a triple (leftEqWitness,
    -- rightEqWitness, witnessAsTermRefl_via_HEq).
    obtain ⟨witnessRawEqLeft, witnessRawEqRight, witnessHeq⟩ :=
      Term.idReflDestruct witnessCanonical
    cases witnessRawEqLeft
    cases witnessRawEqRight
    -- Now witnessRaw' = leftEndpoint = rightEndpoint, and witnessHeq is
    -- HEq witnessCanonical (Term.refl carrier leftEndpoint).
    have witnessEq : witnessCanonical = Term.refl carrier leftEndpoint :=
      eq_of_heq witnessHeq
    rw [witnessEq] at witnessStepTyped
    exact Step.par.iotaIdJReflDeep witnessStepTyped baseStepTyped

/-- **β cast wall demolition — Term.oeqJ full lift.**  Only one
inversion arm (cong); no iota at the raw level for oeqJ. -/
theorem RawStep.par.lift_full_oeqJ
    {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness :
      Term context (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw)
    (baseLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par baseRaw targetRawIH →
      ∃ baseTarget : Term context motiveType targetRawIH,
        Step.par baseCase baseTarget)
    (witnessLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par witnessRaw targetRawIH →
      ∃ witnessTarget :
          Term context (Ty.oeq carrier leftEndpoint rightEndpoint) targetRawIH,
        Step.par witness witnessTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.oeqJ baseRaw witnessRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.oeqJ baseCase witness) targetTerm := by
  obtain ⟨baseTargetRaw, witnessTargetRaw, eq, baseStep, witnessStep⟩ :=
    RawStep.par.oeqJ_inv rawStep
  obtain ⟨baseTarget, baseStepTyped⟩ := baseLift baseStep
  obtain ⟨witnessTarget, witnessStepTyped⟩ := witnessLift witnessStep
  cases eq
  refine ⟨motiveType, Term.oeqJ baseTarget witnessTarget, ?_⟩
  exact Step.par.oeqJCong baseStepTyped witnessStepTyped

/-- Destructor for `Term.idStrictRefl` at type `Ty.idStrict carrier
leftEndpoint rightEndpoint` with raw `RawTerm.idStrictRefl witnessRaw`. -/
def Term.idStrictReflDestruct
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {witnessRaw : RawTerm scope}
    (someTerm :
      Term context (Ty.idStrict carrier leftEndpoint rightEndpoint)
                   (RawTerm.idStrictRefl witnessRaw)) :
    Σ' (_witnessEqLeft : witnessRaw = leftEndpoint)
       (_witnessEqRight : witnessRaw = rightEndpoint),
       HEq someTerm
            (Term.idStrictRefl (context := context) modeIsStrict carrier
                               witnessRaw) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.idStrictRefl witnessRaw)),
        someType = Ty.idStrict carrier leftEndpoint rightEndpoint →
        Σ' (witnessEqLeft : witnessRaw = leftEndpoint)
           (witnessEqRight : witnessRaw = rightEndpoint),
           HEq genericTerm
                (Term.idStrictRefl (context := context) modeIsStrict carrier
                                   witnessRaw) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsIdStrict
  cases genericTerm
  rename_i innerMode innerCarrier
  have idStrictEq := Ty.idStrict.inj someTypeIsIdStrict
  cases idStrictEq.1
  exact ⟨idStrictEq.2.1, idStrictEq.2.2, HEq.rfl⟩

/-- **β cast wall demolition — Term.idStrictRec full lift.**  Two-arm
raw inversion: cong + iotaIdStrictRecRefl.  In iota arm, the witness IH
gives a Term at Ty.idStrict carrier left right with idStrictRefl-raw,
which by typing forces left = right = witnessRaw'. -/
theorem RawStep.par.lift_full_idStrictRec
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness :
      Term context (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw)
    (baseLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par baseRaw targetRawIH →
      ∃ baseTarget : Term context motiveType targetRawIH,
        Step.par baseCase baseTarget)
    (witnessLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par witnessRaw targetRawIH →
      ∃ witnessTarget :
          Term context (Ty.idStrict carrier leftEndpoint rightEndpoint) targetRawIH,
        Step.par witness witnessTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.idStrictRec baseRaw witnessRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.idStrictRec modeIsStrict baseCase witness) targetTerm := by
  rcases RawStep.par.idStrictRec_inv rawStep with
    ⟨baseTargetRaw, witnessTargetRaw, eq, baseStep, witnessStep⟩
    | ⟨witnessRaw', baseTargetRaw, eq, witnessToRefl, baseStep⟩
  · -- cong arm
    obtain ⟨baseTarget, baseStepTyped⟩ := baseLift baseStep
    obtain ⟨witnessTarget, witnessStepTyped⟩ := witnessLift witnessStep
    cases eq
    refine ⟨motiveType, Term.idStrictRec modeIsStrict baseTarget witnessTarget, ?_⟩
    exact Step.par.idStrictRecCong modeIsStrict baseStepTyped witnessStepTyped
  · -- iota arm: witness raw-reduces to RawTerm.idStrictRefl witnessRaw'
    obtain ⟨witnessCanonical, witnessStepTyped⟩ := witnessLift witnessToRefl
    obtain ⟨baseTarget, baseStepTyped⟩ := baseLift baseStep
    cases eq
    obtain ⟨witnessRawEqLeft, witnessRawEqRight, witnessHeq⟩ :=
      Term.idStrictReflDestruct modeIsStrict witnessCanonical
    cases witnessRawEqLeft
    cases witnessRawEqRight
    have witnessEq : witnessCanonical =
        Term.idStrictRefl modeIsStrict carrier leftEndpoint :=
      eq_of_heq witnessHeq
    rw [witnessEq] at witnessStepTyped
    refine ⟨motiveType, baseTarget, ?_⟩
    exact Step.par.iotaIdStrictRecReflDeep modeIsStrict
            witnessStepTyped baseStepTyped

/-! ## Type-changing motive — boolElim via two-Ty existential

`Term.boolElim`'s motive lives at scope+1 (`motiveType : Ty level (scope
+ 1)`) and the boolElim's result type is `motiveType.subst0 Ty.bool
scrutineeRaw`.  After scrutinee steps to scrutineeTargetRaw, the result
type changes to `motiveType.subst0 Ty.bool scrutineeTargetRaw`.  The
two-Ty existential absorbs this gap. -/

/-- **Type-changing motive wall demolition — Term.boolElim full lift.**
Three-arm raw inversion: cong + iotaBoolElimTrueDeep + iotaBoolElimFalseDeep. -/
theorem RawStep.par.lift_full_boolElim
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutineeRaw)
    (thenBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context Ty.bool targetRawIH,
        Step.par scrutinee scrutTarget)
    (thenLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par thenRaw targetRawIH →
      ∃ thenTarget :
          Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) targetRawIH,
        Step.par thenBranch thenTarget)
    (elseLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par elseRaw targetRawIH →
      ∃ elseTarget :
          Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) targetRawIH,
        Step.par elseBranch elseTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.boolElim scrutineeRaw thenRaw elseRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par
        (Term.boolElim (motiveType := motiveType) scrutinee thenBranch elseBranch)
        targetTerm := by
  rcases RawStep.par.boolElim_inv rawStep with
    ⟨scrutTargetRaw, thenTargetRaw, elseTargetRaw, eq, scrutStep, thenStep, elseStep⟩
    | ⟨thenTargetRaw, eq, scrutToTrue, thenStep⟩
    | ⟨elseTargetRaw, eq, scrutToFalse, elseStep⟩
  · -- cong arm
    obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutStep
    obtain ⟨thenTarget, thenStepTyped⟩ := thenLift thenStep
    obtain ⟨elseTarget, elseStepTyped⟩ := elseLift elseStep
    cases eq
    refine ⟨motiveType.subst0 Ty.bool scrutTargetRaw,
            Term.boolElim scrutTarget thenTarget elseTarget, ?_⟩
    exact Step.par.boolElim scrutStepTyped thenStepTyped elseStepTyped
  · -- iotaBoolElimTrueDeep arm: scrutinee →* boolTrue
    obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToTrue
    obtain ⟨thenTarget, thenStepTyped⟩ := thenLift thenStep
    -- scrutTarget : Term ctx Ty.bool RawTerm.boolTrue → must be Term.boolTrue
    have heq :
        HEq scrutTarget (Term.boolTrue (context := context)) :=
      Term.boolTrue_unique scrutTarget Term.boolTrue
    have scrutEq : scrutTarget = (Term.boolTrue (context := context)) :=
      eq_of_heq heq
    rw [scrutEq] at scrutStepTyped
    cases eq
    refine ⟨motiveType.subst0 Ty.bool RawTerm.boolTrue, thenTarget, ?_⟩
    exact Step.par.iotaBoolElimTrueDeep elseBranch scrutStepTyped thenStepTyped
  · -- iotaBoolElimFalseDeep arm: scrutinee →* boolFalse
    obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToFalse
    obtain ⟨elseTarget, elseStepTyped⟩ := elseLift elseStep
    have heq :
        HEq scrutTarget (Term.boolFalse (context := context)) :=
      Term.boolFalse_unique scrutTarget Term.boolFalse
    have scrutEq : scrutTarget = (Term.boolFalse (context := context)) :=
      eq_of_heq heq
    rw [scrutEq] at scrutStepTyped
    cases eq
    refine ⟨motiveType.subst0 Ty.bool RawTerm.boolFalse, elseTarget, ?_⟩
    exact Step.par.iotaBoolElimFalseDeep thenBranch scrutStepTyped elseStepTyped

/-! ## Σ-introduction: Term.pair full lift via `IsClosedTyAtBinder`

The pair cong arm has secondValueTarget at
`secondType.subst0 firstType firstRawTarget`, but the secondLift IH
yields a term at `secondType.subst0 firstType firstRawSource`.  When
`secondType` is in the image of `Ty.weaken`, both substitutions equal
`inner` (Foundation/IsClosedTyAtBinder.lean's `subst0_invariant`), so
a direct `▸`-cast bridges the gap zero-axiom.  Step.par's parallel
form of pair (RawStep.par.pair) admits both first and second
components reducing simultaneously, unlike single-step Step which has
only `pairRight` — the parallel layer is precisely where this
transport problem appears. -/

/-- Transport-preservation for `Step.par`: when target type is
rewritten along a Ty-level equality, the parallel-step relation is
unchanged.  Provable by `cases` on the type equality (no propext —
Eq elimination on indexed-Ty is structural). -/
private theorem Step.par.cast_target_eq
    {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context sourceType sourceRaw}
    {target : Term context sourceType targetRaw}
    (typesEq : sourceType = targetType)
    (step : Step.par source target) :
    Step.par source (typesEq ▸ target) := by
  cases typesEq
  exact step

/-- **β cast wall demolition — Term.pair full lift.**  Σ-introduction
cong has source's secondValue at the source's subst, target's at the
target's subst — differing in `firstRaw`.  Under
`IsClosedTyAtBinder secondType`, the two substs are propositionally
equal (Foundation/IsClosedTyAtBinder.lean's `subst0_invariant`); we
transport the IH-produced secondTarget via `▸` and `cast_target_eq`
recovers the Step.par relation. -/
theorem RawStep.par.lift_full_pair
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    (secondTypeClosed : IsClosedTyAtBinder secondType)
    {firstRawSource secondRawSource : RawTerm scope}
    (firstValueSource : Term context firstType firstRawSource)
    (secondValueSource :
      Term context (secondType.subst0 firstType firstRawSource)
                    secondRawSource)
    (firstLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par firstRawSource targetRawIH →
      ∃ firstValueTarget : Term context firstType targetRawIH,
        Step.par firstValueSource firstValueTarget)
    (secondLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par secondRawSource targetRawIH →
      ∃ secondValueTarget :
          Term context (secondType.subst0 firstType firstRawSource)
                        targetRawIH,
        Step.par secondValueSource secondValueTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.pair firstRawSource secondRawSource) targetRaw) :
    ∃ (targetType : Ty level scope)
      (targetTerm : Term context targetType targetRaw),
      Step.par (Term.pair (secondType := secondType)
                          firstValueSource secondValueSource)
               targetTerm := by
  obtain ⟨firstTargetRaw, secondTargetRaw, eq, firstStep, secondStep⟩ :=
    RawStep.par.pair_inv rawStep
  cases eq
  obtain ⟨firstValueTarget, firstStepTyped⟩ := firstLift firstStep
  obtain ⟨secondValueTargetAtSource, secondStepTyped⟩ := secondLift secondStep
  have typesEq :
      secondType.subst0 firstType firstRawSource =
      secondType.subst0 firstType firstTargetRaw :=
    secondTypeClosed.subst0_invariant firstType firstRawSource firstTargetRaw
  let secondValueTarget :
      Term context (secondType.subst0 firstType firstTargetRaw) secondTargetRaw :=
    typesEq ▸ secondValueTargetAtSource
  refine ⟨Ty.sigmaTy firstType secondType,
          Term.pair (secondType := secondType) firstValueTarget secondValueTarget,
          ?_⟩
  exact Step.par.pair firstStepTyped
          (Step.par.cast_target_eq typesEq secondStepTyped)

/-- **Closed-carrier hcomp full lift via vacuity.**

The raw `hcomp_inv` produces three disjuncts: cong + `hcompBeta`
(shallow β when sides develops the constant-path shape from the
start) + `hcompBetaDeep` (when sides reduces to the constant-path
shape via parallel step).  Both β arms force the typed sides
value to be a `Term.pathLam`, which is uninhabited at a closed
carrier type via `Term.pathLam_excludes_closedTy`
(Foundation/TermPathLamExcludes.lean, commit 92fa8c42) — closed
types have no `Ty.path` ctor, but the only Term ctor projecting
to `RawTerm.pathLam` returns at `Ty.path`.

The cong arm routes to the existing two-Ty cong wrapper
`RawStep.par.lift_full_hcomp_cong` (TwoTyAtomsAndCong.lean:452).

Together: closed-carrier `Term.hcomp` admits a typed parallel
reduction lift WITHOUT any new typed β kernel ctor — the β rules
that exist at the raw layer are vacuous against the typed
intrinsic representation under the closed-carrier precondition.

This closes the closed-carrier half of unblock-A.leaf.hcomp
(#2016).  Path-typed carriers remain (#2067) and route through
`Term.hcompPath` once the hcompPath β kernel rules ship
(#2068/#2069). -/
theorem RawStep.par.lift_full_hcomp
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    (carrierClosed : IsClosedTy carrierType)
    {sidesRaw capRaw : RawTerm scope}
    (sidesValue : Term context carrierType sidesRaw)
    (capValue : Term context carrierType capRaw)
    (sidesLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par sidesRaw targetRawIH →
      ∃ sidesTarget : Term context carrierType targetRawIH,
        Step.par sidesValue sidesTarget)
    (capLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par capRaw targetRawIH →
      ∃ capTarget : Term context carrierType targetRawIH,
        Step.par capValue capTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.hcomp sidesRaw capRaw) targetRaw) :
    ∃ (targetType : Ty level scope)
      (targetTerm : Term context targetType targetRaw),
      Step.par (Term.hcomp modeIsUnivalent sidesValue capValue) targetTerm := by
  rcases RawStep.par.hcomp_inv rawStep with
    ⟨sidesTargetRaw, capTargetRaw, targetEq, sidesStep, capStep⟩
    | ⟨pathBodyRawSource, capTargetRaw, sidesEq, _targetEq, _capStep⟩
    | ⟨pathBodyRawTarget, capTargetRaw, targetEq, sidesStep, _capStep⟩
  · subst targetEq
    exact RawStep.par.lift_full_hcomp_cong modeIsUnivalent sidesValue capValue
            sidesLift capLift sidesStep capStep
  · subst sidesEq
    exact (Term.pathLam_excludes_closedTy sidesValue carrierClosed).elim
  · subst targetEq
    obtain ⟨pathLamTypedTarget, _⟩ := sidesLift sidesStep
    exact (Term.pathLam_excludes_closedTy pathLamTypedTarget carrierClosed).elim

end LeanFX2
