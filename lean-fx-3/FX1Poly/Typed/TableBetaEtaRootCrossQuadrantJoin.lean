import FX1Poly.Typed.TableBetaEtaRootGuardedConfluence
import FX1Poly.Core.StepOverTable
import FX1Poly.Core.StepEtaRootTable
import FX1Poly.Core.EtaTableOrthogonality

/-! # FX1Poly/Typed/TableBetaEtaRootCrossQuadrantJoin
    — discharge the two EASY quadrants of the table beta-eta-root guarded local join natively,
      isolating ONLY the genuinely-typed cross-quadrant residual.

`TableBetaEtaRootGuardedConfluence` assembles the table beta-eta Church-Rosser through
`newmanGuarded`, taking the full four-quadrant guarded local join (`guardedLocalJoin`) as one
explicit hypothesis.  That hypothesis case-splits the two diverging `StepTableBetaEtaRoot` steps
into four quadrants:

  * **Q1** (StepTable, StepTable) — iota/iota.  Discharged here by `StepTable.confluent` (the
    canonical 21-row relation is confluent): each single step lifts to a one-step
    `ReflTransClosure`, confluence joins them, and `joinableStepTableToUnion` re-injects the
    iota join into the union relation.
  * **Q2** (StepEtaRootTable, StepEtaRootTable) — eta/eta.  Discharged here by
    `StepEtaRootOverTable.deterministic` under `etaRuleTable_isWf.introRootsAreDistinct`: two
    root contractions of the same cell produce the SAME reduct, so the two steps are equal and
    join in zero steps.
  * **Q3 / Q4** (cross) — iota/eta.  The genuinely-new join: the eta fires at the root and the
    iota strictly inside a child (the root is never both an intro head and an eliminator head),
    and only the etaLam-over-beta annotation clash needs the typed annotation guard (the
    Nederpelt non-joinability).  Taken here as the SOLE remaining hypothesis
    `crossQuadrantJoin`.

`tableGuardedLocalJoinOfCrossQuadrant` reduces the four-quadrant `guardedLocalJoin` to the
cross-quadrant-only `crossQuadrantJoin`; `tableBetaEtaRootConfluenceTypedFromCrossQuadrant`
threads that through the guarded-Newman headline, so the native table beta-eta CR now rests on
exactly the cross-quadrant join — the last bespoke-`Step.eta`-free brick before the headline
re-point.

## Zero-axiom verification

A composition of `StepTable.confluent`, `StepEtaRootOverTable.deterministic`, the shipped
guarded-Newman headline, and two structural closure lifts; no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTableBetaEtaRootConfluence.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- A reflexive-transitive iota chain lifts into the table beta-eta-root union closure: every
`StepTable` step is the left injection of `StepTableBetaEtaRoot`. -/
theorem reflTransClosureStepTableToUnion {scope : Nat} {source target : RawTerm scope}
    (chain : ReflTransClosure (fun left right : RawTerm scope => StepTable left right)
      source target) :
    ReflTransClosure StepTableBetaEtaRoot source target := by
  induction chain with
  | refl point => exact .refl point
  | head firstStep _restChain liftedRest => exact .head (Or.inl firstStep) liftedRest

/-- Iota joinability lifts into table beta-eta-root joinability (both chains lifted along the
left injection). -/
theorem joinableStepTableToUnion {scope : Nat} {leftValue rightValue : RawTerm scope}
    (joined : Joinable (fun left right : RawTerm scope => StepTable left right)
      leftValue rightValue) :
    Joinable StepTableBetaEtaRoot leftValue rightValue := by
  obtain ⟨commonReduct, leftToCommon, rightToCommon⟩ := joined
  exact ⟨commonReduct,
    reflTransClosureStepTableToUnion leftToCommon,
    reflTransClosureStepTableToUnion rightToCommon⟩

/-- **The four-quadrant guarded local join from the cross-quadrant residual**: discharging the
iota/iota quadrant by `StepTable.confluent` and the eta/eta quadrant by
`StepEtaRootOverTable.deterministic`, the only remaining input is the cross (iota/eta) join. -/
theorem HasTypeDescPi.tableGuardedLocalJoinOfCrossQuadrant
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (crossQuadrantJoin :
      ∀ {origin iotaReduct etaReduct : RawTerm scope},
        (∃ stepClassifier : RawTerm scope,
          HasTypeDescPi profile context origin stepClassifier) →
        StepTable origin iotaReduct →
        StepEtaRootTable origin etaReduct →
        Joinable StepTableBetaEtaRoot iotaReduct etaReduct) :
    ∀ {origin leftStep rightStep : RawTerm scope},
      (∃ stepClassifier : RawTerm scope,
        HasTypeDescPi profile context origin stepClassifier) →
      StepTableBetaEtaRoot origin leftStep →
      StepTableBetaEtaRoot origin rightStep →
      Joinable StepTableBetaEtaRoot leftStep rightStep := by
  intro origin leftStep rightStep guardOrigin stepLeft stepRight
  cases stepLeft with
  | inl iotaLeft =>
    cases stepRight with
    | inl iotaRight =>
        exact joinableStepTableToUnion
          (StepTable.confluent
            (ReflTransClosure.single
              (rel := fun left right : RawTerm scope => StepTable left right) iotaLeft)
            (ReflTransClosure.single
              (rel := fun left right : RawTerm scope => StepTable left right) iotaRight))
    | inr etaRight =>
        exact crossQuadrantJoin guardOrigin iotaLeft etaRight
  | inr etaLeft =>
    cases stepRight with
    | inl iotaRight =>
        obtain ⟨commonReduct, iotaToCommon, etaToCommon⟩ :=
          crossQuadrantJoin guardOrigin iotaRight etaLeft
        exact ⟨commonReduct, etaToCommon, iotaToCommon⟩
    | inr etaRight =>
        have stepsAgree : leftStep = rightStep :=
          StepEtaRootOverTable.deterministic
            etaRuleTable_isWf.introRootsAreDistinct etaLeft etaRight
        subst stepsAgree
        exact ⟨_, ReflTransClosure.refl _, ReflTransClosure.refl _⟩

/-- ★ **Guarded-Newman table beta-eta Church-Rosser (cross-quadrant-conditional)**: the same
headline as `tableBetaEtaRootConfluenceTypedFromLocalJoin`, but resting on the cross-quadrant
(iota/eta) join alone — the iota/iota and eta/eta quadrants are discharged natively. -/
theorem HasTypeDescPi.tableBetaEtaRootConfluenceTypedFromCrossQuadrant
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier)
    (crossQuadrantJoin :
      ∀ {origin iotaReduct etaReduct : RawTerm scope},
        (∃ stepClassifier : RawTerm scope,
          HasTypeDescPi profile context origin stepClassifier) →
        StepTable origin iotaReduct →
        StepEtaRootTable origin etaReduct →
        Joinable StepTableBetaEtaRoot iotaReduct etaReduct)
    {leftReduct rightReduct : RawTerm scope}
    (toLeft : UnionStar (StepTable (scope := scope)) StepEtaRootTable subject leftReduct)
    (toRight : UnionStar (StepTable (scope := scope)) StepEtaRootTable subject rightReduct) :
    ∃ commonReduct : RawTerm scope,
      UnionStar (StepTable (scope := scope)) StepEtaRootTable leftReduct commonReduct
      ∧ UnionStar (StepTable (scope := scope)) StepEtaRootTable rightReduct commonReduct :=
  HasTypeDescPi.tableBetaEtaRootConfluenceTypedFromLocalJoin wellFormed typed
    (HasTypeDescPi.tableGuardedLocalJoinOfCrossQuadrant crossQuadrantJoin)
    toLeft toRight

/-! ## Cross-quadrant structural foundation: the iota step is a child congruence

An eta-root source is intro-headed (`rule.introGenerator` is a lambda / pair / path-lambda); a
root iota firing requires an ELIMINATOR head, and `WfEtaTable.introRootsAreNotIotaElims` certifies
those are disjoint.  So the only way a table step leaves an eta-root source is by congruence into a
child — `crossQuadrantJoinOfChildJoin` uses this to reduce the cross-quadrant join to the
per-child-congruence join obligation (the copy-replacement content), the last residual. -/

/-- **An iota step out of an eta-root source is a child congruence.**  The root-firing disjunct of
`StepOverTable.invertOrCong` forces the eta intro generator to equal an iota rule's eliminator
generator, contradicting the cross-table root disjointness in `etaRuleTable_isWf`. -/
theorem crossQuadrantIotaStepIsCong {scope : Nat}
    {etaRule : EtaRuleDesc} (etaIsRow : etaRule ∈ etaRuleTable)
    {introPayload : etaRule.introGenerator.payload scope}
    {introChildren : RawTermChildren etaRule.introGenerator.binderShifts scope}
    {iotaReduct : RawTerm scope}
    (iotaStep : StepTable
      (.mkGen etaRule.introGenerator introPayload introChildren) iotaReduct) :
    ∃ steppedChildren : RawTermChildren etaRule.introGenerator.binderShifts scope,
      iotaReduct = .mkGen etaRule.introGenerator introPayload steppedChildren
      ∧ StepOverTableChildren iotaRuleTable introChildren steppedChildren := by
  cases iotaStep.invertOrCong rfl with
  | inl rootFires =>
      obtain ⟨iotaRule, iotaIsRow, _elimPayload, _spine, cellEq, _fires⟩ := rootFires
      have headsAgree : iotaRule.elimGenerator = etaRule.introGenerator :=
        congrArg
          (fun cell => match cell with
            | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
          cellEq
      exact absurd headsAgree.symm
        (WfEtaTable.introRootsAreNotIotaElims etaRuleTable_isWf etaIsRow iotaIsRow)
  | inr childCongruence => exact childCongruence

/-- **The cross-quadrant join from the per-child-congruence join.**  Inverting the root eta step
exposes the intro-headed origin and its contraction; `crossQuadrantIotaStepIsCong` turns the
diverging iota step into a child congruence; the supplied `childJoin` discharges the residual
copy-replacement join (clean for pair / path-lambda, typed-guard-consuming for the lambda
annotation clash). -/
theorem HasTypeDescPi.crossQuadrantJoinOfChildJoin
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (childJoin :
      ∀ {etaRule : EtaRuleDesc}, etaRule ∈ etaRuleTable →
        etaRule.requiresTypedFiring = false →
        ∀ {introPayload : etaRule.introGenerator.payload scope}
          {introChildren steppedChildren :
            RawTermChildren etaRule.introGenerator.binderShifts scope}
          {etaReduct : RawTerm scope},
          (∃ stepClassifier : RawTerm scope,
            HasTypeDescPi profile context
              (.mkGen etaRule.introGenerator introPayload introChildren) stepClassifier) →
          StepOverTableChildren iotaRuleTable introChildren steppedChildren →
          etaRule.contractsOn? introChildren = some etaReduct →
          Joinable StepTableBetaEtaRoot
            (.mkGen etaRule.introGenerator introPayload steppedChildren) etaReduct) :
    ∀ {origin iotaReduct etaReduct : RawTerm scope},
      (∃ stepClassifier : RawTerm scope,
        HasTypeDescPi profile context origin stepClassifier) →
      StepTable origin iotaReduct →
      StepEtaRootTable origin etaReduct →
      Joinable StepTableBetaEtaRoot iotaReduct etaReduct := by
  intro origin iotaReduct etaReduct guardOrigin iotaStep etaStep
  obtain ⟨etaRule, etaIsRow, isRawTier, introPayload, introChildren, originShape, contracts⟩ :=
    etaStep.invert
  subst originShape
  obtain ⟨steppedChildren, iotaReductShape, childCongruence⟩ :=
    crossQuadrantIotaStepIsCong etaIsRow iotaStep
  subst iotaReductShape
  exact childJoin etaIsRow isRawTier guardOrigin childCongruence contracts

end FX1Poly.Typed
