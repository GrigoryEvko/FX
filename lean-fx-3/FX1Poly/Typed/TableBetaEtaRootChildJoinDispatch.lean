import FX1Poly.Typed.TableBetaEtaRootChildJoinLam

/-! # FX1Poly/Typed/TableBetaEtaRootChildJoinDispatch
    — the eight-row membership dispatcher that assembles the generic `childJoin`
      obligation from the three shipped raw-tier row joins, and the UNCONDITIONAL
      native table beta-eta-root Church-Rosser it unlocks.

`crossQuadrantJoinOfChildJoin` reduces the cross-quadrant (iota/eta) join to a
single generic `childJoin` obligation — universally quantified over every eta
row, gated on `requiresTypedFiring = false` (the raw tier).  Three modules ship
that obligation specialized to each raw-tier row:

  * `childJoinLam` for `etaLamRow` (the Nederpelt annotation clash, the one case
    that consumes the typed `guardOrigin`),
  * `childJoinPair` for `etaPairRow` (the surjective-pairing multi-observation
    case),
  * `childJoinPathLam` for `etaPathLamRow` (the guard-free path-beta case).

`crossQuadrantChildJoinDispatch` walks the eight-element `etaRuleTable`
membership (`List.Mem` over the literal list) and:

  * for each of the three raw rows, the membership pins `etaRule` to that row, so
    the generic payload / children / reduct specialize to the row's shape and the
    matching shipped lemma applies directly (threading `guardOrigin`,
    `childStep`, `contracts`);
  * for each of the five typed-tier rows (`etaModIntroRow`, `etaGlueIntroRow`,
    `unitEtaRow`, `recordEtaRow`, `refineEtaRow`), the `requiresTypedFiring =
    false` premise is contradictory (those rows carry `requiresTypedFiring =
    true`) and is discharged by `Bool.noConfusion`.

This is the EXACT membership-walk pattern of `stepEtaTableRootToBespokeEta`
(`FX1Poly/Core/StepEtaTableBackward.lean`): explicit `.head`/`.tail` chains on
`List.Mem`, no wildcard or partial match, so it is propext-clean.

`tableBetaEtaRootConfluenceTypedNative` then feeds the dispatcher into
`crossQuadrantJoinOfChildJoin` and `tableBetaEtaRootConfluenceTypedFromCrossQuadrant`,
yielding the UNCONDITIONAL native table beta-eta-root Church-Rosser — the same
conclusion shape as `tableBetaEtaRootConfluenceTyped`, with NO bespoke
`Step.eta`/`Step.betaEta` round-trip and NO remaining hypothesis beyond the
context well-formedness and the subject typing.

## Zero-axiom verification

The dispatcher is a structural `List.Mem` membership walk delegating to the three
shipped row joins and `Bool.noConfusion`; the native headline is a single
instantiation of two shipped theorems.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTableBetaEtaRootConfluence.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- ★ **The eight-row childJoin dispatcher.**  The generic per-child
copy-replacement join obligation of `crossQuadrantJoinOfChildJoin`, assembled by
walking the `etaRuleTable` membership: the three raw rows delegate to
`childJoinLam` / `childJoinPair` / `childJoinPathLam`, the five typed-tier rows
contradict the `requiresTypedFiring = false` gate.  Its statement unifies exactly
with the `childJoin` hypothesis `crossQuadrantJoinOfChildJoin` consumes. -/
theorem HasTypeDescPi.crossQuadrantChildJoinDispatch
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} :
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
          (.mkGen etaRule.introGenerator introPayload steppedChildren) etaReduct := by
  intro etaRule isRow isRawTier introPayload introChildren steppedChildren etaReduct
    guardOrigin childStep contracts
  cases isRow with
  | head => exact childJoinLam guardOrigin childStep contracts
  | tail _ isRow => cases isRow with
    | head => exact childJoinPair guardOrigin childStep contracts
    | tail _ isRow => cases isRow with
      | head => exact childJoinPathLam guardOrigin childStep contracts
      | tail _ isRow => cases isRow with
        | head => exact Bool.noConfusion isRawTier
        | tail _ isRow => cases isRow with
          | head => exact Bool.noConfusion isRawTier
          | tail _ isRow => cases isRow with
            | head => exact Bool.noConfusion isRawTier
            | tail _ isRow => cases isRow with
              | head => exact Bool.noConfusion isRawTier
              | tail _ isRow => cases isRow with
                | head => exact Bool.noConfusion isRawTier
                | tail _ isRow => cases isRow

/-- ★★★ **The UNCONDITIONAL native table beta-eta-root Church-Rosser.**  The
dispatcher discharges the cross-quadrant childJoin obligation, so
`crossQuadrantJoinOfChildJoin` supplies the cross-quadrant join unconditionally,
and `tableBetaEtaRootConfluenceTypedFromCrossQuadrant` produces the table beta-eta
Church-Rosser with NO remaining hypothesis: any two `UnionStar StepTable
StepEtaRootTable` reducts of a grown-typed subject in a well-formed context join
by table-union stars — assembled natively via guarded Newman, with no bespoke
`Step.eta`/`Step.betaEta` round-trip. -/
theorem HasTypeDescPi.tableBetaEtaRootConfluenceTypedNative
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier)
    {leftReduct rightReduct : RawTerm scope}
    (toLeft : UnionStar (StepTable (scope := scope)) StepEtaRootTable subject leftReduct)
    (toRight : UnionStar (StepTable (scope := scope)) StepEtaRootTable subject rightReduct) :
    ∃ commonReduct : RawTerm scope,
      UnionStar (StepTable (scope := scope)) StepEtaRootTable leftReduct commonReduct
      ∧ UnionStar (StepTable (scope := scope)) StepEtaRootTable rightReduct commonReduct :=
  HasTypeDescPi.tableBetaEtaRootConfluenceTypedFromCrossQuadrant wellFormed typed
    (HasTypeDescPi.crossQuadrantJoinOfChildJoin
      HasTypeDescPi.crossQuadrantChildJoinDispatch)
    toLeft toRight

end FX1Poly.Typed
