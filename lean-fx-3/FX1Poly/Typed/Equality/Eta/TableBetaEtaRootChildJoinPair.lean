import FX1Poly.Typed.Equality.Eta.TableBetaEtaRootChildJoinPathLam

/-! # FX1Poly/Typed/TableBetaEtaRootChildJoinPair
    — the per-child copy-replacement join for the pair (Sigma-intro) eta row.

The generic `childJoin` obligation of `crossQuadrantJoinOfChildJoin`
specialized to `etaPairRow`: an iota child congruence diverging from the
pair-eta intro cell joins with the eta contraction.  Pair is the
MULTI-OBSERVATION case — the surjective-pairing row watches TWO copies of
the shared core (slot 0 through `gen_fst`, slot 1 through `gen_snd`, both
under NO binder, so the cores sit directly under the projectors with no
weakening).

The pair-eta source is
`pair (fst core) (snd core)` (two observed copies, NO domain
annotation).  A table step into one projected child has two possible
exits:

* **root projection iota** — the stepped projector is forced to be a
  projection of a `gen_pair` cell (`fstPairRowFiringDecompose` /
  `sndPairRowFiringDecompose`), so `core` itself is a `pair firstValue
  secondValue` and the projection extracts one component.  The LEFT cell
  now disagrees across observations, so it does NOT directly
  eta-contract; the OTHER projector iota-steps the same explicit pair,
  re-aligning both copies to `core` itself, which then eta-contracts.
  Both branches collapse to `core`, joining in the projection step on the
  other slot.
* **congruence in the projected core** — the projector's single child
  `core` steps to `core'`.  The LEFT cell again disagrees; the OTHER
  projector replays the SAME core-step, re-aligning both copies to
  `core'`, which eta-contracts.  Meanwhile the RIGHT reduct `core`
  iota-steps to `core'`.  Both join at `core'`.

The `guardOrigin` typed hypothesis is genuinely UNUSED here (it is kept
only to match the generic `childJoin` shape) — the pair-eta peak is
guard-free.

## Zero-axiom verification

A structural inversion of `StepOverTableChildren` plus the two firing
decompositions; no `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTableBetaEtaRootConfluence.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- The `etaPairRow` membership pin in the eta-rule table (second row). -/
theorem etaPairRow_memTable : etaPairRow ∈ etaRuleTable :=
  .tail _ (.head _)

/-- **The fst-head dispatch brick**: a table row eliminating `gen_fst`
IS the pair-first-projection row (the only `gen_fst`-eliminating row in
`iotaRuleTable`). -/
theorem iotaRowAtFstIsFstPair {rule : IotaRuleDesc}
    (isRow : rule ∈ iotaRuleTable)
    (isFstHead : rule.elimGenerator = .gen_fst) : rule = fstPairIotaRow := by
  cases isRow with
  | head => exact Generator.noConfusion isFstHead
  | tail _ isRow => cases isRow with
    | head => exact Generator.noConfusion isFstHead
    | tail _ isRow => cases isRow with
      | head => exact Generator.noConfusion isFstHead
      | tail _ isRow => cases isRow with
        | head => rfl
        | tail _ isRow => cases isRow with
          | head => exact Generator.noConfusion isFstHead
          | tail _ isRow => cases isRow with
            | head => exact Generator.noConfusion isFstHead
            | tail _ isRow => cases isRow with
              | head => exact Generator.noConfusion isFstHead
              | tail _ isRow => cases isRow with
                | head => exact Generator.noConfusion isFstHead
                | tail _ isRow => cases isRow with
                  | head => exact Generator.noConfusion isFstHead
                  | tail _ isRow => cases isRow with
                    | head => exact Generator.noConfusion isFstHead
                    | tail _ isRow => cases isRow with
                      | head => exact Generator.noConfusion isFstHead
                      | tail _ isRow => cases isRow with
                        | head => exact Generator.noConfusion isFstHead
                        | tail _ isRow => cases isRow with
                          | head => exact Generator.noConfusion isFstHead
                          | tail _ isRow => cases isRow with
                            | head => exact Generator.noConfusion isFstHead
                            | tail _ isRow => cases isRow with
                              | head => exact Generator.noConfusion isFstHead
                              | tail _ isRow => cases isRow with
                                | head =>
                                    exact Generator.noConfusion isFstHead
                                | tail _ isRow => cases isRow with
                                  | head =>
                                      exact Generator.noConfusion isFstHead
                                  | tail _ isRow => cases isRow with
                                    | head =>
                                        exact Generator.noConfusion isFstHead
                                    | tail _ isRow => cases isRow with
                                      | head =>
                                          exact
                                            Generator.noConfusion isFstHead
                                      | tail _ isRow => cases isRow with
                                        | head =>
                                            exact
                                              Generator.noConfusion isFstHead
                                        | tail _ isRow => cases isRow with
                                          | head =>
                                              exact
                                                Generator.noConfusion isFstHead
                                          | tail _ isRow => cases isRow

/-- **The snd-head dispatch brick**: a table row eliminating `gen_snd`
IS the pair-second-projection row. -/
theorem iotaRowAtSndIsSndPair {rule : IotaRuleDesc}
    (isRow : rule ∈ iotaRuleTable)
    (isSndHead : rule.elimGenerator = .gen_snd) : rule = sndPairIotaRow := by
  cases isRow with
  | head => exact Generator.noConfusion isSndHead
  | tail _ isRow => cases isRow with
    | head => exact Generator.noConfusion isSndHead
    | tail _ isRow => cases isRow with
      | head => exact Generator.noConfusion isSndHead
      | tail _ isRow => cases isRow with
        | head => exact Generator.noConfusion isSndHead
        | tail _ isRow => cases isRow with
          | head => rfl
          | tail _ isRow => cases isRow with
            | head => exact Generator.noConfusion isSndHead
            | tail _ isRow => cases isRow with
              | head => exact Generator.noConfusion isSndHead
              | tail _ isRow => cases isRow with
                | head => exact Generator.noConfusion isSndHead
                | tail _ isRow => cases isRow with
                  | head => exact Generator.noConfusion isSndHead
                  | tail _ isRow => cases isRow with
                    | head => exact Generator.noConfusion isSndHead
                    | tail _ isRow => cases isRow with
                      | head => exact Generator.noConfusion isSndHead
                      | tail _ isRow => cases isRow with
                        | head => exact Generator.noConfusion isSndHead
                        | tail _ isRow => cases isRow with
                          | head => exact Generator.noConfusion isSndHead
                          | tail _ isRow => cases isRow with
                            | head => exact Generator.noConfusion isSndHead
                            | tail _ isRow => cases isRow with
                              | head => exact Generator.noConfusion isSndHead
                              | tail _ isRow => cases isRow with
                                | head =>
                                    exact Generator.noConfusion isSndHead
                                | tail _ isRow => cases isRow with
                                  | head =>
                                      exact Generator.noConfusion isSndHead
                                  | tail _ isRow => cases isRow with
                                    | head =>
                                        exact Generator.noConfusion isSndHead
                                    | tail _ isRow => cases isRow with
                                      | head =>
                                          exact
                                            Generator.noConfusion isSndHead
                                      | tail _ isRow => cases isRow with
                                        | head =>
                                            exact
                                              Generator.noConfusion isSndHead
                                        | tail _ isRow => cases isRow with
                                          | head =>
                                              exact
                                                Generator.noConfusion isSndHead
                                          | tail _ isRow => cases isRow

/-- **`fstPairIotaRow` firing decomposition**: a successful `fst`-cell
firing on a literal one-child spine forces the projected scrutinee to be
a `gen_pair` cell and pins the reduct to its FIRST component.  The
projector twin of `pathBetaRowFiringDecompose`. -/
theorem fstPairRowFiringDecompose {scope : Nat}
    {projectedChild reduct : RawTerm scope}
    (fires : fstPairIotaRow.firesOn? ()
        (.childCons projectedChild .childNil)
      = some reduct) :
    ∃ firstValue secondValue : RawTerm scope,
      projectedChild =
          RawTerm.mkGen .gen_pair ()
            (.childCons firstValue (.childCons secondValue .childNil)) ∧
        reduct = firstValue := by
  cases projectedChild with
  | mkGen projectedGenerator projectedPayload projectedChildren =>
      have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
      subst isHead
      cases projectedPayload
      cases projectedChildren with
      | childCons firstValue secondAndRest =>
          cases secondAndRest with
          | childCons secondValue pairNil =>
              cases pairNil
              exact ⟨firstValue, secondValue, rfl, (Option.some.inj fires).symm⟩

/-- **`sndPairIotaRow` firing decomposition**: the `snd`-cell twin of
`fstPairRowFiringDecompose`, pinning the reduct to the SECOND component. -/
theorem sndPairRowFiringDecompose {scope : Nat}
    {projectedChild reduct : RawTerm scope}
    (fires : sndPairIotaRow.firesOn? ()
        (.childCons projectedChild .childNil)
      = some reduct) :
    ∃ firstValue secondValue : RawTerm scope,
      projectedChild =
          RawTerm.mkGen .gen_pair ()
            (.childCons firstValue (.childCons secondValue .childNil)) ∧
        reduct = secondValue := by
  cases projectedChild with
  | mkGen projectedGenerator projectedPayload projectedChildren =>
      have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
      subst isHead
      cases projectedPayload
      cases projectedChildren with
      | childCons firstValue secondAndRest =>
          cases secondAndRest with
          | childCons secondValue pairNil =>
              cases pairNil
              exact ⟨firstValue, secondValue, rfl, (Option.some.inj fires).symm⟩

/-- **Pair-eta source-shape inversion**: a successful `etaPairRow`
contraction forces the two intro children to be the canonical projections
`fst core` and `snd core` of the SAME shared core (binder depth zero, so
no weakening). -/
theorem etaPairRowContraction_introChildrenShape {scope : Nat}
    {introChildren :
      RawTermChildren etaPairRow.introGenerator.binderShifts scope}
    {core : RawTerm scope}
    (contracts : etaPairRow.contractsOn? introChildren = some core) :
    introChildren =
      (RawTermChildren.childCons
        (RawTerm.mkGen .gen_fst ()
          ((.childCons core .childNil :
            RawTermChildren Generator.gen_fst.binderShifts scope)))
        (.childCons
          (RawTerm.mkGen .gen_snd ()
            ((.childCons core .childNil :
              RawTermChildren Generator.gen_snd.binderShifts scope)))
          .childNil) :
        RawTermChildren Generator.gen_pair.binderShifts scope) := by
  obtain ⟨primarySpec, restSpecs, specsShape, primaryExtracts, restAgree⟩ :=
    etaPairRow.contractsOn?_consInversion contracts
  -- The pair row's observations are exactly the two projection specs.
  injection specsShape with primaryEq restEq
  subst primaryEq
  subst restEq
  -- The second observation also extracts `core` (the agreement gate).
  have secondExtracts :
      ({ introChildSlot := 1, observerHead := .gen_snd, coreSlot := 0
       , binderDepth := 0, freshVarSlots := [] } :
          EtaObservationSpec).extractCoreFrom? introChildren = some core :=
    etaObservationsAgree_memberExtracts _ restAgree (.head _)
  -- Invert both observations to pin the two child shapes.
  match introChildren with
  | .childCons firstChild (.childCons secondChild .childNil) =>
    obtain ⟨firstPayload, firstObserved, firstLookup, _firstFresh,
        firstCoreExtract⟩ :=
      EtaObservationSpec.extractCoreFrom?_someInversion _ primaryExtracts
    obtain ⟨secondPayload, secondObserved, secondLookup, _secondFresh,
        secondCoreExtract⟩ :=
      EtaObservationSpec.extractCoreFrom?_someInversion _ secondExtracts
    -- The primary observes slot 0 (fst), the secondary slot 1 (snd).
    have firstShape :
        firstChild = RawTerm.mkGen .gen_fst firstPayload firstObserved :=
      Option.some.inj
        (firstLookup :
          some firstChild
            = some (RawTerm.mkGen .gen_fst firstPayload firstObserved))
    have secondShape :
        secondChild = RawTerm.mkGen .gen_snd secondPayload secondObserved :=
      Option.some.inj
        (secondLookup :
          some secondChild
            = some (RawTerm.mkGen .gen_snd secondPayload secondObserved))
    subst firstShape
    subst secondShape
    cases firstPayload
    cases secondPayload
    -- Each projector's single child is the core (binderDepth 0 = no
    -- strengthening).
    match firstObserved, firstCoreExtract with
    | .childCons firstCore .childNil, firstCoreExtract =>
      match secondObserved, secondCoreExtract with
      | .childCons secondCore .childNil, secondCoreExtract =>
        have firstCoreIsCore : firstCore = core :=
          Option.some.inj
            (firstCoreExtract :
              some firstCore = some core)
        have secondCoreIsCore : secondCore = core :=
          Option.some.inj
            (secondCoreExtract :
              some secondCore = some core)
        subst firstCoreIsCore
        subst secondCoreIsCore
        rfl

set_option linter.unusedVariables false in
/-- ★ **Per-child copy-replacement join, pair (Sigma-intro) eta row.**
The `childJoin` obligation of `crossQuadrantJoinOfChildJoin` specialized
to `etaPairRow`.  One projected copy steps; inverting it splits into a
root projection iota (joins at `core` after re-aligning the other copy by
the dual projection) and a core congruence (joins at the reflected reduct
`core'` after re-aligning the other copy by the same core-step).  The
typed `guardOrigin` is unused — the pair-eta peak is guard-free. -/
theorem childJoinPair {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {introPayload : etaPairRow.introGenerator.payload scope}
    {introChildren steppedChildren :
      RawTermChildren etaPairRow.introGenerator.binderShifts scope}
    {etaReduct : RawTerm scope}
    (guardOrigin : ∃ stepClassifier : RawTerm scope,
      HasTypeDescPi profile context
        (.mkGen etaPairRow.introGenerator introPayload introChildren) stepClassifier)
    (childStep : StepOverTableChildren iotaRuleTable introChildren steppedChildren)
    (contracts : etaPairRow.contractsOn? introChildren = some etaReduct) :
    Joinable StepTableBetaEtaRoot
      (.mkGen etaPairRow.introGenerator introPayload steppedChildren) etaReduct := by
  clear guardOrigin
  -- Force the intro spine to the two canonical projections of `etaReduct`.
  have introShape := etaPairRowContraction_introChildrenShape contracts
  subst introShape
  -- The pair-eta payload is `Unit`.
  cases introPayload
  -- One of the two projected copies steps.
  cases childStep with
  | here _rest fstStep =>
      -- `fstStep : StepOverTable … (fst etaReduct) fst'`.
      cases fstStep.invertOrCong rfl with
      | inl rootFires =>
          -- A root firing at the `gen_fst` cell: only `fstPairIotaRow` fires.
          obtain ⟨iotaRule, iotaIsRow, elimPayload, spine, cellEq, fires⟩ :=
            rootFires
          have headIsFst : iotaRule.elimGenerator = .gen_fst :=
            congrArg
              (fun cell => match cell with
                | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
              cellEq
          have rowIsFstPair : iotaRule = fstPairIotaRow :=
            iotaRowAtFstIsFstPair iotaIsRow headIsFst
          subst rowIsFstPair
          -- Now the cell identity is homogeneous: pin the firing spine.
          injection cellEq with _scopeRefl _genRefl _payloadEq spineEq
          subst spineEq
          cases elimPayload
          obtain ⟨firstValue, secondValue, coreIsPair, reductEq⟩ :=
            fstPairRowFiringDecompose fires
          subst coreIsPair
          rw [reductEq]
          -- LEFT now holds `firstValue` in slot 0 and `snd (pair …)` in slot 1.
          -- RIGHT (`etaReduct = pair firstValue secondValue`) is already a pair.
          refine ⟨RawTerm.mkGen .gen_pair ()
              (.childCons firstValue (.childCons secondValue .childNil)),
            ?_, ReflTransClosure.refl _⟩
          -- LEFT iota-steps slot 1 `snd (pair …) ↝ secondValue`.
          exact ReflTransClosure.single
            (Or.inl
              (StepOverTable.cong .gen_pair ()
                (StepOverTableChildren.there _
                  (StepOverTableChildren.here _
                    (StepOverTable.tableRedex sndPairIotaRow_memTable () rfl)))))
      | inr fstCong =>
          -- A congruence strictly inside the `fst` cell.
          obtain ⟨fstChildren', fst'Eq, fstChildStep⟩ := fstCong
          subst fst'Eq
          cases fstChildStep with
          | here _rest coreStep =>
              -- The projected core `etaReduct` steps to `coreReduct`.
              -- RIGHT iota-steps `etaReduct ↝ coreReduct`.
              -- LEFT re-aligns slot 1 by the SAME core-step, then eta-contracts.
              refine ⟨_, ?_, ReflTransClosure.single (Or.inl coreStep)⟩
              refine ReflTransClosure.head
                (Or.inl
                  (StepOverTable.cong .gen_pair ()
                    (StepOverTableChildren.there _
                      (StepOverTableChildren.here _
                        (StepOverTable.cong .gen_snd ()
                          (StepOverTableChildren.here _ coreStep))))))
                ?_
              exact ReflTransClosure.single
                (Or.inr
                  (StepEtaRootOverTable.etaRedex etaPairRow_memTable rfl ()
                    (etaPairRow_contractsOnSource _)))
          | there _head emptyStep => cases emptyStep
  | there _head sndOuterStep =>
      -- The second projected copy is the one that steps.
      cases sndOuterStep with
      | here _rest sndStep =>
          cases sndStep.invertOrCong rfl with
          | inl rootFires =>
              obtain ⟨iotaRule, iotaIsRow, elimPayload, spine, cellEq, fires⟩ :=
                rootFires
              have headIsSnd : iotaRule.elimGenerator = .gen_snd :=
                congrArg
                  (fun cell => match cell with
                    | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
                  cellEq
              have rowIsSndPair : iotaRule = sndPairIotaRow :=
                iotaRowAtSndIsSndPair iotaIsRow headIsSnd
              subst rowIsSndPair
              injection cellEq with _scopeRefl _genRefl _payloadEq spineEq
              subst spineEq
              cases elimPayload
              obtain ⟨firstValue, secondValue, coreIsPair, reductEq⟩ :=
                sndPairRowFiringDecompose fires
              subst coreIsPair
              rw [reductEq]
              -- LEFT now holds `fst (pair …)` in slot 0 and `secondValue` in slot 1.
              refine ⟨RawTerm.mkGen .gen_pair ()
                  (.childCons firstValue (.childCons secondValue .childNil)),
                ?_, ReflTransClosure.refl _⟩
              -- LEFT iota-steps slot 0 `fst (pair …) ↝ firstValue`.
              exact ReflTransClosure.single
                (Or.inl
                  (StepOverTable.cong .gen_pair ()
                    (StepOverTableChildren.here _
                      (StepOverTable.tableRedex fstPairIotaRow_memTable () rfl))))
          | inr sndCong =>
              obtain ⟨sndChildren', snd'Eq, sndChildStep⟩ := sndCong
              subst snd'Eq
              cases sndChildStep with
              | here _rest coreStep =>
                  refine ⟨_, ?_, ReflTransClosure.single (Or.inl coreStep)⟩
                  refine ReflTransClosure.head
                    (Or.inl
                      (StepOverTable.cong .gen_pair ()
                        (StepOverTableChildren.here _
                          (StepOverTable.cong .gen_fst ()
                            (StepOverTableChildren.here _ coreStep)))))
                    ?_
                  exact ReflTransClosure.single
                    (Or.inr
                      (StepEtaRootOverTable.etaRedex etaPairRow_memTable rfl ()
                        (etaPairRow_contractsOnSource _)))
              | there _head emptyStep => cases emptyStep
      | there _head emptyStep =>
          -- The pair spine's tail after slot 1 is `childNil`.
          cases emptyStep

end FX1Poly.Typed
