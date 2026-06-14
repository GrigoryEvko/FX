import FX1Poly.Typed.Equality.Eta.TableBetaEtaRootCrossQuadrantJoin
import FX1Poly.Typed.Engine.RuleTables.IotaElimTypedLink
import FX1Poly.Core.Rewriting.RuleTables.Eta.StepEtaTableBackward
import FX1Poly.Core.Equality.Eta.EtaRowFiringSubstrate
import FX1Poly.Core.Rewriting.RuleTables.StepOver.StepTableRenameReflection
import FX1Poly.Core.Rewriting.RuleTables.StepOver.StepTableEquivariance
import FX1Poly.Tier0.Syntax.RawTermSubstLiftWeaken

/-! # FX1Poly/Typed/TableBetaEtaRootChildJoinPathLam
    — the per-child copy-replacement join for the path-lambda eta row.

The generic `childJoin` obligation of `crossQuadrantJoinOfChildJoin`
specialized to `etaPathLamRow`: an iota child congruence diverging from
the path-eta intro cell joins with the eta contraction.  The path-eta
row is the CLEAN case — unlike `etaLamRow`, the path-beta-vs-eta peak
needs NO typing guard, joining by pure equality on the diagonal.

The path-eta source is
`pathLam (pathApp (weaken core) (var 0))` (one child under one binder,
NO domain annotation).  A table step into the single body child has two
possible exits:

* **root path-beta** — the function slot `weaken core` is forced to be a
  path-lambda (`pathBetaRowFiringDecompose`), so `core` itself is a
  path-lambda whose lifted-weakened body the `var 0` substitution exactly
  un-weakens (`subst0_lift_weaken_newestVar`): both reducts collapse to
  `core`, joining in ZERO steps.
* **congruence in the weakened function** — reflected back to a step on
  `core` (`StepOverTable.reflectRename` at `RawRenaming.weaken`,
  `iotaRuleTable_isScopeUniform`): the right reduct `core` iota-steps to
  `core'`, the left reduct re-eta-contracts to `core'`, joining at
  `core'`.

The `guardOrigin` typed hypothesis is genuinely UNUSED here (it is kept
only to match the generic `childJoin` shape).

## Zero-axiom verification

A structural inversion of `StepOverTableChildren` plus the two
substrate decompositions; no `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTableBetaEtaRootConfluence.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core
open FX1Poly.Tier0.Syntax

/-- The `etaPathLamRow` membership pin in the eta-rule table (third row). -/
theorem etaPathLamRow_memTable : etaPathLamRow ∈ etaRuleTable :=
  .tail _ (.tail _ (.head _))

/-- A variable cell has an empty child spine, so no canonical-table step
leaves it: the root-firing disjunct forces a `gen_var`-headed row
(excluded by the scope-uniformity certificate), and the congruence
disjunct steps the empty spine (no constructor). -/
theorem noStepTableFromVarCell {scope : Nat} {bound : Nat}
    (isInBounds : bound < scope) {target : RawTerm scope}
    (varStep : StepTable
      (RawTerm.mkGen .gen_var ⟨bound, isInBounds⟩ .childNil) target) :
    False := by
  cases varStep.invertOrCong rfl with
  | inl rootFires =>
      obtain ⟨iotaRule, iotaIsRow, _elimPayload, _spine, cellEq, _fires⟩ := rootFires
      have headIsVar : iotaRule.elimGenerator = .gen_var :=
        congrArg
          (fun cell => match cell with
            | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
          cellEq
      exact (iotaRuleTable_isScopeUniform iotaRule iotaIsRow).isNotVarHead headIsVar
  | inr childCong =>
      obtain ⟨_children', _targetEq, emptyStep⟩ := childCong
      cases emptyStep

/-- **Path-eta source-shape inversion**: a successful `etaPathLamRow`
contraction forces the single intro child to be the canonical path-eta
body `pathApp (weaken core) (var 0)`.  The shape companion of
`etaPathLamRowContractionToBespokeEta` (same decode, concluding the
spine equation rather than a bespoke `Step.eta`). -/
theorem etaPathLamRowContraction_introChildrenShape {scope : Nat}
    {introChildren :
      RawTermChildren etaPathLamRow.introGenerator.binderShifts scope}
    {core : RawTerm scope}
    (contracts : etaPathLamRow.contractsOn? introChildren = some core) :
    introChildren =
      RawTermChildren.childCons
        (RawTerm.mkGen .gen_pathApp ()
          (.childCons (RawTerm.weaken core)
            (.childCons RawTerm.newestVar .childNil)))
        .childNil := by
  match introChildren, contracts with
  | .childCons bodyChild .childNil, contracts =>
    have peeled :
        (({ introChildSlot := 0, observerHead := .gen_pathApp, coreSlot := 0
          , binderDepth := 1, freshVarSlots := [1] } :
            EtaObservationSpec).extractCoreFrom?
          (RawTermChildren.childCons bodyChild
            RawTermChildren.childNil)).bind some
        = some core := contracts
    match extractEq :
        ({ introChildSlot := 0, observerHead := .gen_pathApp, coreSlot := 0
         , binderDepth := 1, freshVarSlots := [1] } :
           EtaObservationSpec).extractCoreFrom?
          (RawTermChildren.childCons bodyChild RawTermChildren.childNil) with
    | none =>
        rw [extractEq] at peeled
        exact nomatch peeled
    | some extracted =>
        rw [extractEq] at peeled
        have extractedIsCore : core = extracted :=
          (Option.some.inj (peeled : some extracted = some core)).symm
        subst extractedIsCore
        obtain ⟨observedPayload, observedChildren, lookupEq, freshHolds,
          coreExtract⟩ :=
          EtaObservationSpec.extractCoreFrom?_someInversion _ extractEq
        have bodyShape :
            bodyChild
              = RawTerm.mkGen .gen_pathApp observedPayload
                  observedChildren :=
          Option.some.inj
            (lookupEq :
              some bodyChild
                = some (RawTerm.mkGen .gen_pathApp observedPayload
                    observedChildren))
        subst bodyShape
        match observedChildren, freshHolds, coreExtract with
        | .childCons pathChild (.childCons argumentChild .childNil),
            freshHolds, coreExtract =>
          have argTest :
              ((if argumentChild
                    = RawTerm.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩
                        .childNil then true
                else false)
                && true)
              = true := freshHolds
          by_cases argEq :
              argumentChild
                = RawTerm.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩
                    .childNil
          case neg =>
              rw [if_neg argEq] at argTest
              exact nomatch argTest
          case pos =>
              subst argEq
              cases observedPayload
              have strengthened :
                  RawTerm.strengthenBy? 1 pathChild = some core :=
                coreExtract
              have pathShape : RawTerm.weakenBy 1 core = pathChild :=
                RawTerm.weakenBy_strengthenBy? 1 pathChild core strengthened
              rw [← pathShape]
              rfl

set_option linter.unusedVariables false in
/-- ★ **Per-child copy-replacement join, path-lambda eta row.**  The
`childJoin` obligation of `crossQuadrantJoinOfChildJoin` specialized to
`etaPathLamRow`.  The single intro body steps; inverting it splits into
the root path-beta peak (joins by equality at `core`) and the
function-slot congruence (joins at the reflected reduct `core'`).  The
typed `guardOrigin` is unused — the path-eta peak is guard-free. -/
theorem childJoinPathLam {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {introPayload : etaPathLamRow.introGenerator.payload scope}
    {introChildren steppedChildren :
      RawTermChildren etaPathLamRow.introGenerator.binderShifts scope}
    {etaReduct : RawTerm scope}
    (guardOrigin : ∃ stepClassifier : RawTerm scope,
      HasTypeDescPi profile context
        (.mkGen etaPathLamRow.introGenerator introPayload introChildren) stepClassifier)
    (childStep : StepOverTableChildren iotaRuleTable introChildren steppedChildren)
    (contracts : etaPathLamRow.contractsOn? introChildren = some etaReduct) :
    Joinable StepTableBetaEtaRoot
      (.mkGen etaPathLamRow.introGenerator introPayload steppedChildren) etaReduct := by
  clear guardOrigin
  -- Force the intro spine to the canonical path-eta body.
  have introShape := etaPathLamRowContraction_introChildrenShape contracts
  subst introShape
  -- The path-eta payload is `Unit`.
  cases introPayload
  -- The single body steps (`.here`); `.there` would step `childNil` — impossible.
  cases childStep with
  | here _rest bodyStep =>
      -- `bodyStep : StepOverTable iotaRuleTable (pathApp (weaken etaReduct) (var 0)) body'`.
      cases bodyStep.invertOrCong rfl with
      | inl rootFires =>
          -- A root firing at the `gen_pathApp` cell: only `pathBetaIotaRow` fires there.
          obtain ⟨iotaRule, iotaIsRow, elimPayload, spine, cellEq, fires⟩ := rootFires
          -- The fired row eliminates `gen_pathApp`, so it IS the endpoint-β row.
          have headIsPathApp : iotaRule.elimGenerator = .gen_pathApp :=
            congrArg
              (fun cell => match cell with
                | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
              cellEq
          have rowIsPathBeta : iotaRule = pathBetaIotaRow :=
            iotaRowAtPathAppIsPathBeta iotaIsRow headIsPathApp
          subst rowIsPathBeta
          -- Now the cell identity is homogeneous: pin the firing spine.
          injection cellEq with _scopeRefl _genRefl _payloadEq spineEq
          subst spineEq
          cases elimPayload
          -- Decode the path-beta firing: the function slot is a path-lambda,
          -- and `body'` is its single substitution.
          obtain ⟨pathBody, functionEq, reductEq⟩ :=
            pathBetaRowFiringDecompose
              (functionChild := RawTerm.weaken etaReduct)
              (argumentChild := RawTerm.newestVar)
              fires
          -- `weaken etaReduct = pathLam pathBody` forces `etaReduct = pathLam innerBody`.
          obtain ⟨innerBody, etaReductEq, weakenedBodyEq⟩ :=
            RawTerm.weaken_eq_pathLam_implies_source_pathLam functionEq
          -- The var-0 substitution exactly un-weakens: both reducts collapse to `etaReduct`.
          refine ⟨etaReduct, ?_, ReflTransClosure.refl _⟩
          -- LEFT = `pathLam body'` where `body' = subst0 pathBody newestVar = innerBody`;
          -- rewriting the right side to the same `pathLam innerBody` closes by reflexivity.
          rw [reductEq, weakenedBodyEq, RawTerm.subst0_lift_weaken_newestVar,
            etaReductEq]
          exact ReflTransClosure.refl _
      | inr functionCong =>
          -- A congruence strictly inside the pathApp cell.
          obtain ⟨pathAppChildren', body'Eq, pathAppChildStep⟩ := functionCong
          subst body'Eq
          cases pathAppChildStep with
          | here _rest functionStep =>
              -- The weakened function `weaken etaReduct` steps; reflect back to a step on `etaReduct`.
              obtain ⟨coreReduct, coreStep, renamedEq⟩ :=
                StepOverTable.reflectRename iotaRuleTable_isScopeUniform
                  RawRenaming.weaken
                  (sourceTerm := etaReduct)
                  (by
                    rw [← RawTerm.weaken_eq_rename]
                    exact functionStep)
              -- RIGHT: `etaReduct` iota-steps to `coreReduct`.
              -- LEFT: `pathLam (pathApp (weaken coreReduct) (var 0))` eta-contracts to `coreReduct`.
              refine ⟨coreReduct, ?_, ReflTransClosure.single (Or.inl coreStep)⟩
              -- LEFT cell, after rewriting the renamed function slot to `weaken coreReduct`.
              have leftEtaStep :
                  StepEtaRootTable
                    (RawTerm.mkGen .gen_pathLam ()
                      (.childCons
                        (RawTerm.mkGen .gen_pathApp ()
                          (.childCons (RawTerm.weaken coreReduct)
                            (.childCons RawTerm.newestVar .childNil)))
                        .childNil))
                    coreReduct :=
                StepEtaRootOverTable.etaRedex
                  etaPathLamRow_memTable rfl ()
                  (etaPathLamRow_contractsOnSource coreReduct)
              rw [← RawTerm.weaken_eq_rename] at renamedEq
              rw [← renamedEq]
              exact ReflTransClosure.single (Or.inr leftEtaStep)
          | there _head restStep =>
              -- The argument slot `var 0` would step — impossible (var has no children),
              -- or the trailing `childNil` would step — impossible.
              cases restStep with
              | here _rest argumentStep =>
                  exact absurd argumentStep
                    (fun varStep => noStepTableFromVarCell _ varStep)
              | there _head emptyStep => cases emptyStep
  | there _head emptyStep =>
      -- The pathLam spine's tail is `childNil` — it cannot step.
      cases emptyStep

end FX1Poly.Typed
