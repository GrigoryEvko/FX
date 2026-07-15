import FX1Poly.Typed.Equality.Eta.TableBetaEtaRootChildJoinPair
import FX1Poly.Typed.Equality.Eta.TypedEtaLamAnnotationJoinable
import FX1Poly.Core.Rewriting.Confluence.StepStarConfluenceViaTable
import FX1Poly.Core.Rewriting.Reduction.Step.StepLamDomainCong

/-! # FX1Poly/Typed/TableBetaEtaRootChildJoinLam
    — the per-child copy-replacement join for the function-lambda eta row.

The generic `childJoin` obligation of `crossQuadrantJoinOfChildJoin`
specialized to `etaLamRow`: an iota child congruence diverging from the
function-eta intro cell joins with the eta contraction.  The
function-lambda row is the GENUINELY-TYPED case — unlike `etaPairRow` and
`etaPathLamRow`, the lambda-beta-vs-eta peak is the Nederpelt
annotation clash, NON-joinable on raw terms, and the ONLY raw-tier
childJoin case that consumes the typed `guardOrigin`.

The function-eta source is
`lam domainAnn (app (weaken core) (var 0))` (TWO children: slot 0 = the
domain annotation, slot 1 = the body under one binder).  A table step
into the spine has three possible exits:

* **domain-slot congruence** — the domain annotation `domainAnn` steps;
  the observation reads slot 1 only, so the stepped spine STILL
  eta-contracts to `core = etaReduct`, joining the LEFT eta contraction
  with a RIGHT refl (the disjoint-slot case).
* **root beta** — the body `app (weaken core) (var 0)` root-fires beta
  iff `weaken core` is a lambda, i.e. `core = lam innerDomainAnn
  innerBody`.  The beta reduct un-weakens to `innerBody`, so LEFT is
  `lam domainAnn innerBody` while RIGHT `etaReduct = lam innerDomainAnn
  innerBody`: the two domain annotations need NOT agree.  This is where
  the typed guard resolves it — `guardOrigin` types the eta source, so
  `HasTypeDescPi.etaLamSourceAnnotationJoinable` yields the joinability
  `StepStar.Join innerDomainAnn domainAnn`; replaying both annotation
  chains through the lambda's domain child (`StepStar.lamDomainCong`),
  lifted across the iota-table adequacy (`StepStar.toTableClosure`) into
  the beta-eta-root union, joins LEFT and RIGHT at `lam commonAnn
  innerBody`.
* **function-slot congruence** — the weakened function `weaken core`
  steps; reflected back to a step on `core`
  (`StepOverTable.reflectRename` at `RawRenaming.weaken`), the RIGHT
  reduct `core` iota-steps to `core'`, the LEFT re-eta-contracts to
  `core'`, joining at `core'`.

## Zero-axiom verification

A structural inversion of `StepOverTableChildren` plus the typed
annotation extraction and the lambda-domain replay congruence; no
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Audit-gated in
`FX1PolyAudit/AuditTableBetaEtaRootConfluence.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core
open FX1Poly.Axis.Syntax

/-- The `etaLamRow` membership pin in the eta-rule table (first row). -/
theorem etaLamRow_memTable : etaLamRow ∈ etaRuleTable := .head _

/-- **`betaIotaRow` firing decomposition**: a successful β-cell firing on
a literal two-child `gen_app` spine forces the function slot to be a
`gen_lam` cell and pins the reduct to its single-substitution.  The
function-lambda twin of `pathBetaRowFiringDecompose`. -/
theorem betaRowFiringDecompose {scope : Nat}
    {functionChild argumentChild reduct : RawTerm scope}
    (fires : betaIotaRow.firesOn? ()
        (.childCons functionChild (.childCons argumentChild .childNil))
      = some reduct) :
    ∃ (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)),
      functionChild =
          RawTerm.mkGen .gen_lam ()
            (.childCons domainAnn (.childCons body .childNil)) ∧
        reduct = RawTerm.subst0 body argumentChild := by
  cases functionChild with
  | mkGen functionGenerator functionPayload functionChildren =>
      have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
      subst isHead
      cases functionPayload
      cases functionChildren with
      | childCons domainAnn lamRest =>
          cases lamRest with
          | childCons body lamNil =>
              cases lamNil
              exact ⟨domainAnn, body, rfl, (Option.some.inj fires).symm⟩

/-- **Function-eta source-shape inversion**: a successful `etaLamRow`
contraction forces the two intro children to be an unconstrained domain
annotation `domainAnn` (slot 0) and the canonical function-eta body
`app (weaken core) (var 0)` (slot 1).  The shape companion of
`etaPathLamRowContraction_introChildrenShape`, extracting BOTH the slot-0
domain and the slot-1 body shape. -/
theorem etaLamRowContraction_introChildrenShape {scope : Nat}
    {introChildren :
      RawTermChildren etaLamRow.introGenerator.binderShifts scope}
    {core : RawTerm scope}
    (contracts : etaLamRow.contractsOn? introChildren = some core) :
    ∃ domainAnn : RawTerm (scope + 0),
      introChildren =
        (RawTermChildren.childCons domainAnn
          (.childCons
            (RawTerm.mkGen .gen_app ()
              (.childCons (RawTerm.weaken core)
                (.childCons RawTerm.newestVar .childNil)))
            .childNil) :
          RawTermChildren Generator.gen_lam.binderShifts scope) := by
  match introChildren, contracts with
  | .childCons domainAnn (.childCons bodyChild .childNil), contracts =>
    have peeled :
        (({ introChildSlot := 1, observerHead := .gen_app, coreSlot := 0
          , binderDepth := 1, freshVarSlots := [1] } :
            EtaObservationSpec).extractCoreFrom?
          (RawTermChildren.childCons domainAnn
            (RawTermChildren.childCons bodyChild
              RawTermChildren.childNil))).bind some
        = some core := contracts
    match extractEq :
        ({ introChildSlot := 1, observerHead := .gen_app, coreSlot := 0
         , binderDepth := 1, freshVarSlots := [1] } :
           EtaObservationSpec).extractCoreFrom?
          (RawTermChildren.childCons domainAnn
            (RawTermChildren.childCons bodyChild
              RawTermChildren.childNil)) with
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
              = RawTerm.mkGen .gen_app observedPayload observedChildren :=
          Option.some.inj
            (lookupEq :
              some bodyChild
                = some (RawTerm.mkGen .gen_app observedPayload
                    observedChildren))
        subst bodyShape
        match observedChildren, freshHolds, coreExtract with
        | .childCons functionChild (.childCons argumentChild .childNil),
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
                  RawTerm.strengthenBy? 1 functionChild = some core :=
                coreExtract
              have functionShape : RawTerm.weakenBy 1 core = functionChild :=
                RawTerm.weakenBy_strengthenBy? 1 functionChild core strengthened
              refine ⟨domainAnn, ?_⟩
              rw [← functionShape]
              rfl

set_option linter.unusedVariables false in
/-- ★ **Per-child copy-replacement join, function-lambda eta row.**  The
`childJoin` obligation of `crossQuadrantJoinOfChildJoin` specialized to
`etaLamRow`.  One of the two intro children steps; inverting it splits
into the disjoint domain-slot congruence (joins by the unchanged eta
contraction), the root-beta peak (joins through the typed
annotation guard `guardOrigin`), and the function-slot congruence (joins
at the reflected reduct `core'`).  This is the SOLE childJoin case
consuming the typed `guardOrigin` — the Nederpelt annotation clash. -/
theorem childJoinLam {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {introPayload : etaLamRow.introGenerator.payload scope}
    {introChildren steppedChildren :
      RawTermChildren etaLamRow.introGenerator.binderShifts scope}
    {etaReduct : RawTerm scope}
    (guardOrigin : ∃ stepClassifier : RawTerm scope,
      HasTypeDescPi profile context
        (.mkGen etaLamRow.introGenerator introPayload introChildren) stepClassifier)
    (childStep : StepOverTableChildren iotaRuleTable introChildren steppedChildren)
    (contracts : etaLamRow.contractsOn? introChildren = some etaReduct) :
    Joinable StepTableBetaEtaRoot
      (.mkGen etaLamRow.introGenerator introPayload steppedChildren) etaReduct := by
  -- Force the intro spine to the canonical function-eta shape.
  obtain ⟨domainAnn, introShape⟩ := etaLamRowContraction_introChildrenShape contracts
  subst introShape
  -- The function-eta payload is `Unit`.
  cases introPayload
  -- Either the domain (slot 0) steps, or the body (slot 1) steps.
  cases childStep with
  | here _rest _domainStep =>
      -- ★ DOMAIN-SLOT congruence: the domain annotation steps to `steppedDomain`.
      -- The observation reads slot 1, untouched, so the stepped spine STILL
      -- eta-contracts to `etaReduct`.  LEFT eta-contracts; RIGHT is refl.
      rename_i steppedDomain
      refine ⟨etaReduct, ?_, ReflTransClosure.refl _⟩
      exact ReflTransClosure.single
        (Or.inr
          (StepEtaRootOverTable.etaRedex etaLamRow_memTable rfl ()
            (etaLamRow_contractsOnSource steppedDomain etaReduct)))
  | there _head bodyOuterStep =>
      -- The body child (slot 1) is the one that steps.
      cases bodyOuterStep with
      | here _rest bodyStep =>
          -- `bodyStep : StepOverTable … (app (weaken etaReduct) (var 0)) body'`.
          cases bodyStep.invertOrCong rfl with
          | inl rootFires =>
              -- ★ ROOT BETA: only `betaIotaRow` fires at the `gen_app` cell.
              obtain ⟨iotaRule, iotaIsRow, elimPayload, spine, cellEq, fires⟩ :=
                rootFires
              have headIsApp : iotaRule.elimGenerator = .gen_app :=
                congrArg
                  (fun cell => match cell with
                    | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
                  cellEq
              have rowIsBeta : iotaRule = betaIotaRow :=
                iotaRowAtAppIsBeta iotaIsRow headIsApp
              subst rowIsBeta
              -- Pin the firing spine: the function slot is `weaken etaReduct`.
              injection cellEq with _scopeRefl _genRefl _payloadEq spineEq
              subst spineEq
              cases elimPayload
              obtain ⟨weakenedDomain, weakenedBody, weakenedFunctionEq, reductEq⟩ :=
                betaRowFiringDecompose
                  (functionChild := RawTerm.weaken etaReduct)
                  (argumentChild := RawTerm.newestVar)
                  fires
              -- `weaken etaReduct = lam …` forces `etaReduct = lam innerDomainAnn innerBody`.
              obtain ⟨innerDomainAnn, innerBody, etaReductEq, _weakenedDomainEq,
                  weakenedBodyEq⟩ :=
                RawTerm.weaken_eq_lam_implies_source_lam weakenedFunctionEq
              -- The typed guard supplies the annotation joinability, taken as a
              -- `StepStar.Join innerDomainAnn domainAnn`.
              obtain ⟨stepClassifier, typedSource⟩ := guardOrigin
              have annotationJoin :
                  StepStar.Join innerDomainAnn domainAnn :=
                HasTypeDescPi.etaLamSourceAnnotationJoinable typedSource
                  innerDomainAnn innerBody etaReductEq
              -- Reduce LEFT to the canonical lambda cell `lam domainAnn innerBody`
              -- (the beta reduct un-weakens to `innerBody`) and RIGHT to
              -- `lam innerDomainAnn innerBody`, then route the annotation clash
              -- through the table-native Nederpelt diagonal join.
              rw [reductEq, weakenedBodyEq, RawTerm.subst0_lift_weaken_newestVar,
                etaReductEq]
              exact etaLamAnnotationClashJoinsOverTable annotationJoin
          | inr functionCong =>
              -- A congruence strictly inside the `gen_app` cell.
              obtain ⟨appChildren', body'Eq, appChildStep⟩ := functionCong
              subst body'Eq
              cases appChildStep with
              | here _rest functionStep =>
                  -- The weakened function `weaken etaReduct` steps; reflect back to `etaReduct`.
                  obtain ⟨coreReduct, coreStep, renamedEq⟩ :=
                    StepOverTable.reflectRename iotaRuleTable_isScopeUniform
                      RawRenaming.weaken
                      (sourceTerm := etaReduct)
                      (by
                        rw [← RawTerm.weaken_eq_rename]
                        exact functionStep)
                  -- RIGHT: `etaReduct` iota-steps to `coreReduct`.
                  -- LEFT: `lam domainAnn (app (weaken coreReduct) (var 0))` eta-contracts.
                  refine ⟨coreReduct, ?_, ReflTransClosure.single (Or.inl coreStep)⟩
                  have leftEtaStep :
                      StepEtaRootTable
                        (RawTerm.mkGen .gen_lam ()
                          (.childCons domainAnn
                            (.childCons
                              (RawTerm.mkGen .gen_app ()
                                (.childCons (RawTerm.weaken coreReduct)
                                  (.childCons RawTerm.newestVar .childNil)))
                              .childNil)))
                        coreReduct :=
                    StepEtaRootOverTable.etaRedex
                      etaLamRow_memTable rfl ()
                      (etaLamRow_contractsOnSource domainAnn coreReduct)
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
          -- The lam spine's tail after slot 1 is `childNil`.
          cases emptyStep

end FX1Poly.Typed
