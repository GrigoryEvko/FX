import FX1Poly.Typed.Metatheory.SubjectReduction.ElimGateReassembleBounded
import FX1Poly.Typed.Metatheory.SubjectReduction.DependentElimObligationsDriftBounded
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimOutputTypeDrift
import FX1Poly.Typed.Metatheory.SubjectReduction.UsabilityHoldsUnderObligationsDriftBounded
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/ElimGateBranchesBounded
    — SR-WF-TIEOFF (elim third): the per-generator branches of the FUEL-BOUNDED eliminator-congruence gate

The fuel-bounded twin of `ElimGateBranches.lean`.  Each branch is a near-verbatim mirror of its unbounded
counterpart, with the standard swaps that thread the fuel-bounded child-SR:

  * the universal `childSubjectReduction : UnionChildSubjectReduction profile` becomes the fuel-bounded
    `childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (ruleX.memberCell scope args).size`
    (the bound the gate `UnionElimCongruenceClosesBounded` supplies);
  * the obligation drift `*ObligationsDriftUnderArgStep` becomes its bounded twin
    `*ObligationsDriftUnderArgStepBounded` (already shipped in `CleanElimObligationsDriftBounded` /
    `RecursorElimObligationsDriftBounded` / `DependentElimObligationsDriftBounded`);
  * the reassembly `elimGateRowReassemble` becomes `elimGateRowReassembleBounded`;
  * the after-args usability driver `usabilityHoldsUnderObligationsDrift` becomes
    `usabilityHoldsUnderObligationsDriftBelow` (the bounded subject drift is length ≤ 1, so it needs only the
    single-step preservation, no child-SR);
  * the after-args premise driver `premisesHoldUnderObligationsDrift` becomes `premisesHoldUnderObligationsDriftBelow`.

The OUTPUT-drift lemmas (`appOutputTypeDriftUnderArgStep`, …) are bound-independent, so the unbounded ones are
reused verbatim.

## The two after-usability routes (the bounded elim gate carries NO `usabilityHolds`)

Unlike the bounded INTRO gate, `UnionElimCongruenceClosesBounded` does not carry a before-step usability premise
(`congruenceClosesGenericAuxBounded` drops the native `elim` arm's `usabilityHolds`).  So the after-args usability
the bounded reassembly demands splits the rows two ways:

  * **rigid-classifier rows** (`fst` / `snd`): every obligation classifier is a rigid former (`product` / universe
    code) provably `≢ interval`, so the after-args usability discharges PURELY from the re-typed obligations via
    `typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval` — no before-usability needed.  These branches are
    UNCONDITIONAL.
  * **step-preservation rows** (`app` / `boolElim` / `natElim` / `natRec`): a branch obligation reads the motive /
    an arbitrary param, so its usability is NOT derivable from typing alone; the branch instead threads the
    before-step usability (`usabilityHolds`) forward through `usabilityHoldsUnderObligationsDriftBelow`.  That
    `usabilityHolds` is the honest residual the dispatch supplies.
  * the `pathApp` row threads a `.dimensional` argument-usability residual (`argumentReductUsable`) — the use-site
    statement of interval non-fibrancy — and discharges the rigid `path` / `carrier` obligations from typing.

The four dependent-match rows whose bounded drift is not yet shipped (`optionMatch` / `eitherMatch` / `idJ` /
`listElim`) are NOT in this file; the dispatch takes them as honest per-row premises.

## Zero-axiom

The shipped bounded drift builders + `elimGateRowReassembleBounded` + `usabilityHoldsUnderObligationsDriftBelow` +
`premisesHoldUnderObligationsDriftBelow` + `typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval` + the
head-stability refuters + the `mkGen` injection recipe.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## Head-stability refuters — `intervalTypeCell ≢ <rigid former>` (local twins of the `ElimGateBranches` privates) -/

/-- (local) **Interval ≢ Product under conversion.** -/
private theorem intervalNotConvProductCodeBounded {scope : Nat} (firstType secondType : RawTerm scope) :
    ¬ Conv (intervalTypeCell : RawTerm scope) (productTypeCell firstType secondType) :=
  fun convertibility => Conv.refutedByDistinctStableHeads convertibility
    (fun _reduct chain => headReaches_intervalTypeCell chain)
    (fun _reduct chain => headReaches_productTypeCell chain)
    (fun headsEqual => Generator.noConfusion headsEqual)

/-! ## The rigid-classifier clean rows — `fst` / `snd` (UNCONDITIONAL after-usability discharge) -/

/-- (local) **`fst`'s after-args usability, discharged from the re-typed obligations.**  Mirror of the unbounded
`fstUsabilityDischarge`: the pair obligation (at `productType`) and the self-certifying first-type obligation (at
`universeCode`) are both rigid `≢ interval`, so fibrant usability follows from the typed-at-non-interval bridge. -/
private theorem fstAfterUsableBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (firstType secondType : RawTerm scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag) (wellFormed : WfContextUnion context)
    {argsAfter : RawTermChildren fstElimRule.argShifts scope}
    (premisesAfter : ∀ obligation ∈ fstElimRule.obligations scope context argsAfter
        (.childCons firstType (.childCons secondType .childNil)) level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) :
    ∀ obligation ∈ fstElimRule.obligations scope context argsAfter
        (.childCons firstType (.childCons secondType .childNil)) level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true := by
  cases argsAfter with
  | childCons pairAfter restAfter =>
    cases restAfter
    intro obligation hmem
    cases hmem with
    | head =>
        exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
          (WfContextUnion.allLocksAreInterval context wellFormed)
          (intervalNotConvProductCodeBounded firstType secondType) (premisesAfter _ (List.Mem.head _))
    | tail _ hmem => cases hmem with
      | head =>
          exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
            (WfContextUnion.allLocksAreInterval context wellFormed)
            (intervalTypeCell_not_conv_universeCodeCell level0 flag)
            (premisesAfter _ (List.Mem.tail _ (List.Mem.head _)))
      | tail _ hmem => cases hmem

/-- (local) **`snd`'s after-args usability** — the `fst` twin (the self-certifying obligation pins `secondType`). -/
private theorem sndAfterUsableBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (firstType secondType : RawTerm scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag) (wellFormed : WfContextUnion context)
    {argsAfter : RawTermChildren sndElimRule.argShifts scope}
    (premisesAfter : ∀ obligation ∈ sndElimRule.obligations scope context argsAfter
        (.childCons firstType (.childCons secondType .childNil)) level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) :
    ∀ obligation ∈ sndElimRule.obligations scope context argsAfter
        (.childCons firstType (.childCons secondType .childNil)) level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true := by
  cases argsAfter with
  | childCons pairAfter restAfter =>
    cases restAfter
    intro obligation hmem
    cases hmem with
    | head =>
        exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
          (WfContextUnion.allLocksAreInterval context wellFormed)
          (intervalNotConvProductCodeBounded firstType secondType) (premisesAfter _ (List.Mem.head _))
    | tail _ hmem => cases hmem with
      | head =>
          exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
            (WfContextUnion.allLocksAreInterval context wellFormed)
            (intervalTypeCell_not_conv_universeCodeCell level0 flag)
            (premisesAfter _ (List.Mem.tail _ (List.Mem.head _)))
      | tail _ hmem => cases hmem

/-- **The `fst` branch (bounded)** — UNCONDITIONAL.  A stepped `fst` cell re-types at its (param) output type,
`Conv`-equal to the original; after-usability discharges from the re-typed obligations (all rigid). -/
theorem fstElimGateBranchClosesBounded {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren fstElimRule.argShifts scope) (params : RawTermChildren fstElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ fstElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (fstElimRule.memberCell scope args).size)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : fstElimRule.memberCell scope args = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (fstElimRule.outputType scope args params) := by
  match args, params with
  | .childCons pairTerm .childNil, .childCons firstType (.childCons secondType .childNil) =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have pairTyped : HasTypeUnion profile context pairTerm (productTypeCell firstType secondType) :=
      premisesHold _ (List.Mem.head _)
    have pairClassifierFormed : UnionClassifierIsType profile context (productTypeCell firstType secondType) :=
      HasTypeUnion.classifierIsType pairTyped wellFormed
    have firstTypeClassifierFormed : UnionClassifierIsType profile context (universeCodeCell level0 flag) :=
      ⟨_, _, HasTypeUnion.universeFormation context level0 flag⟩
    have memberAfterEq : fstElimRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_fst () childrenAfter := by
      cases childrenAfter with
      | childCons headAfter restAfter => cases restAfter; rfl
    have drift := fstObligationsDriftUnderArgStepBounded level0 level1 flag pairClassifierFormed
      firstTypeClassifierFormed childStep
    have premisesAfter := premisesHoldUnderObligationsDriftBelow drift childSubjectReductionBelow premisesHold
    rw [← memberAfterEq]
    exact elimGateRowReassembleBounded .gen_fst fstElimRule
      (.childCons firstType (.childCons secondType .childNil)) level0 level1 flag rfl premisesHold
      childSubjectReductionBelow drift (Conv.refl _)
      (fstAfterUsableBounded firstType secondType level0 level1 flag wellFormed premisesAfter)

/-- **The `snd` branch (bounded)** — UNCONDITIONAL, the `fst` twin (output `secondType`, a param). -/
theorem sndElimGateBranchClosesBounded {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren sndElimRule.argShifts scope) (params : RawTermChildren sndElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ sndElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (sndElimRule.memberCell scope args).size)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : sndElimRule.memberCell scope args = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (sndElimRule.outputType scope args params) := by
  match args, params with
  | .childCons pairTerm .childNil, .childCons firstType (.childCons secondType .childNil) =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have pairTyped : HasTypeUnion profile context pairTerm (productTypeCell firstType secondType) :=
      premisesHold _ (List.Mem.head _)
    have pairClassifierFormed : UnionClassifierIsType profile context (productTypeCell firstType secondType) :=
      HasTypeUnion.classifierIsType pairTyped wellFormed
    have secondTypeClassifierFormed : UnionClassifierIsType profile context (universeCodeCell level0 flag) :=
      ⟨_, _, HasTypeUnion.universeFormation context level0 flag⟩
    have memberAfterEq : sndElimRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_snd () childrenAfter := by
      cases childrenAfter with
      | childCons headAfter restAfter => cases restAfter; rfl
    have drift := sndObligationsDriftUnderArgStepBounded level0 level1 flag pairClassifierFormed
      secondTypeClassifierFormed childStep
    have premisesAfter := premisesHoldUnderObligationsDriftBelow drift childSubjectReductionBelow premisesHold
    rw [← memberAfterEq]
    exact elimGateRowReassembleBounded .gen_snd sndElimRule
      (.childCons firstType (.childCons secondType .childNil)) level0 level1 flag rfl premisesHold
      childSubjectReductionBelow drift (Conv.refl _)
      (sndAfterUsableBounded firstType secondType level0 level1 flag wellFormed premisesAfter)

/-! ## The step-preservation clean row — `app` (mixed output drift, before-usability threaded) -/

/-- **The `app` branch (bounded)** — the mixed-output row.  Output `subst0 codomainCode argument` drifts when the
`argument` child steps; a function step leaves it fixed.  After-args usability is threaded from the before-step
`usabilityHolds` via the bounded step-preservation driver (both obligations are fibrant). -/
theorem appElimGateBranchClosesBounded {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren appElimRule.argShifts scope) (params : RawTermChildren appElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ appElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (appElimRule.memberCell scope args).size)
    (wellFormed : WfContextUnion context)
    (usabilityHolds : ∀ obligation ∈ appElimRule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : appElimRule.memberCell scope args = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (appElimRule.outputType scope args params) := by
  match args, params with
  | .childCons function (.childCons argument .childNil), .childCons domainCode (.childCons codomainCode .childNil) =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have functionTyped : HasTypeUnion profile context function (piTyCodeCell domainCode codomainCode) :=
      premisesHold _ (List.Mem.head _)
    have argumentTyped : HasTypeUnion profile context argument domainCode :=
      premisesHold _ (List.Mem.tail _ (List.Mem.head _))
    have functionClassifierFormed : UnionClassifierIsType profile context
        (piTyCodeCell domainCode codomainCode) :=
      HasTypeUnion.classifierIsType functionTyped wellFormed
    have argumentClassifierFormed : UnionClassifierIsType profile context domainCode :=
      HasTypeUnion.classifierIsType argumentTyped wellFormed
    have memberAfterEq : appElimRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_app () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest1 => cases rest1 with
        | childCons _ rest2 => cases rest2; rfl
    have drift := appObligationsDriftUnderArgStepBounded level0 level1 flag functionClassifierFormed
      argumentClassifierFormed childStep
    rw [← memberAfterEq]
    exact elimGateRowReassembleBounded .gen_app appElimRule
      (.childCons domainCode (.childCons codomainCode .childNil)) level0 level1 flag rfl premisesHold
      childSubjectReductionBelow drift
      (appOutputTypeDriftUnderArgStep function domainCode codomainCode childStep)
      (usabilityHoldsUnderObligationsDriftBelow drift
        (by intro obligation hmem
            cases hmem with
            | head => rfl
            | tail _ hmem => cases hmem with
              | head => rfl
              | tail _ hmem => cases hmem)
        premisesHold usabilityHolds)

/-! ## The dimensional clean row — `pathApp` (rigid path / carrier discharge, `.dimensional` argument residual) -/

/-- (local) **Interval ≢ Bridge under conversion.** -/
private theorem intervalNotConvBridgeCodeBounded {scope : Nat}
    (carrierCode leftEndpoint rightEndpoint : RawTerm scope) :
    ¬ Conv (intervalTypeCell : RawTerm scope) (bridgeTypeCell carrierCode leftEndpoint rightEndpoint) :=
  fun convertibility => Conv.refutedByDistinctStableHeads convertibility
    (fun _reduct chain => headReaches_intervalTypeCell chain)
    (fun _reduct chain => headReaches_bridgeTypeCell chain)
    (fun headsEqual => Generator.noConfusion headsEqual)

/-- (local) **`pathApp`'s after-args usability.**  Mirror of the unbounded `pathAppUsabilityDischarge`: the `path`
obligation (at the bridge type) and the self-certifying `carrier` obligation (at `universeCode`) are rigid
`≢ interval`, so fibrant usability follows from the typed-at-non-interval bridge; the interval-typed `argument`
obligation, consumed at the `.dimensional` modality, takes the supplied dimensional residual. -/
private theorem pathAppAfterUsableBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (carrierCode leftEndpoint rightEndpoint : RawTerm scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag) (wellFormed : WfContextUnion context)
    (argumentReductUsable : ∀ {subject : RawTerm scope},
      HasTypeUnion profile context subject intervalTypeCell →
        context.isSubjectUsableAtModality subject ObligationModality.dimensional = true)
    {argsAfter : RawTermChildren pathAppElimRule.argShifts scope}
    (premisesAfter : ∀ obligation ∈ pathAppElimRule.obligations scope context argsAfter
        (.childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))
        level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) :
    ∀ obligation ∈ pathAppElimRule.obligations scope context argsAfter
        (.childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))
        level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true := by
  cases argsAfter with
  | childCons pathAfter rest1 => cases rest1 with
    | childCons argumentAfter rest2 =>
      cases rest2
      intro obligation hmem
      cases hmem with
      | head =>
          exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
            (WfContextUnion.allLocksAreInterval context wellFormed)
            (intervalNotConvBridgeCodeBounded carrierCode leftEndpoint rightEndpoint)
            (premisesAfter _ (List.Mem.head _))
      | tail _ hmem => cases hmem with
        | head => exact argumentReductUsable (premisesAfter _ (List.Mem.tail _ (List.Mem.head _)))
        | tail _ hmem => cases hmem with
          | head =>
              exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
                (WfContextUnion.allLocksAreInterval context wellFormed)
                (intervalTypeCell_not_conv_universeCodeCell level0 flag)
                (premisesAfter _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
          | tail _ hmem => cases hmem

/-- **The `pathApp` branch (bounded)** — output `carrierCode`, a param (`Conv.refl`).  Path / interval-argument /
carrier obligations formed via `classifierIsType` / `universeFormation`; after-usability discharges the rigid
path / carrier and threads the supplied `.dimensional` residual for the interval argument. -/
theorem pathAppElimGateBranchClosesBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (args : RawTermChildren pathAppElimRule.argShifts scope)
    (params : RawTermChildren pathAppElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ pathAppElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile
      (pathAppElimRule.memberCell scope args).size)
    (wellFormed : WfContextUnion context)
    (argumentReductUsable : ∀ {subject : RawTerm scope},
      HasTypeUnion profile context subject intervalTypeCell →
        context.isSubjectUsableAtModality subject ObligationModality.dimensional = true)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : pathAppElimRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (pathAppElimRule.outputType scope args params) := by
  match args, params with
  | .childCons path (.childCons argument .childNil),
    .childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)) =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have pathTyped : HasTypeUnion profile context path
        (bridgeTypeCell carrierCode leftEndpoint rightEndpoint) :=
      premisesHold _ (List.Mem.head _)
    have argumentTyped : HasTypeUnion profile context argument intervalTypeCell :=
      premisesHold _ (List.Mem.tail _ (List.Mem.head _))
    have pathClassifierFormed : UnionClassifierIsType profile context
        (bridgeTypeCell carrierCode leftEndpoint rightEndpoint) :=
      HasTypeUnion.classifierIsType pathTyped wellFormed
    have argumentClassifierFormed : UnionClassifierIsType profile context intervalTypeCell :=
      HasTypeUnion.classifierIsType argumentTyped wellFormed
    have carrierClassifierFormed : UnionClassifierIsType profile context (universeCodeCell level0 flag) :=
      ⟨_, _, HasTypeUnion.universeFormation context level0 flag⟩
    have memberAfterEq : pathAppElimRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_pathApp () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest1 => cases rest1 with
        | childCons _ rest2 => cases rest2; rfl
    have drift := pathAppObligationsDriftUnderArgStepBounded level0 level1 flag pathClassifierFormed
      argumentClassifierFormed carrierClassifierFormed childStep
    have premisesAfter := premisesHoldUnderObligationsDriftBelow drift childSubjectReductionBelow premisesHold
    rw [← memberAfterEq]
    exact elimGateRowReassembleBounded .gen_pathApp pathAppElimRule
      (.childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))
      level0 level1 flag rfl premisesHold childSubjectReductionBelow drift (Conv.refl _)
      (pathAppAfterUsableBounded carrierCode leftEndpoint rightEndpoint level0 level1 flag wellFormed
        argumentReductUsable premisesAfter)

/-! ## The step-preservation recursors — `natElim` / `natRec` (before-usability threaded) -/

/-- **The `natElim` branch (bounded)** — the binder-extended recursor.  The step-branch obligation's formedness
comes from the motive typing via `natElimDependentSuccBranchType_formed_ofMotive`; after-usability threads the
before-step `usabilityHolds` through the bounded step-preservation driver. -/
theorem natElimGateBranchClosesBounded {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren natElimRule.argShifts scope) (params : RawTermChildren natElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ natElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (natElimRule.memberCell scope args).size)
    (wellFormed : WfContextUnion context)
    (usabilityHolds : ∀ obligation ∈ natElimRule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : natElimRule.memberCell scope args = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (natElimRule.outputType scope args params) := by
  match args, params with
  | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))), .childNil =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have scrutineeClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.head _)) wellFormed
    have baseBranchClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.tail _ (List.Mem.head _))) wellFormed
    have motiveTyped : HasTypeUnion profile (context.cons natTypeCell) motive (universeCodeCell level0 flag) :=
      premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have stepBranchClassifierFormed : UnionClassifierIsType profile ((context.cons natTypeCell).cons motive)
        (natElimDependentSuccBranchType motive) :=
      ⟨level0, flag, natElimDependentSuccBranchType_formed_ofMotive context motive level0 flag motiveTyped⟩
    have memberAfterEq : natElimRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_natElim () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest1 => cases rest1 with
        | childCons _ rest2 => cases rest2 with
          | childCons _ rest3 => cases rest3 with
            | childCons _ rest4 => cases rest4; rfl
    have drift := natElimObligationsDriftUnderArgStepBounded level0 level1 flag motiveTyped
      scrutineeClassifierFormed baseBranchClassifierFormed stepBranchClassifierFormed
      childSubjectReductionBelow childStep
    rw [← memberAfterEq]
    exact elimGateRowReassembleBounded .gen_natElim natElimRule .childNil level0 level1 flag rfl premisesHold
      childSubjectReductionBelow drift
      (natElimOutputTypeDriftUnderArgStep .childNil childStep)
      (usabilityHoldsUnderObligationsDriftBelow drift
        (by intro obligation hmem
            cases hmem with
            | head => rfl
            | tail _ hmem => cases hmem with
              | head => rfl
              | tail _ hmem => cases hmem with
                | head => rfl
                | tail _ hmem => cases hmem with
                  | head => rfl
                  | tail _ hmem => cases hmem)
        premisesHold usabilityHolds)

/-- **The `natRec` branch (bounded)** — the `natElim` twin (`natRecElimRule` shares `natElim`'s drift verbatim). -/
theorem natRecGateBranchClosesBounded {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren natRecElimRule.argShifts scope)
    (params : RawTermChildren natRecElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ natRecElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (natRecElimRule.memberCell scope args).size)
    (wellFormed : WfContextUnion context)
    (usabilityHolds : ∀ obligation ∈ natRecElimRule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : natRecElimRule.memberCell scope args = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (natRecElimRule.outputType scope args params) := by
  match args, params with
  | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))), .childNil =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have scrutineeClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.head _)) wellFormed
    have baseBranchClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.tail _ (List.Mem.head _))) wellFormed
    have motiveTyped : HasTypeUnion profile (context.cons natTypeCell) motive (universeCodeCell level0 flag) :=
      premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have stepBranchClassifierFormed : UnionClassifierIsType profile ((context.cons natTypeCell).cons motive)
        (natElimDependentSuccBranchType motive) :=
      ⟨level0, flag, natElimDependentSuccBranchType_formed_ofMotive context motive level0 flag motiveTyped⟩
    have memberAfterEq : natRecElimRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_natRec () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest1 => cases rest1 with
        | childCons _ rest2 => cases rest2 with
          | childCons _ rest3 => cases rest3 with
            | childCons _ rest4 => cases rest4; rfl
    have drift := natRecElimObligationsDriftUnderArgStepBounded level0 level1 flag motiveTyped
      scrutineeClassifierFormed baseBranchClassifierFormed stepBranchClassifierFormed
      childSubjectReductionBelow childStep
    rw [← memberAfterEq]
    exact elimGateRowReassembleBounded .gen_natRec natRecElimRule .childNil level0 level1 flag rfl premisesHold
      childSubjectReductionBelow drift
      (natRecOutputTypeDriftUnderArgStep .childNil childStep)
      (usabilityHoldsUnderObligationsDriftBelow drift
        (by intro obligation hmem
            cases hmem with
            | head => rfl
            | tail _ hmem => cases hmem with
              | head => rfl
              | tail _ hmem => cases hmem with
                | head => rfl
                | tail _ hmem => cases hmem with
                  | head => rfl
                  | tail _ hmem => cases hmem)
        premisesHold usabilityHolds)

/-! ## The step-preservation dependent-match row — `boolElim` (cell-spine-permuting) -/

/-- **The `boolElim` branch (bounded)** — cell-spine-aligned via per-position reindexing.  `boolElimCell` emits the
spine `(motive, then, else, scrutinee)`, so the gate's `childStep` steps that spine; we `cases` the spine step into
its four positions, reconstruct the corresponding `args`-order `StepChildren` (motive at `args` 0, scrutinee at
`args` 1, then at `args` 2, else at `args` 3) for the args-ordered bounded drift, and let `elimGateRowReassembleBounded`
unify its `memberCell scope argsAfter` conclusion with the stepped spine by `isDefEq`.  After-usability threads the
before-step `usabilityHolds` through the bounded step-preservation driver. -/
theorem boolElimGateBranchClosesBounded {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren boolElimRule.argShifts scope)
    (params : RawTermChildren boolElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ boolElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (boolElimRule.memberCell scope args).size)
    (wellFormed : WfContextUnion context)
    (usabilityHolds : ∀ obligation ∈ boolElimRule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : boolElimRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (boolElimRule.outputType scope args params) := by
  match args, params with
  | .childCons motive (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil))),
    .childNil =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have scrutineeClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.head _)) wellFormed
    have thenBranchClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.tail _ (List.Mem.head _))) wellFormed
    have elseBranchClassifierFormed :=
      HasTypeUnion.classifierIsType
        (premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) wellFormed
    have motiveTyped : HasTypeUnion profile (context.cons boolTypeCell) motive (universeCodeCell level0 flag) :=
      premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have allFibrant : ∀ obligation ∈ boolElimRule.obligations scope context
        (.childCons motive (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil))))
        .childNil level0 level1 flag,
        obligation.modality = ObligationModality.fibrant := by
      intro obligation hmem
      cases hmem with
      | head => rfl
      | tail _ hmem => cases hmem with
        | head => rfl
        | tail _ hmem => cases hmem with
          | head => rfl
          | tail _ hmem => cases hmem with
            | head => rfl
            | tail _ hmem => cases hmem
    cases childStep with
    | here _ motiveStep =>
        exact elimGateRowReassembleBounded .gen_boolElim boolElimRule .childNil level0 level1 flag rfl premisesHold
          childSubjectReductionBelow
          (boolElimObligationsDriftUnderArgStepBounded level0 level1 flag motiveTyped scrutineeClassifierFormed
            thenBranchClassifierFormed elseBranchClassifierFormed childSubjectReductionBelow
            (StepChildren.here _ motiveStep))
          (boolElimOutputTypeDriftUnderArgStep .childNil (StepChildren.here _ motiveStep))
          (usabilityHoldsUnderObligationsDriftBelow
            (boolElimObligationsDriftUnderArgStepBounded level0 level1 flag motiveTyped scrutineeClassifierFormed
              thenBranchClassifierFormed elseBranchClassifierFormed childSubjectReductionBelow
              (StepChildren.here _ motiveStep))
            allFibrant premisesHold usabilityHolds)
    | there _ tail1 => cases tail1 with
      | here _ thenStep =>
          exact elimGateRowReassembleBounded .gen_boolElim boolElimRule .childNil level0 level1 flag rfl premisesHold
            childSubjectReductionBelow
            (boolElimObligationsDriftUnderArgStepBounded level0 level1 flag motiveTyped scrutineeClassifierFormed
              thenBranchClassifierFormed elseBranchClassifierFormed childSubjectReductionBelow
              (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ thenStep))))
            (boolElimOutputTypeDriftUnderArgStep .childNil
              (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ thenStep))))
            (usabilityHoldsUnderObligationsDriftBelow
              (boolElimObligationsDriftUnderArgStepBounded level0 level1 flag motiveTyped scrutineeClassifierFormed
                thenBranchClassifierFormed elseBranchClassifierFormed childSubjectReductionBelow
                (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ thenStep))))
              allFibrant premisesHold usabilityHolds)
      | there _ tail2 => cases tail2 with
        | here _ elseStep =>
            exact elimGateRowReassembleBounded .gen_boolElim boolElimRule .childNil level0 level1 flag rfl
              premisesHold childSubjectReductionBelow
              (boolElimObligationsDriftUnderArgStepBounded level0 level1 flag motiveTyped scrutineeClassifierFormed
                thenBranchClassifierFormed elseBranchClassifierFormed childSubjectReductionBelow
                (StepChildren.there _ (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ elseStep)))))
              (boolElimOutputTypeDriftUnderArgStep .childNil
                (StepChildren.there _ (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ elseStep)))))
              (usabilityHoldsUnderObligationsDriftBelow
                (boolElimObligationsDriftUnderArgStepBounded level0 level1 flag motiveTyped scrutineeClassifierFormed
                  thenBranchClassifierFormed elseBranchClassifierFormed childSubjectReductionBelow
                  (StepChildren.there _ (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ elseStep)))))
                allFibrant premisesHold usabilityHolds)
        | there _ tail3 => cases tail3 with
          | here _ scrutineeStep =>
              exact elimGateRowReassembleBounded .gen_boolElim boolElimRule .childNil level0 level1 flag rfl
                premisesHold childSubjectReductionBelow
                (boolElimObligationsDriftUnderArgStepBounded level0 level1 flag motiveTyped scrutineeClassifierFormed
                  thenBranchClassifierFormed elseBranchClassifierFormed childSubjectReductionBelow
                  (StepChildren.there _ (StepChildren.here _ scrutineeStep)))
                (boolElimOutputTypeDriftUnderArgStep .childNil
                  (StepChildren.there _ (StepChildren.here _ scrutineeStep)))
                (usabilityHoldsUnderObligationsDriftBelow
                  (boolElimObligationsDriftUnderArgStepBounded level0 level1 flag motiveTyped scrutineeClassifierFormed
                    thenBranchClassifierFormed elseBranchClassifierFormed childSubjectReductionBelow
                    (StepChildren.there _ (StepChildren.here _ scrutineeStep)))
                  allFibrant premisesHold usabilityHolds)
          | there _ emptyTailStep => cases emptyTailStep

end FX1Poly.Typed
