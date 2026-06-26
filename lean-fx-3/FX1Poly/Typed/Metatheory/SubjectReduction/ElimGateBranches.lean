import FX1Poly.Typed.Metatheory.SubjectReduction.ElimGateReassemble
import FX1Poly.Typed.Metatheory.SubjectReduction.CleanElimObligationsDrift
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimOutputTypeDrift
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/ElimGateBranches
    — SR-DSL-5: the SPINE-ALIGNED per-generator branches of the eliminator-congruence gate

`UnionElimCongruenceCloses` (HasTypeUnionCongruenceClosesGeneric.lean) dispatches on the eliminator generator.
This file ships the per-generator BRANCH lemmas: each proves the gate conclusion for ONE eliminator, given the
gate's hypotheses specialized to that rule.  The shape is uniform per row:

  1. destructure the rule's `args` / `params` (a fixed `childCons` shape from the rule's arity);
  2. reduce `memberCell scope args` to its `mkGen genX payloadX args` form and inject the gate's `memberCell =
     mkGen reformed…` equation to pin `reformedGenerator = genX`, `reformedPayload = payloadX`,
     `childrenBefore = args`;
  3. derive the per-obligation classifier-formedness witnesses the row's `*ObligationsDriftUnderArgStep` needs
     (`classifierIsType` over `WfContextUnion` for the typed obligations; `universeFormation` for the universe-code
     ones);
  4. build the obligation drift + output drift and hand them to the generic `elimGateRowReassemble`;
  5. bridge `memberCell scope childrenAfter = mkGen genX payloadX childrenAfter` (the reformed cell) by the same
     `childCons`-shape reduction.

## The cell-spine vs rule-args alignment requirement (SR-DSL-5 design constraint)

Step (5)'s bridge `rule.memberCell scope X = RawTerm.mkGen generator () X` holds DEFINITIONALLY exactly when the
row's emitted cell spine equals the rule's `args` order — i.e. `<row>Cell` lays its `childCons` spine out in the
SAME order the `memberCell` match binds them.  This holds for the FOUR cell-spine-aligned rows shipped here —
`fst` (`fstCell pairTerm`), `snd`, `app` (`appCell function argument`), `pathApp` — whose `args` ARE the cell
spine, so the gate's `childrenBefore` IS `args` and the args-ordered `*ObligationsDriftUnderArgStep` / output-drift
families apply directly.

The SEVEN dependent rows (`boolElim` / `optionMatch` / `eitherMatch` / `listElim` / `natElim` / `natRec` / `idJ`)
PERMUTE: e.g. `boolElimCell motive scrutinee thenBranch elseBranch` emits the spine `(motive, thenBranch,
elseBranch, scrutinee)` — scrutinee moves from `args` position 1 to spine position 3.  There the gate's
`childrenBefore` is the cell SPINE, not `args`, so `memberCell scope X ≠ mkGen generator () X` and the args-ordered
drift families do not match the spine-ordered `childStep`.  Those rows need a spine-aligned rebuild (cases the spine
`StepChildren` per position → identify the stepped `args` position → args-ordered obligation drift at the unpermuted
`argsAfter`), which the per-position bespoke congruence lemmas already implement; the dependent-row gate branches are
the follow-up.

## Zero-axiom

`HasTypeUnion.classifierIsType` + the row drift lemma + `elimGateRowReassemble` + the `mkGen` injection recipe
(`injection` / `eq_of_heq` / `subst`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The `fst` branch of the eliminator-congruence gate.**  A stepped `fst` cell re-types at its (param) output
type, `Conv`-equal to the original.  The pair obligation's classifier (`productTypeCell firstType secondType`) is
formed via `classifierIsType` over `WfContextUnion`; the self-certifying `firstType : universeCode` obligation gives
the second formedness directly via `universeFormation`; the output `firstType` is a param, so the output drift is
`Conv.refl`. -/
theorem fstElimGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren fstElimRule.argShifts scope) (params : RawTermChildren fstElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ fstElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
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
    have pairClassifierFormed : UnionClassifierIsType profile context
        (productTypeCell firstType secondType) :=
      HasTypeUnion.classifierIsType pairTyped wellFormed
    have firstTypeClassifierFormed : UnionClassifierIsType profile context (universeCodeCell level0 flag) :=
      ⟨_, _, HasTypeUnion.universeFormation context level0 flag⟩
    have memberAfterEq : fstElimRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_fst () childrenAfter := by
      cases childrenAfter with
      | childCons headAfter restAfter => cases restAfter; rfl
    rw [← memberAfterEq]
    exact elimGateRowReassemble .gen_fst fstElimRule
      (.childCons firstType (.childCons secondType .childNil)) level0 level1 flag rfl premisesHold
      childSubjectReduction
      (fstObligationsDriftUnderArgStep level0 level1 flag pairClassifierFormed firstTypeClassifierFormed childStep)
      (Conv.refl _)

/-- **The `snd` branch** — the `fst` twin at the second projection (output `secondType`, a param). -/
theorem sndElimGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren sndElimRule.argShifts scope) (params : RawTermChildren sndElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ sndElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
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
    have pairClassifierFormed : UnionClassifierIsType profile context
        (productTypeCell firstType secondType) :=
      HasTypeUnion.classifierIsType pairTyped wellFormed
    have secondTypeClassifierFormed : UnionClassifierIsType profile context (universeCodeCell level0 flag) :=
      ⟨_, _, HasTypeUnion.universeFormation context level0 flag⟩
    have memberAfterEq : sndElimRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_snd () childrenAfter := by
      cases childrenAfter with
      | childCons headAfter restAfter => cases restAfter; rfl
    rw [← memberAfterEq]
    exact elimGateRowReassemble .gen_snd sndElimRule
      (.childCons firstType (.childCons secondType .childNil)) level0 level1 flag rfl premisesHold
      childSubjectReduction
      (sndObligationsDriftUnderArgStep level0 level1 flag pairClassifierFormed secondTypeClassifierFormed childStep)
      (Conv.refl _)

/-- **The `app` branch** — the mixed-output row: output `subst0 codomainCode argument` drifts when the `argument`
child steps (`appOutputTypeDriftUnderArgStep`); a function step leaves it fixed.  Both obligation classifiers
(`piTyCode` / `domainCode`) are formed via `classifierIsType` over the well-formed context. -/
theorem appElimGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren appElimRule.argShifts scope) (params : RawTermChildren appElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ appElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
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
    rw [← memberAfterEq]
    exact elimGateRowReassemble .gen_app appElimRule
      (.childCons domainCode (.childCons codomainCode .childNil)) level0 level1 flag rfl premisesHold
      childSubjectReduction
      (appObligationsDriftUnderArgStep level0 level1 flag functionClassifierFormed argumentClassifierFormed childStep)
      (appOutputTypeDriftUnderArgStep function domainCode codomainCode childStep)

/-- **The `pathApp` branch** — output `carrierCode`, a param (`Conv.refl`).  Path / interval-argument obligations
formed via `classifierIsType`; the self-certifying carrier obligation via `universeFormation`. -/
theorem pathAppElimGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren pathAppElimRule.argShifts scope)
    (params : RawTermChildren pathAppElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ pathAppElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
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
    rw [← memberAfterEq]
    exact elimGateRowReassemble .gen_pathApp pathAppElimRule
      (.childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))
      level0 level1 flag rfl premisesHold childSubjectReduction
      (pathAppObligationsDriftUnderArgStep level0 level1 flag pathClassifierFormed argumentClassifierFormed
        carrierClassifierFormed childStep)
      (Conv.refl _)

end FX1Poly.Typed
