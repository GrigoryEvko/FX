import FX1Poly.Typed.Metatheory.SubjectReduction.ElimGateReassemble
import FX1Poly.Typed.Metatheory.SubjectReduction.CleanElimObligationsDrift
import FX1Poly.Typed.Metatheory.SubjectReduction.DependentElimObligationsDrift
import FX1Poly.Typed.Metatheory.SubjectReduction.RecursorElimObligationsDrift
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
SAME order the `memberCell` match binds them.  This holds for NINE of the eleven rows:

  * the four base rows — `fst` (`fstCell pairTerm`), `snd`, `app` (`appCell function argument`), `pathApp`; and
  * the five dependent rows whose scrutinee/witness is LAST in BOTH `args` and spine — `optionMatch`
    (`optionMatchCell motive none some scrutinee`), `eitherMatch`, `natElim` (`natElimCell motive zeroBranch
    succBranch scrutinee`), `natRec`, `idJ` (`idJCell motive baseCase witness`).

For those nine the gate's `childrenBefore` IS `args`, so the `mkGen` bridge `cases childrenAfter …; rfl` discharges
and the args-ordered `*ObligationsDriftUnderArgStep` / output-drift families apply with the gate's `childStep`
passed directly.

The TWO permuting rows — `boolElim` and `listElim` — put scrutinee at `args` position 1 but emit it LAST in the
cell spine: `boolElimCell motive scrutinee thenBranch elseBranch` emits `(motive, thenBranch, elseBranch,
scrutinee)`; `listElimCell motive scrutinee nilBranch consBranch` emits `(motive, nilBranch, consBranch,
scrutinee)`.  There the gate's `childrenBefore` is the cell SPINE, not `args`, so `memberCell scope X ≠ mkGen
generator () X`.  Those two use a spine-aligned rebuild: case the spine `StepChildren` per position, identify which
`args` position stepped (the fixed permutation `spine0↦args0`, `spine1↦args2`, `spine2↦args3`, `spine3↦args1`), feed
the args-ordered obligation / output drift at the reindexed `StepChildren`, and let `elimGateRowReassemble`'s
`memberCell scope argsAfter` conclusion unify with the goal's stepped spine by `isDefEq`.

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

/-- **The `boolElim` branch (cell-spine-aligned via per-position reindexing).**  `boolElimCell` emits the spine
`(motive, thenBranch, elseBranch, scrutinee)`, so the gate's `childrenBefore` is that spine and `childStep` steps
it.  We `cases` the spine step into its four positions and, per position, construct the corresponding `args`-order
`StepChildren` (motive at `args` 0, scrutinee at `args` 1, then at `args` 2, else at `args` 3) to feed the
args-ordered `boolElimObligationsDriftUnderArgStep` / `boolElimOutputTypeDriftUnderArgStep`.  `elimGateRowReassemble`
rebuilds at `memberCell scope argsAfter`, which is DEFINITIONALLY `mkGen gen_boolElim () childrenAfter` (the
permutation `memberCell` applies to `argsAfter` reproduces the stepped spine), so `exact` closes the gate goal by
`isDefEq` — no explicit `mkGen` bridge.  The three branch-classifier formedness witnesses come from the scrutinee /
then / else obligations via `classifierIsType`; the motive obligation's universe formedness is the drift lemma's
internal `universeFormation`. -/
theorem boolElimGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren boolElimRule.argShifts scope)
    (params : RawTermChildren boolElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ boolElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
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
    cases childStep with
    | here _ motiveStep =>
        exact elimGateRowReassemble .gen_boolElim boolElimRule .childNil level0 level1 flag rfl premisesHold
          childSubjectReduction
          (boolElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
            thenBranchClassifierFormed elseBranchClassifierFormed (StepChildren.here _ motiveStep))
          (boolElimOutputTypeDriftUnderArgStep .childNil (StepChildren.here _ motiveStep))
    | there _ tail1 => cases tail1 with
      | here _ thenStep =>
          exact elimGateRowReassemble .gen_boolElim boolElimRule .childNil level0 level1 flag rfl premisesHold
            childSubjectReduction
            (boolElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
              thenBranchClassifierFormed elseBranchClassifierFormed
              (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ thenStep))))
            (boolElimOutputTypeDriftUnderArgStep .childNil
              (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ thenStep))))
      | there _ tail2 => cases tail2 with
        | here _ elseStep =>
            exact elimGateRowReassemble .gen_boolElim boolElimRule .childNil level0 level1 flag rfl premisesHold
              childSubjectReduction
              (boolElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
                thenBranchClassifierFormed elseBranchClassifierFormed
                (StepChildren.there _ (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ elseStep)))))
              (boolElimOutputTypeDriftUnderArgStep .childNil
                (StepChildren.there _ (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ elseStep)))))
        | there _ tail3 => cases tail3 with
          | here _ scrutineeStep =>
              exact elimGateRowReassemble .gen_boolElim boolElimRule .childNil level0 level1 flag rfl premisesHold
                childSubjectReduction
                (boolElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
                  thenBranchClassifierFormed elseBranchClassifierFormed
                  (StepChildren.there _ (StepChildren.here _ scrutineeStep)))
                (boolElimOutputTypeDriftUnderArgStep .childNil
                  (StepChildren.there _ (StepChildren.here _ scrutineeStep)))
          | there _ emptyTailStep => cases emptyTailStep

/-- **The `optionMatch` branch** — CELL-SPINE-ALIGNED (`optionMatchCell` emits `(motive, none, some, scrutinee)` =
the rule `args`), so the gate `mkGen` bridge holds definitionally and the args-ordered drift / output-drift apply
directly.  Formedness from the scrutinee / none / some obligations. -/
theorem optionMatchGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren optionMatchElimRule.argShifts scope)
    (params : RawTermChildren optionMatchElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ optionMatchElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : optionMatchElimRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (optionMatchElimRule.outputType scope args params) := by
  match args, params with
  | .childCons motive (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))),
    .childCons typeParamA (.childCons typeParamB .childNil) =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have scrutineeClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.head _)) wellFormed
    have noneBranchClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.tail _ (List.Mem.head _))) wellFormed
    have someBranchClassifierFormed :=
      HasTypeUnion.classifierIsType
        (premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) wellFormed
    have memberAfterEq : optionMatchElimRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_optionMatch () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest1 => cases rest1 with
        | childCons _ rest2 => cases rest2 with
          | childCons _ rest3 => cases rest3 with
            | childCons _ rest4 => cases rest4; rfl
    rw [← memberAfterEq]
    exact elimGateRowReassemble .gen_optionMatch optionMatchElimRule
      (.childCons typeParamA (.childCons typeParamB .childNil)) level0 level1 flag rfl premisesHold
      childSubjectReduction
      (optionMatchObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
        noneBranchClassifierFormed someBranchClassifierFormed childStep)
      (optionMatchOutputTypeDriftUnderArgStep (.childCons typeParamA (.childCons typeParamB .childNil)) childStep)

/-- **The `eitherMatch` branch** — CELL-SPINE-ALIGNED (`eitherMatchCell` emits `(motive, left, right, scrutinee)` =
`args`).  Formedness from the scrutinee / left / right obligations. -/
theorem eitherMatchGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren eitherMatchElimRule.argShifts scope)
    (params : RawTermChildren eitherMatchElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ eitherMatchElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : eitherMatchElimRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (eitherMatchElimRule.outputType scope args params) := by
  match args, params with
  | .childCons motive (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))),
    .childCons typeParamA (.childCons typeParamB .childNil) =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have scrutineeClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.head _)) wellFormed
    have leftBranchClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.tail _ (List.Mem.head _))) wellFormed
    have rightBranchClassifierFormed :=
      HasTypeUnion.classifierIsType
        (premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) wellFormed
    have memberAfterEq : eitherMatchElimRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_eitherMatch () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest1 => cases rest1 with
        | childCons _ rest2 => cases rest2 with
          | childCons _ rest3 => cases rest3 with
            | childCons _ rest4 => cases rest4; rfl
    rw [← memberAfterEq]
    exact elimGateRowReassemble .gen_eitherMatch eitherMatchElimRule
      (.childCons typeParamA (.childCons typeParamB .childNil)) level0 level1 flag rfl premisesHold
      childSubjectReduction
      (eitherMatchObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
        leftBranchClassifierFormed rightBranchClassifierFormed childStep)
      (eitherMatchOutputTypeDriftUnderArgStep (.childCons typeParamA (.childCons typeParamB .childNil)) childStep)

/-- **The `natElim` branch** — CELL-SPINE-ALIGNED (`natElimCell` emits `(motive, zero, succ, scrutinee)` = `args`).
The binder-extended succ-branch obligation's formedness comes NOT from `classifierIsType` (its context is the
2-extended `(context.cons natType).cons motive`, whose well-formedness the gate does not carry) but from the motive
typing via `natElimDependentSuccBranchType_formed_ofMotive` — the same route the drift lemma uses internally. -/
theorem natElimGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren natElimRule.argShifts scope) (params : RawTermChildren natElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ natElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
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
    rw [← memberAfterEq]
    exact elimGateRowReassemble .gen_natElim natElimRule .childNil level0 level1 flag rfl premisesHold
      childSubjectReduction
      (natElimObligationsDriftUnderArgStep level0 level1 flag motiveTyped scrutineeClassifierFormed
        baseBranchClassifierFormed stepBranchClassifierFormed childSubjectReduction childStep)
      (natElimOutputTypeDriftUnderArgStep .childNil childStep)

/-- **The `natRec` branch** — the `natElim` twin (same substrate; only `natRecRule` / `natRecCell` differ). -/
theorem natRecGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren natRecElimRule.argShifts scope) (params : RawTermChildren natRecElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ natRecElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
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
    rw [← memberAfterEq]
    exact elimGateRowReassemble .gen_natRec natRecElimRule .childNil level0 level1 flag rfl premisesHold
      childSubjectReduction
      (natRecElimObligationsDriftUnderArgStep level0 level1 flag motiveTyped scrutineeClassifierFormed
        baseBranchClassifierFormed stepBranchClassifierFormed childSubjectReduction childStep)
      (natRecOutputTypeDriftUnderArgStep .childNil childStep)

/-- **The `idJ` branch** — CELL-SPINE-ALIGNED (`idJCell` emits `(motive, baseCase, witness)` = `args`).  Output
`idJMotiveAt motive rightEndpoint witness`; formedness from the witness / rightEndpoint / baseCase obligations. -/
theorem idJGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren idJElimRule.argShifts scope) (params : RawTermChildren idJElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ idJElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : idJElimRule.memberCell scope args = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (idJElimRule.outputType scope args params) := by
  match args, params with
  | .childCons motive (.childCons baseCase (.childCons witness .childNil)),
    .childCons typeCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)) =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have witnessClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.head _)) wellFormed
    have rightEndpointClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.tail _ (List.Mem.head _))) wellFormed
    have baseCaseClassifierFormed :=
      HasTypeUnion.classifierIsType
        (premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) wellFormed
    have memberAfterEq : idJElimRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_idJ () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest1 => cases rest1 with
        | childCons _ rest2 => cases rest2 with
          | childCons _ rest3 => cases rest3; rfl
    rw [← memberAfterEq]
    exact elimGateRowReassemble .gen_idJ idJElimRule
      (.childCons typeCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))
      level0 level1 flag rfl premisesHold childSubjectReduction
      (idJObligationsDriftUnderArgStep level0 level1 flag witnessClassifierFormed rightEndpointClassifierFormed
        baseCaseClassifierFormed childStep)
      (idJOutputTypeDriftUnderArgStep typeCode leftEndpoint rightEndpoint childStep)

/-- **The `listElim` branch** — CELL-SPINE-PERMUTING (the `boolElim` twin).  `listElimCell motive scrutinee
nilBranch consBranch` emits the spine `(motive, nilBranch, consBranch, scrutinee)` — scrutinee moves from `args`
position 1 to spine position 3.  So the gate's `childStep` is over the cell SPINE, not `args`, and we cannot use
the direct `mkGen` bridge.  Instead we case the spine `StepChildren` per position, identify which `args` position
stepped (the fixed permutation `spine0↦args0`, `spine1↦args2`, `spine2↦args3`, `spine3↦args1`), and feed the
args-ordered obligation / output drift at the reindexed `StepChildren`; `elimGateRowReassemble`'s `memberCell scope
argsAfter` conclusion then unifies with the goal's stepped spine by `isDefEq` (`memberCell` whnf-permutes argsAfter
into the concrete stepped spine).  The cons-branch formedness comes from the base-context obligation
(`listElimDependentConsBranchType motive elementType`), so — unlike the recursors — no `motiveTyped` is needed. -/
theorem listElimGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren listElimRule.argShifts scope)
    (params : RawTermChildren listElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ listElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : listElimRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (listElimRule.outputType scope args params) := by
  match args, params with
  | .childCons motive (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil))),
    .childCons elementType (.childCons resultType .childNil) =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have scrutineeClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.head _)) wellFormed
    have nilBranchClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.tail _ (List.Mem.head _))) wellFormed
    have consBranchClassifierFormed :=
      HasTypeUnion.classifierIsType
        (premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) wellFormed
    cases childStep with
    | here _ motiveStep =>
        exact elimGateRowReassemble .gen_listElim listElimRule
          (.childCons elementType (.childCons resultType .childNil)) level0 level1 flag rfl premisesHold
          childSubjectReduction
          (listElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
            nilBranchClassifierFormed consBranchClassifierFormed (StepChildren.here _ motiveStep))
          (listElimOutputTypeDriftUnderArgStep (.childCons elementType (.childCons resultType .childNil))
            (StepChildren.here _ motiveStep))
    | there _ tail1 => cases tail1 with
      | here _ nilStep =>
          exact elimGateRowReassemble .gen_listElim listElimRule
            (.childCons elementType (.childCons resultType .childNil)) level0 level1 flag rfl premisesHold
            childSubjectReduction
            (listElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
              nilBranchClassifierFormed consBranchClassifierFormed
              (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ nilStep))))
            (listElimOutputTypeDriftUnderArgStep (.childCons elementType (.childCons resultType .childNil))
              (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ nilStep))))
      | there _ tail2 => cases tail2 with
        | here _ consStep =>
            exact elimGateRowReassemble .gen_listElim listElimRule
              (.childCons elementType (.childCons resultType .childNil)) level0 level1 flag rfl premisesHold
              childSubjectReduction
              (listElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
                nilBranchClassifierFormed consBranchClassifierFormed
                (StepChildren.there _ (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ consStep)))))
              (listElimOutputTypeDriftUnderArgStep (.childCons elementType (.childCons resultType .childNil))
                (StepChildren.there _ (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ consStep)))))
        | there _ tail3 => cases tail3 with
          | here _ scrutineeStep =>
              exact elimGateRowReassemble .gen_listElim listElimRule
                (.childCons elementType (.childCons resultType .childNil)) level0 level1 flag rfl premisesHold
                childSubjectReduction
                (listElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
                  nilBranchClassifierFormed consBranchClassifierFormed
                  (StepChildren.there _ (StepChildren.here _ scrutineeStep)))
                (listElimOutputTypeDriftUnderArgStep (.childCons elementType (.childCons resultType .childNil))
                  (StepChildren.there _ (StepChildren.here _ scrutineeStep)))
          | there _ emptyTailStep => cases emptyTailStep

end FX1Poly.Typed
