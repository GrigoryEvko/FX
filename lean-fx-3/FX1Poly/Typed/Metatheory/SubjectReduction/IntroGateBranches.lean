import FX1Poly.Typed.Metatheory.SubjectReduction.IntroGateReassemble
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/IntroGateBranches
    — SR-DSL-5: the per-generator branches of the INTRODUCER-congruence gate (the `Conv`-refl-output rows)

`UnionIntroCongruenceCloses` (HasTypeUnionCongruenceClosesGeneric.lean) dispatches on the introducer generator.
This file ships the per-generator BRANCH lemmas for the rows whose output type is param-determined (so the output
drift is `Conv.refl`), in two shapes:

  * **The eight nullary data constructors** (`boolTrue` / `boolFalse` / `unit` / `interval0` / `interval1` /
    `natZero` / `optionNone` / `listNil`) — their `memberCell` IGNORES `args` (a constant `mkGen genX () childNil`),
    so the gate's `childrenBefore` is `childNil` and the `childStep : StepChildren childNil _` is VACUOUS.  The proof
    is uniform: inject the `mkGen` equation, then `cases childStep` (no constructor steps an empty child vector).

  * **The six recursive / grown data constructors** (`natSucc` / `optionSome` / `eitherInl` / `eitherInr` / `pair` /
    `listCons`) — their `memberCell` IS the cell spine (`pairCell a b = mkGen gen_pair () [a, b]`, etc.), so the
    gate's `childStep` steps one arg.  We `cases childStep` per arg position, build the `ObligationsDrift` (the
    stepped arg's obligation gets `StepStar.single`; the other obligations — params and non-stepped args — get
    `StepStar.refl`, since the classifiers are arg-free), and hand it with `sideHoldsAfter := trivial` (the data
    rows' `sideCondition` is `True`) and `outputDrift := Conv.refl` to the generic `introGateRowReassemble`.  Its
    `memberCell scope argsAfter` conclusion unifies with the goal's stepped spine by `isDefEq`.

The two output-DRIFTING rows (`refl`, whose `idType` output reads the stepping witness; `lam`, whose domain step
drifts the codomain / body obligation contexts) are the follow-up; the affine `pathLam` row is blocked by the
interval-fibrancy obstruction (the staged interval-non-fibrant arc).

## Zero-axiom

`HasTypeUnion.classifierIsType` / `.universeFormation` + `StepStar.single` / `.refl` + the `ObligationsDrift`
constructors + `introGateRowReassemble` + the `mkGen` injection recipe.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## The eight nullary data constructors — vacuous `childStep` (constant `mkGen genX () childNil`) -/

/-- **The `boolTrue` branch** — nullary; `memberCell` is the constant `mkGen gen_boolTrue () childNil`, so the
gate's `childStep` steps an empty child vector and is vacuous. -/
theorem boolTrueIntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren boolTrueIntroRule.argShifts scope)
    (params : RawTermChildren boolTrueIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ boolTrueIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : boolTrueIntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (boolTrueIntroRule.outputType scope args params) := by
  injection memberEq with _scopeEq genEq payloadEq childrenEq
  subst genEq
  cases eq_of_heq payloadEq
  cases eq_of_heq childrenEq
  cases childStep

/-- **The `boolFalse` branch** — nullary; vacuous `childStep`. -/
theorem boolFalseIntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren boolFalseIntroRule.argShifts scope)
    (params : RawTermChildren boolFalseIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ boolFalseIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : boolFalseIntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (boolFalseIntroRule.outputType scope args params) := by
  injection memberEq with _scopeEq genEq payloadEq childrenEq
  subst genEq
  cases eq_of_heq payloadEq
  cases eq_of_heq childrenEq
  cases childStep

/-- **The `unit` branch** — nullary; vacuous `childStep`. -/
theorem unitIntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren unitIntroRule.argShifts scope)
    (params : RawTermChildren unitIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ unitIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : unitIntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (unitIntroRule.outputType scope args params) := by
  injection memberEq with _scopeEq genEq payloadEq childrenEq
  subst genEq
  cases eq_of_heq payloadEq
  cases eq_of_heq childrenEq
  cases childStep

/-- **The `interval0` branch** — nullary; vacuous `childStep`. -/
theorem interval0IntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren interval0IntroRule.argShifts scope)
    (params : RawTermChildren interval0IntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ interval0IntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : interval0IntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (interval0IntroRule.outputType scope args params) := by
  injection memberEq with _scopeEq genEq payloadEq childrenEq
  subst genEq
  cases eq_of_heq payloadEq
  cases eq_of_heq childrenEq
  cases childStep

/-- **The `interval1` branch** — nullary; vacuous `childStep`. -/
theorem interval1IntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren interval1IntroRule.argShifts scope)
    (params : RawTermChildren interval1IntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ interval1IntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : interval1IntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (interval1IntroRule.outputType scope args params) := by
  injection memberEq with _scopeEq genEq payloadEq childrenEq
  subst genEq
  cases eq_of_heq payloadEq
  cases eq_of_heq childrenEq
  cases childStep

/-- **The `natZero` branch** — nullary; vacuous `childStep`. -/
theorem natZeroIntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren natZeroIntroRule.argShifts scope)
    (params : RawTermChildren natZeroIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ natZeroIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : natZeroIntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (natZeroIntroRule.outputType scope args params) := by
  injection memberEq with _scopeEq genEq payloadEq childrenEq
  subst genEq
  cases eq_of_heq payloadEq
  cases eq_of_heq childrenEq
  cases childStep

/-- **The `optionNone` branch** — nullary in `args` (the free type is a `param`); vacuous `childStep`. -/
theorem optionNoneIntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren optionNoneIntroRule.argShifts scope)
    (params : RawTermChildren optionNoneIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ optionNoneIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : optionNoneIntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (optionNoneIntroRule.outputType scope args params) := by
  injection memberEq with _scopeEq genEq payloadEq childrenEq
  subst genEq
  cases eq_of_heq payloadEq
  cases eq_of_heq childrenEq
  cases childStep

/-- **The `listNil` branch** — nullary in `args` (the free type is a `param`); vacuous `childStep`. -/
theorem listNilIntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren listNilIntroRule.argShifts scope)
    (params : RawTermChildren listNilIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ listNilIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : listNilIntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (listNilIntroRule.outputType scope args params) := by
  injection memberEq with _scopeEq genEq payloadEq childrenEq
  subst genEq
  cases eq_of_heq payloadEq
  cases eq_of_heq childrenEq
  cases childStep

/-! ## The recursive / grown data constructors — one arg steps, `Conv.refl` output

Each branch builds `driftAt : ObligationsDrift (obligations args) (obligations childrenAfter)` with `childrenAfter`
the gate's symbolic variable (cased internally), bridges the goal's `mkGen genX () childrenAfter` to
`memberCell scope childrenAfter` via `memberAfterEq`, and hands `driftAt` to `introGateRowReassemble` so the
`argsAfter` implicit unifies symbolically (`argsAfter := childrenAfter`) — never an `obligations`-inversion. -/

/-- **The `natSucc` branch** — one union-recursive child at `Nat`; when it steps, its sole obligation drifts
(`StepStar.single`), output `natType` is constant (`Conv.refl`). -/
theorem natSuccIntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren natSuccIntroRule.argShifts scope)
    (params : RawTermChildren natSuccIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ natSuccIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : natSuccIntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (natSuccIntroRule.outputType scope args params) := by
  match args, params with
  | .childCons child .childNil, .childNil =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have natFormed : UnionClassifierIsType profile context natTypeCell :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.head _)) wellFormed
    have driftAt : ObligationsDrift profile
        (natSuccIntroRule.obligations scope context (.childCons child .childNil) .childNil level0 level1 flag)
        (natSuccIntroRule.obligations scope context childrenAfter .childNil level0 level1 flag) := by
      cases childStep with
      | here _ childStepHead =>
          exact .cons (StepStar.single childStepHead) (StepStar.refl _) natFormed .nil
      | there _ restStep => cases restStep
    have memberAfterEq : natSuccIntroRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_natSucc () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest => cases rest; rfl
    rw [← memberAfterEq]
    exact introGateRowReassemble .gen_natSucc natSuccIntroRule .childNil level0 level1 flag
      introRuleOf_natSucc premisesHold childSubjectReduction trivial driftAt (Conv.refl _)

/-- **The `optionSome` branch** — one grown child at the type `param`; when it steps, its sole obligation drifts,
output `option(param)` is param-determined (`Conv.refl`). -/
theorem optionSomeIntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren optionSomeIntroRule.argShifts scope)
    (params : RawTermChildren optionSomeIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ optionSomeIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : optionSomeIntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (optionSomeIntroRule.outputType scope args params) := by
  match args, params with
  | .childCons value .childNil, .childCons typeParam0 .childNil =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have tp0Formed : UnionClassifierIsType profile context typeParam0 :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.head _)) wellFormed
    have driftAt : ObligationsDrift profile
        (optionSomeIntroRule.obligations scope context (.childCons value .childNil)
          (.childCons typeParam0 .childNil) level0 level1 flag)
        (optionSomeIntroRule.obligations scope context childrenAfter
          (.childCons typeParam0 .childNil) level0 level1 flag) := by
      cases childStep with
      | here _ valueStep =>
          exact .cons (StepStar.single valueStep) (StepStar.refl _) tp0Formed .nil
      | there _ restStep => cases restStep
    have memberAfterEq : optionSomeIntroRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_optionSome () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest => cases rest; rfl
    rw [← memberAfterEq]
    exact introGateRowReassemble .gen_optionSome optionSomeIntroRule
      (.childCons typeParam0 .childNil) level0 level1 flag introRuleOf_optionSome premisesHold
      childSubjectReduction trivial driftAt (Conv.refl _)

/-- **The `eitherInl` branch** — one grown value at the LEFT type; the two type-`param` formedness obligations are
unchanged when the value steps, output `either(param0, param1)` param-determined (`Conv.refl`). -/
theorem eitherInlIntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren eitherInlIntroRule.argShifts scope)
    (params : RawTermChildren eitherInlIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ eitherInlIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : eitherInlIntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (eitherInlIntroRule.outputType scope args params) := by
  match args, params with
  | .childCons value .childNil, .childCons typeParam0 (.childCons typeParam1 .childNil) =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have tp0Formed : UnionClassifierIsType profile context typeParam0 :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.head _)) wellFormed
    have univ0Formed : UnionClassifierIsType profile context (universeCodeCell level0 flag) :=
      ⟨_, _, HasTypeUnion.universeFormation context level0 flag⟩
    have univ1Formed : UnionClassifierIsType profile context (universeCodeCell level1 flag) :=
      ⟨_, _, HasTypeUnion.universeFormation context level1 flag⟩
    have driftAt : ObligationsDrift profile
        (eitherInlIntroRule.obligations scope context (.childCons value .childNil)
          (.childCons typeParam0 (.childCons typeParam1 .childNil)) level0 level1 flag)
        (eitherInlIntroRule.obligations scope context childrenAfter
          (.childCons typeParam0 (.childCons typeParam1 .childNil)) level0 level1 flag) := by
      cases childStep with
      | here _ valueStep =>
          exact .cons (StepStar.single valueStep) (StepStar.refl _) tp0Formed
            (.cons (StepStar.refl _) (StepStar.refl _) univ0Formed
              (.cons (StepStar.refl _) (StepStar.refl _) univ1Formed .nil))
      | there _ restStep => cases restStep
    have memberAfterEq : eitherInlIntroRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_eitherInl () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest => cases rest; rfl
    rw [← memberAfterEq]
    exact introGateRowReassemble .gen_eitherInl eitherInlIntroRule
      (.childCons typeParam0 (.childCons typeParam1 .childNil)) level0 level1 flag introRuleOf_eitherInl
      premisesHold childSubjectReduction trivial driftAt (Conv.refl _)

/-- **The `eitherInr` branch** — the `eitherInl` twin (value at the RIGHT type, output puts the free side first);
same one-arg drift. -/
theorem eitherInrIntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren eitherInrIntroRule.argShifts scope)
    (params : RawTermChildren eitherInrIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ eitherInrIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : eitherInrIntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (eitherInrIntroRule.outputType scope args params) := by
  match args, params with
  | .childCons value .childNil, .childCons typeParam0 (.childCons typeParam1 .childNil) =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have tp0Formed : UnionClassifierIsType profile context typeParam0 :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.head _)) wellFormed
    have univ0Formed : UnionClassifierIsType profile context (universeCodeCell level0 flag) :=
      ⟨_, _, HasTypeUnion.universeFormation context level0 flag⟩
    have univ1Formed : UnionClassifierIsType profile context (universeCodeCell level1 flag) :=
      ⟨_, _, HasTypeUnion.universeFormation context level1 flag⟩
    have driftAt : ObligationsDrift profile
        (eitherInrIntroRule.obligations scope context (.childCons value .childNil)
          (.childCons typeParam0 (.childCons typeParam1 .childNil)) level0 level1 flag)
        (eitherInrIntroRule.obligations scope context childrenAfter
          (.childCons typeParam0 (.childCons typeParam1 .childNil)) level0 level1 flag) := by
      cases childStep with
      | here _ valueStep =>
          exact .cons (StepStar.single valueStep) (StepStar.refl _) tp0Formed
            (.cons (StepStar.refl _) (StepStar.refl _) univ0Formed
              (.cons (StepStar.refl _) (StepStar.refl _) univ1Formed .nil))
      | there _ restStep => cases restStep
    have memberAfterEq : eitherInrIntroRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_eitherInr () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest => cases rest; rfl
    rw [← memberAfterEq]
    exact introGateRowReassemble .gen_eitherInr eitherInrIntroRule
      (.childCons typeParam0 (.childCons typeParam1 .childNil)) level0 level1 flag introRuleOf_eitherInr
      premisesHold childSubjectReduction trivial driftAt (Conv.refl _)

/-- **The `pair` branch** — two grown children at the two type `param`s plus two formedness obligations; either
child can step (cases the two `args` positions), the other obligations stay `refl`, output `product(param0, param1)`
param-determined (`Conv.refl`). -/
theorem pairIntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren pairIntroRule.argShifts scope)
    (params : RawTermChildren pairIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ pairIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : pairIntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (pairIntroRule.outputType scope args params) := by
  match args, params with
  | .childCons child0 (.childCons child1 .childNil), .childCons typeParam0 (.childCons typeParam1 .childNil) =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have tp0Formed : UnionClassifierIsType profile context typeParam0 :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.head _)) wellFormed
    have tp1Formed : UnionClassifierIsType profile context typeParam1 :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.tail _ (List.Mem.head _))) wellFormed
    have univ0Formed : UnionClassifierIsType profile context (universeCodeCell level0 flag) :=
      ⟨_, _, HasTypeUnion.universeFormation context level0 flag⟩
    have univ1Formed : UnionClassifierIsType profile context (universeCodeCell level1 flag) :=
      ⟨_, _, HasTypeUnion.universeFormation context level1 flag⟩
    have driftAt : ObligationsDrift profile
        (pairIntroRule.obligations scope context (.childCons child0 (.childCons child1 .childNil))
          (.childCons typeParam0 (.childCons typeParam1 .childNil)) level0 level1 flag)
        (pairIntroRule.obligations scope context childrenAfter
          (.childCons typeParam0 (.childCons typeParam1 .childNil)) level0 level1 flag) := by
      cases childStep with
      | here _ child0Step =>
          exact .cons (StepStar.single child0Step) (StepStar.refl _) tp0Formed
            (.cons (StepStar.refl _) (StepStar.refl _) tp1Formed
              (.cons (StepStar.refl _) (StepStar.refl _) univ0Formed
                (.cons (StepStar.refl _) (StepStar.refl _) univ1Formed .nil)))
      | there _ tail1 => cases tail1 with
        | here _ child1Step =>
            exact .cons (StepStar.refl _) (StepStar.refl _) tp0Formed
              (.cons (StepStar.single child1Step) (StepStar.refl _) tp1Formed
                (.cons (StepStar.refl _) (StepStar.refl _) univ0Formed
                  (.cons (StepStar.refl _) (StepStar.refl _) univ1Formed .nil)))
        | there _ tail2 => cases tail2
    have memberAfterEq : pairIntroRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_pair () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest1 => cases rest1 with
        | childCons _ rest2 => cases rest2; rfl
    rw [← memberAfterEq]
    exact introGateRowReassemble .gen_pair pairIntroRule
      (.childCons typeParam0 (.childCons typeParam1 .childNil)) level0 level1 flag introRuleOf_pair
      premisesHold childSubjectReduction trivial driftAt (Conv.refl _)

/-- **The `listCons` branch** — a grown head at the element type and a union-recursive tail at `List(element)`;
either can step, output `List(element)` param-determined (`Conv.refl`). -/
theorem listConsIntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren listConsIntroRule.argShifts scope)
    (params : RawTermChildren listConsIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ listConsIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : listConsIntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (listConsIntroRule.outputType scope args params) := by
  match args, params with
  | .childCons head (.childCons tail .childNil), .childCons elementType .childNil =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have elemFormed : UnionClassifierIsType profile context elementType :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.head _)) wellFormed
    have listFormed : UnionClassifierIsType profile context (listTypeCell elementType) :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.tail _ (List.Mem.head _))) wellFormed
    have driftAt : ObligationsDrift profile
        (listConsIntroRule.obligations scope context (.childCons head (.childCons tail .childNil))
          (.childCons elementType .childNil) level0 level1 flag)
        (listConsIntroRule.obligations scope context childrenAfter
          (.childCons elementType .childNil) level0 level1 flag) := by
      cases childStep with
      | here _ headStep =>
          exact .cons (StepStar.single headStep) (StepStar.refl _) elemFormed
            (.cons (StepStar.refl _) (StepStar.refl _) listFormed .nil)
      | there _ tail1 => cases tail1 with
        | here _ tailStep =>
            exact .cons (StepStar.refl _) (StepStar.refl _) elemFormed
              (.cons (StepStar.single tailStep) (StepStar.refl _) listFormed .nil)
        | there _ tail2 => cases tail2
    have memberAfterEq : listConsIntroRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_listCons () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest1 => cases rest1 with
        | childCons _ rest2 => cases rest2; rfl
    rw [← memberAfterEq]
    exact introGateRowReassemble .gen_listCons listConsIntroRule
      (.childCons elementType .childNil) level0 level1 flag introRuleOf_listCons premisesHold
      childSubjectReduction trivial driftAt (Conv.refl _)

/-! ## The output-drifting grown constructor — `refl` (the witness flows into the `idType` output) -/

/-- **The `refl` branch** — output `idType(param, witness, witness)` reads the stepping `witness` TWICE, so a witness
step drifts the output: `idType A w w` reduces (both endpoint children of `gen_idCode`) to `idType A w' w'`, giving
`Conv (idType A w' w') (idType A w w)` via a two-step `gen_idCode` congruence chain (left endpoint, then right).
The sole obligation `witness : param` drifts as for `optionSome`. -/
theorem reflIntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren reflIntroRule.argShifts scope)
    (params : RawTermChildren reflIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ reflIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : reflIntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (reflIntroRule.outputType scope args params) := by
  match args, params with
  | .childCons witness .childNil, .childCons typeParam0 .childNil =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have tp0Formed : UnionClassifierIsType profile context typeParam0 :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.head _)) wellFormed
    have driftAt : ObligationsDrift profile
        (reflIntroRule.obligations scope context (.childCons witness .childNil)
          (.childCons typeParam0 .childNil) level0 level1 flag)
        (reflIntroRule.obligations scope context childrenAfter
          (.childCons typeParam0 .childNil) level0 level1 flag) := by
      cases childStep with
      | here _ witnessStep =>
          exact .cons (StepStar.single witnessStep) (StepStar.refl _) tp0Formed .nil
      | there _ restStep => cases restStep
    have outputDriftAt : Conv
        (reflIntroRule.outputType scope childrenAfter (.childCons typeParam0 .childNil))
        (reflIntroRule.outputType scope (.childCons witness .childNil) (.childCons typeParam0 .childNil)) := by
      cases childStep with
      | @here _ _ _ _ witnessPrime _ witnessStep =>
          exact ⟨_, StepStar.refl _,
            StepStar.trans
              (Step.cong .gen_idCode () (.there typeParam0 (.here (.childCons witness .childNil) witnessStep)))
              (StepStar.single (Step.cong .gen_idCode ()
                (.there typeParam0 (.there witnessPrime (.here .childNil witnessStep)))))⟩
      | there _ restStep => cases restStep
    have memberAfterEq : reflIntroRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_refl () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest => cases rest; rfl
    rw [← memberAfterEq]
    exact introGateRowReassemble .gen_refl reflIntroRule
      (.childCons typeParam0 .childNil) level0 level1 flag introRuleOf_refl premisesHold
      childSubjectReduction trivial driftAt outputDriftAt

end FX1Poly.Typed
