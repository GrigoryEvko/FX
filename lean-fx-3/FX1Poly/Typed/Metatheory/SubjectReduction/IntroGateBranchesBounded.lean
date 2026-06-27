import FX1Poly.Typed.Metatheory.SubjectReduction.IntroGateReassembleBounded
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/IntroGateBranchesBounded
    — SR-WF-TIEOFF (intro third): the per-generator branches of the FUEL-BOUNDED introducer-congruence gate

The fuel-bounded twin of `IntroGateBranches.lean`.  Each branch is a near-verbatim mirror of its unbounded
counterpart, with three swaps that thread the fuel-bounded child-SR:

  * the universal `childSubjectReduction : UnionChildSubjectReduction profile` becomes the fuel-bounded
    `childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (ruleX.memberCell scope args).size`
    (the bound the gate `UnionIntroCongruenceClosesBounded` supplies);
  * the drift `ObligationsDrift` becomes `ObligationsDriftBelow profile (ruleX.memberCell scope args).size`, with
    each stepping arg's `.cons (StepStar.single step) (StepStar.refl _) formed` becoming
    `.cons (.stepsBelow step <bound>) formed` (the stepping arg is a structural cell-child, so its size is strictly
    below `(memberCell scope args).size` — `<bound>` is the `headChildBelowSuccSize` / `secondChildBelowSuccSize`
    witness) and each fixed `.cons (StepStar.refl _) (StepStar.refl _) formed` becoming `.cons (.fixed _) formed`;
  * the reassembly `introGateRowReassemble` becomes `introGateRowReassembleBounded`.

The eight nullary branches don't even reach the bounded driver — their `childStep` is vacuous (an empty child
vector cannot step) — so the bounded child-SR is unused and the proof is the same `injection` + `cases childStep`.

The two output-DRIFTING rows (`refl`, `lam`) thread the bound identically; the `lam` domain-step branch uses the
`consContextHeadConv` arm (verbatim from the unbounded driver, no child-SR) for the codomain / body obligation
context drift, and `.stepsBelow` only for the stepping domain itself.  The affine `pathLam` row stays blocked by the
interval-fibrancy obstruction (the staged interval-non-fibrant A1 arc).

## Zero-axiom

`HasTypeUnion.classifierIsType` / `.universeFormation` + `SubjectDriftBelow` / `ObligationsDriftBelow` constructors +
`introGateRowReassembleBounded` + the `RawSize` `size_lt_childCons_*` / `Nat.lt_succ_self` / `Nat.lt_trans` bound
arithmetic + the `mkGen` injection recipe.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## Size helpers — a stepping arg is strictly smaller than its own `mkGen` cell

`(RawTerm.mkGen generator payload children).size` is DEFINITIONALLY `children.size + 1` (the generator / payload are
ignored by `RawTerm.size`), so a bound `child.size < (childCons … child …).size + 1` is defeq to
`child.size < (ruleX.memberCell scope args).size` once `memberCell scope args` reduces to its `mkGen` spine. -/

/-- A head child is strictly below its parent `childCons … + 1` size. -/
private theorem headChildBelowSuccSize {scope firstShift : Nat} {restShifts : List Nat}
    (head : RawTerm (scope + firstShift)) (tail : RawTermChildren restShifts scope) :
    head.size < (RawTermChildren.childCons head tail).size + 1 :=
  Nat.lt_trans (RawTermChildren.size_lt_childCons_head head tail) (Nat.lt_succ_self _)

/-- A second child is strictly below its grandparent `childCons … (childCons … ) + 1` size. -/
private theorem secondChildBelowSuccSize {scope firstShift secondShift : Nat} {restShifts : List Nat}
    (first : RawTerm (scope + firstShift)) (second : RawTerm (scope + secondShift))
    (tail : RawTermChildren restShifts scope) :
    second.size < (RawTermChildren.childCons first (.childCons second tail)).size + 1 :=
  Nat.lt_trans
    (Nat.lt_trans (RawTermChildren.size_lt_childCons_head second tail)
      (RawTermChildren.size_lt_childCons_tail first _))
    (Nat.lt_succ_self _)

/-! ## The eight nullary data constructors — vacuous `childStep` (constant `mkGen genX () childNil`) -/

/-- **The `boolTrue` branch (bounded)** — nullary; vacuous `childStep`. -/
theorem boolTrueIntroGateBranchClosesBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (args : RawTermChildren boolTrueIntroRule.argShifts scope)
    (params : RawTermChildren boolTrueIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ boolTrueIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (_childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (boolTrueIntroRule.memberCell scope args).size)
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

/-- **The `boolFalse` branch (bounded)** — nullary; vacuous `childStep`. -/
theorem boolFalseIntroGateBranchClosesBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (args : RawTermChildren boolFalseIntroRule.argShifts scope)
    (params : RawTermChildren boolFalseIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ boolFalseIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (_childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (boolFalseIntroRule.memberCell scope args).size)
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

/-- **The `unit` branch (bounded)** — nullary; vacuous `childStep`. -/
theorem unitIntroGateBranchClosesBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (args : RawTermChildren unitIntroRule.argShifts scope)
    (params : RawTermChildren unitIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ unitIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (_childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (unitIntroRule.memberCell scope args).size)
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

/-- **The `interval0` branch (bounded)** — nullary; vacuous `childStep`. -/
theorem interval0IntroGateBranchClosesBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (args : RawTermChildren interval0IntroRule.argShifts scope)
    (params : RawTermChildren interval0IntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ interval0IntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (_childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (interval0IntroRule.memberCell scope args).size)
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

/-- **The `interval1` branch (bounded)** — nullary; vacuous `childStep`. -/
theorem interval1IntroGateBranchClosesBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (args : RawTermChildren interval1IntroRule.argShifts scope)
    (params : RawTermChildren interval1IntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ interval1IntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (_childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (interval1IntroRule.memberCell scope args).size)
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

/-- **The `natZero` branch (bounded)** — nullary; vacuous `childStep`. -/
theorem natZeroIntroGateBranchClosesBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (args : RawTermChildren natZeroIntroRule.argShifts scope)
    (params : RawTermChildren natZeroIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ natZeroIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (_childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (natZeroIntroRule.memberCell scope args).size)
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

/-- **The `optionNone` branch (bounded)** — nullary in `args`; vacuous `childStep`. -/
theorem optionNoneIntroGateBranchClosesBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (args : RawTermChildren optionNoneIntroRule.argShifts scope)
    (params : RawTermChildren optionNoneIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ optionNoneIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (_childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (optionNoneIntroRule.memberCell scope args).size)
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

/-- **The `listNil` branch (bounded)** — nullary in `args`; vacuous `childStep`. -/
theorem listNilIntroGateBranchClosesBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (args : RawTermChildren listNilIntroRule.argShifts scope)
    (params : RawTermChildren listNilIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ listNilIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (_childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (listNilIntroRule.memberCell scope args).size)
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

/-! ## The recursive / grown data constructors — one arg steps, `Conv.refl` output -/

/-- **The `natSucc` branch (bounded)** — one union-recursive child at `Nat`; the stepping child is below the cell. -/
theorem natSuccIntroGateBranchClosesBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (args : RawTermChildren natSuccIntroRule.argShifts scope)
    (params : RawTermChildren natSuccIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ natSuccIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (natSuccIntroRule.memberCell scope args).size)
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
    have driftAt : ObligationsDriftBelow profile (natSuccIntroRule.memberCell scope (.childCons child .childNil)).size
        (natSuccIntroRule.obligations scope context (.childCons child .childNil) .childNil level0 level1 flag)
        (natSuccIntroRule.obligations scope context childrenAfter .childNil level0 level1 flag) := by
      cases childStep with
      | here _ childStepHead =>
          exact .cons (.stepsBelow childStepHead (headChildBelowSuccSize child .childNil)) natFormed .nil
      | there _ restStep => cases restStep
    have memberAfterEq : natSuccIntroRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_natSucc () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest => cases rest; rfl
    rw [← memberAfterEq]
    exact introGateRowReassembleBounded .gen_natSucc natSuccIntroRule .childNil level0 level1 flag
      introRuleOf_natSucc premisesHold childSubjectReductionBelow trivial driftAt (Conv.refl _)

/-- **The `optionSome` branch (bounded)** — one grown child at the type `param`. -/
theorem optionSomeIntroGateBranchClosesBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (args : RawTermChildren optionSomeIntroRule.argShifts scope)
    (params : RawTermChildren optionSomeIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ optionSomeIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (optionSomeIntroRule.memberCell scope args).size)
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
    have driftAt : ObligationsDriftBelow profile (optionSomeIntroRule.memberCell scope
        (.childCons value .childNil)).size
        (optionSomeIntroRule.obligations scope context (.childCons value .childNil)
          (.childCons typeParam0 .childNil) level0 level1 flag)
        (optionSomeIntroRule.obligations scope context childrenAfter
          (.childCons typeParam0 .childNil) level0 level1 flag) := by
      cases childStep with
      | here _ valueStep =>
          exact .cons (.stepsBelow valueStep (headChildBelowSuccSize value .childNil)) tp0Formed .nil
      | there _ restStep => cases restStep
    have memberAfterEq : optionSomeIntroRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_optionSome () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest => cases rest; rfl
    rw [← memberAfterEq]
    exact introGateRowReassembleBounded .gen_optionSome optionSomeIntroRule
      (.childCons typeParam0 .childNil) level0 level1 flag introRuleOf_optionSome premisesHold
      childSubjectReductionBelow trivial driftAt (Conv.refl _)

/-- **The `eitherInl` branch (bounded)** — one grown value at the LEFT type; the two type-`param` formedness
obligations are unchanged when the value steps. -/
theorem eitherInlIntroGateBranchClosesBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (args : RawTermChildren eitherInlIntroRule.argShifts scope)
    (params : RawTermChildren eitherInlIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ eitherInlIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (eitherInlIntroRule.memberCell scope args).size)
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
    have driftAt : ObligationsDriftBelow profile (eitherInlIntroRule.memberCell scope
        (.childCons value .childNil)).size
        (eitherInlIntroRule.obligations scope context (.childCons value .childNil)
          (.childCons typeParam0 (.childCons typeParam1 .childNil)) level0 level1 flag)
        (eitherInlIntroRule.obligations scope context childrenAfter
          (.childCons typeParam0 (.childCons typeParam1 .childNil)) level0 level1 flag) := by
      cases childStep with
      | here _ valueStep =>
          exact .cons (.stepsBelow valueStep (headChildBelowSuccSize value .childNil)) tp0Formed
            (.cons (.fixed _) univ0Formed
              (.cons (.fixed _) univ1Formed .nil))
      | there _ restStep => cases restStep
    have memberAfterEq : eitherInlIntroRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_eitherInl () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest => cases rest; rfl
    rw [← memberAfterEq]
    exact introGateRowReassembleBounded .gen_eitherInl eitherInlIntroRule
      (.childCons typeParam0 (.childCons typeParam1 .childNil)) level0 level1 flag introRuleOf_eitherInl
      premisesHold childSubjectReductionBelow trivial driftAt (Conv.refl _)

/-- **The `eitherInr` branch (bounded)** — the `eitherInl` twin (value at the RIGHT type). -/
theorem eitherInrIntroGateBranchClosesBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (args : RawTermChildren eitherInrIntroRule.argShifts scope)
    (params : RawTermChildren eitherInrIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ eitherInrIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (eitherInrIntroRule.memberCell scope args).size)
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
    have driftAt : ObligationsDriftBelow profile (eitherInrIntroRule.memberCell scope
        (.childCons value .childNil)).size
        (eitherInrIntroRule.obligations scope context (.childCons value .childNil)
          (.childCons typeParam0 (.childCons typeParam1 .childNil)) level0 level1 flag)
        (eitherInrIntroRule.obligations scope context childrenAfter
          (.childCons typeParam0 (.childCons typeParam1 .childNil)) level0 level1 flag) := by
      cases childStep with
      | here _ valueStep =>
          exact .cons (.stepsBelow valueStep (headChildBelowSuccSize value .childNil)) tp0Formed
            (.cons (.fixed _) univ0Formed
              (.cons (.fixed _) univ1Formed .nil))
      | there _ restStep => cases restStep
    have memberAfterEq : eitherInrIntroRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_eitherInr () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest => cases rest; rfl
    rw [← memberAfterEq]
    exact introGateRowReassembleBounded .gen_eitherInr eitherInrIntroRule
      (.childCons typeParam0 (.childCons typeParam1 .childNil)) level0 level1 flag introRuleOf_eitherInr
      premisesHold childSubjectReductionBelow trivial driftAt (Conv.refl _)

/-- **The `pair` branch (bounded)** — two grown children at the two type `param`s plus two formedness obligations;
either child can step. -/
theorem pairIntroGateBranchClosesBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (args : RawTermChildren pairIntroRule.argShifts scope)
    (params : RawTermChildren pairIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ pairIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (pairIntroRule.memberCell scope args).size)
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
    have driftAt : ObligationsDriftBelow profile (pairIntroRule.memberCell scope
        (.childCons child0 (.childCons child1 .childNil))).size
        (pairIntroRule.obligations scope context (.childCons child0 (.childCons child1 .childNil))
          (.childCons typeParam0 (.childCons typeParam1 .childNil)) level0 level1 flag)
        (pairIntroRule.obligations scope context childrenAfter
          (.childCons typeParam0 (.childCons typeParam1 .childNil)) level0 level1 flag) := by
      cases childStep with
      | here _ child0Step =>
          exact .cons (.stepsBelow child0Step (headChildBelowSuccSize child0 _)) tp0Formed
            (.cons (.fixed _) tp1Formed
              (.cons (.fixed _) univ0Formed
                (.cons (.fixed _) univ1Formed .nil)))
      | there _ tail1 => cases tail1 with
        | here _ child1Step =>
            exact .cons (.fixed _) tp0Formed
              (.cons (.stepsBelow child1Step (secondChildBelowSuccSize child0 child1 .childNil)) tp1Formed
                (.cons (.fixed _) univ0Formed
                  (.cons (.fixed _) univ1Formed .nil)))
        | there _ tail2 => cases tail2
    have memberAfterEq : pairIntroRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_pair () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest1 => cases rest1 with
        | childCons _ rest2 => cases rest2; rfl
    rw [← memberAfterEq]
    exact introGateRowReassembleBounded .gen_pair pairIntroRule
      (.childCons typeParam0 (.childCons typeParam1 .childNil)) level0 level1 flag introRuleOf_pair
      premisesHold childSubjectReductionBelow trivial driftAt (Conv.refl _)

/-- **The `listCons` branch (bounded)** — a grown head at the element type and a union-recursive tail at
`List(element)`; either can step. -/
theorem listConsIntroGateBranchClosesBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (args : RawTermChildren listConsIntroRule.argShifts scope)
    (params : RawTermChildren listConsIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ listConsIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (listConsIntroRule.memberCell scope args).size)
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
    have driftAt : ObligationsDriftBelow profile (listConsIntroRule.memberCell scope
        (.childCons head (.childCons tail .childNil))).size
        (listConsIntroRule.obligations scope context (.childCons head (.childCons tail .childNil))
          (.childCons elementType .childNil) level0 level1 flag)
        (listConsIntroRule.obligations scope context childrenAfter
          (.childCons elementType .childNil) level0 level1 flag) := by
      cases childStep with
      | here _ headStep =>
          exact .cons (.stepsBelow headStep (headChildBelowSuccSize head _)) elemFormed
            (.cons (.fixed _) listFormed .nil)
      | there _ tail1 => cases tail1 with
        | here _ tailStep =>
            exact .cons (.fixed _) elemFormed
              (.cons (.stepsBelow tailStep (secondChildBelowSuccSize head tail .childNil)) listFormed .nil)
        | there _ tail2 => cases tail2
    have memberAfterEq : listConsIntroRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_listCons () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest1 => cases rest1 with
        | childCons _ rest2 => cases rest2; rfl
    rw [← memberAfterEq]
    exact introGateRowReassembleBounded .gen_listCons listConsIntroRule
      (.childCons elementType .childNil) level0 level1 flag introRuleOf_listCons premisesHold
      childSubjectReductionBelow trivial driftAt (Conv.refl _)

/-! ## The output-drifting grown constructor — `refl` -/

/-- **The `refl` branch (bounded)** — output `idType(param, witness, witness)` reads the stepping `witness` twice,
so a witness step drifts the output via a two-step `gen_idCode` congruence chain; the sole obligation
`witness : param` drifts as for `optionSome`. -/
theorem reflIntroGateBranchClosesBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (args : RawTermChildren reflIntroRule.argShifts scope)
    (params : RawTermChildren reflIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ reflIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (reflIntroRule.memberCell scope args).size)
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
    have driftAt : ObligationsDriftBelow profile (reflIntroRule.memberCell scope
        (.childCons witness .childNil)).size
        (reflIntroRule.obligations scope context (.childCons witness .childNil)
          (.childCons typeParam0 .childNil) level0 level1 flag)
        (reflIntroRule.obligations scope context childrenAfter
          (.childCons typeParam0 .childNil) level0 level1 flag) := by
      cases childStep with
      | here _ witnessStep =>
          exact .cons (.stepsBelow witnessStep (headChildBelowSuccSize witness .childNil)) tp0Formed .nil
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
    exact introGateRowReassembleBounded .gen_refl reflIntroRule
      (.childCons typeParam0 .childNil) level0 level1 flag introRuleOf_refl premisesHold
      childSubjectReductionBelow trivial driftAt outputDriftAt

/-! ## The graded binder — `lam` (domain-step context drift + `piTyCode` output drift) -/

/-- **The `lam` branch (bounded)** — a domain step drifts the codomain / body obligation CONTEXTS via
`consContextHeadConv` plus the `piTyCode` output; a body step is a single context-fixed obligation drift. -/
theorem lamIntroGateBranchClosesBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (args : RawTermChildren lamIntroRule.argShifts scope)
    (params : RawTermChildren lamIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ lamIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile (lamIntroRule.memberCell scope args).size)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : lamIntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (lamIntroRule.outputType scope args params) := by
  match args, params with
  | .childCons domainCode (.childCons body .childNil), .childCons codomainCode .childNil =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have domainCodeFormed : UnionClassifierIsType profile context domainCode :=
      ⟨level0, flag, premisesHold _ (List.Mem.head _)⟩
    have codomainTyped : HasTypeUnion profile (context.cons domainCode) codomainCode
        (universeCodeCell level1 flag) :=
      premisesHold _ (List.Mem.tail _ (List.Mem.head _))
    have univ0Formed : UnionClassifierIsType profile context (universeCodeCell level0 flag) :=
      ⟨_, _, HasTypeUnion.universeFormation context level0 flag⟩
    cases childStep with
    | @here _ _ _ _ domainPrime _ domainStep =>
        have bindingConv : Conv domainCode domainPrime :=
          ⟨_, StepStar.single domainStep, StepStar.refl _⟩
        exact introGateRowReassembleBounded (argsAfter := .childCons domainPrime (.childCons body .childNil))
          .gen_lam lamIntroRule (.childCons codomainCode .childNil) level0 level1 flag introRuleOf_lam
          premisesHold childSubjectReductionBelow (gradedBinderChecks_spectrum body).1
          (.cons (.stepsBelow domainStep (headChildBelowSuccSize domainCode _)) univ0Formed
            (.consContextHeadConv bindingConv domainCodeFormed (Conv.refl _)
                ⟨_, _, HasTypeUnion.universeFormation (context.cons domainPrime) level1 flag⟩
              (.consContextHeadConv bindingConv domainCodeFormed (Conv.refl _)
                  ⟨level1, flag, HasTypeUnion.convertHeadBinding codomainTyped bindingConv domainCodeFormed⟩
                .nil)))
          ⟨_, StepStar.refl _,
            StepStar.single (Step.cong .gen_piTyCode ()
              (.here (.childCons codomainCode .childNil) domainStep))⟩
    | there _ tail1 => cases tail1 with
      | @here _ _ _ _ bodyPrime _ bodyStep =>
          exact introGateRowReassembleBounded (argsAfter := .childCons domainCode (.childCons bodyPrime .childNil))
            .gen_lam lamIntroRule (.childCons codomainCode .childNil) level0 level1 flag introRuleOf_lam
            premisesHold childSubjectReductionBelow (gradedBinderChecks_spectrum bodyPrime).1
            (.cons (.fixed _) univ0Formed
              (.cons (.fixed _)
                  ⟨_, _, HasTypeUnion.universeFormation (context.cons domainCode) level1 flag⟩
                (.cons (.stepsBelow bodyStep (secondChildBelowSuccSize domainCode body .childNil))
                    ⟨level1, flag, codomainTyped⟩
                  .nil)))
            (Conv.refl _)
      | there _ tail2 => cases tail2

end FX1Poly.Typed
