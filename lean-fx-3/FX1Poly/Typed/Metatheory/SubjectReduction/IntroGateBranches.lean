import FX1Poly.Typed.Metatheory.SubjectReduction.IntroGateBranchesBounded
import FX1Poly.Typed.Metatheory.SubjectReduction.IntroGateReassemble
import FX1Poly.Typed.Metatheory.SubjectReduction.UsabilityHoldsUnderObligationsDrift
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity
import FX1Poly.Typed.Metatheory.Validity.IntervalNotConvRigidHeads

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/IntroGateBranches
    — SR-DSL-5: the per-generator branches of the INTRODUCER-congruence gate (the `Conv`-refl-output rows)

`UnionIntroCongruenceCloses` (HasTypeUnionCongruenceClosesGeneric.lean) dispatches on the introducer generator.
This file ships the per-generator BRANCH lemmas for all sixteen decided introducer rows, each consuming the
UNIVERSAL child-SR self-reference `UnionChildSubjectReduction profile`.

## ★ Every row here is DERIVED from its fuel-bounded twin — this file states, it does not prove

The branch statements below differ from their `IntroGateBranchesBounded` twins in EXACTLY ONE hypothesis: the
child-SR flavor.  The unbounded row takes the universal `UnionChildSubjectReduction profile`; the bounded row
takes `UnionChildSubjectReductionBelow profile (ruleX.memberCell scope args).size`.  Every other hypothesis —
`args` / `params` / levels / `flag` / `premisesHold` / `wellFormed` / `usabilityHolds` / `memberEq` /
`childStep` — and the ENTIRE conclusion are identical, in the same argument positions.

The bounded hypothesis is WEAKER (it constrains only subterms below the cell's own size), so the bounded row is
the STRONGER theorem and the unbounded row is its corollary: `UnionChildSubjectReduction.toBelow` forgets the
size gate at any bound, in particular at `(ruleX.memberCell scope args).size`.  So each row below is a single
application of its bounded twin at `childSubjectReduction.toBelow`.

This is the honest direction of the collapse.  The proof CONTENT (the `mkGen` injection, the per-arg
`ObligationsDrift` construction, the `usabilityHoldsAfter` discharge, the `refl` / `lam` output-drift chains)
lives ONCE, in the bounded twin, where the fuel-bounded SR tie-off actually consumes it.  Writing it twice —
once per flavor — is what this file used to do; a new introducer row now needs its proof written ONLY in the
bounded file, and its unbounded row falls out by `toBelow`.

## What is NOT derived — the two head-refutation helpers

`intervalTypeCell_not_conv_natTypeCell` / `intervalTypeCell_not_conv_listTypeCell` are genuine content and are
stated here in full: they are public API (the bounded twin keeps its own `private` copies, since it sits BELOW
this file in the import graph and cannot reach these).

## Zero-axiom

`UnionChildSubjectReduction.toBelow` (`Nat` order only) + the bounded twins + `Conv.refutedByDistinctStableHeads`
with `Generator.noConfusion`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## The head-refutation kit — genuine content (public API; not derived)

Both `intervalTypeCell` and the data former are step normal forms with distinct head generators, so a `Conv` join
is refuted by `Conv.refutedByDistinctStableHeads`. -/

/-- `Interval ≢ Nat` under conversion (`gen_intervalCode` vs `gen_natCode` head no-confusion). -/
theorem intervalTypeCell_not_conv_natTypeCell {scope : Nat} :
    ¬ Conv (intervalTypeCell : RawTerm scope) natTypeCell :=
  fun convertibility =>
    Conv.refutedByDistinctStableHeads convertibility
      (fun _reduct chain => headReaches_intervalTypeCell chain)
      (fun _reduct chain => headReaches_natTypeCell chain)
      (fun headsEqual => Generator.noConfusion headsEqual)

/-- `Interval ≢ List A` under conversion (`gen_intervalCode` vs `gen_listCode` head no-confusion). -/
theorem intervalTypeCell_not_conv_listTypeCell {scope : Nat} (elementType : RawTerm scope) :
    ¬ Conv (intervalTypeCell : RawTerm scope) (listTypeCell elementType) :=
  fun convertibility =>
    Conv.refutedByDistinctStableHeads convertibility
      (fun _reduct chain => headReaches_intervalTypeCell chain)
      (fun _reduct chain => headReaches_listTypeCell chain)
      (fun headsEqual => Generator.noConfusion headsEqual)

/-! ## The eight nullary data constructors — vacuous `childStep` (constant `mkGen genX () childNil`)

Each row forgets the size gate (`toBelow`) into its bounded twin, whose proof injects the `mkGen` equation and
kills the vacuous empty-child-vector step. -/

/-- **The `boolTrue` branch** — nullary; `memberCell` is the constant `mkGen gen_boolTrue () childNil`, so the
gate's `childStep` steps an empty child vector and is vacuous.  Derived from `boolTrueIntroGateBranchClosesBounded`. -/
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
      Conv pinned (boolTrueIntroRule.outputType scope args params) :=
  boolTrueIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
    childSubjectReduction.toBelow wellFormed memberEq childStep

/-- **The `boolFalse` branch** — nullary; vacuous `childStep`.  Derived from its bounded twin. -/
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
      Conv pinned (boolFalseIntroRule.outputType scope args params) :=
  boolFalseIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
    childSubjectReduction.toBelow wellFormed memberEq childStep

/-- **The `unit` branch** — nullary; vacuous `childStep`.  Derived from its bounded twin. -/
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
      Conv pinned (unitIntroRule.outputType scope args params) :=
  unitIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
    childSubjectReduction.toBelow wellFormed memberEq childStep

/-- **The `interval0` branch** — nullary; vacuous `childStep`.  Derived from its bounded twin. -/
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
      Conv pinned (interval0IntroRule.outputType scope args params) :=
  interval0IntroGateBranchClosesBounded args params level0 level1 flag premisesHold
    childSubjectReduction.toBelow wellFormed memberEq childStep

/-- **The `interval1` branch** — nullary; vacuous `childStep`.  Derived from its bounded twin. -/
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
      Conv pinned (interval1IntroRule.outputType scope args params) :=
  interval1IntroGateBranchClosesBounded args params level0 level1 flag premisesHold
    childSubjectReduction.toBelow wellFormed memberEq childStep

/-- **The `natZero` branch** — nullary; vacuous `childStep`.  Derived from its bounded twin. -/
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
      Conv pinned (natZeroIntroRule.outputType scope args params) :=
  natZeroIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
    childSubjectReduction.toBelow wellFormed memberEq childStep

/-- **The `optionNone` branch** — nullary in `args` (the free type is a `param`); vacuous `childStep`.  Derived
from its bounded twin. -/
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
      Conv pinned (optionNoneIntroRule.outputType scope args params) :=
  optionNoneIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
    childSubjectReduction.toBelow wellFormed memberEq childStep

/-- **The `listNil` branch** — nullary in `args` (the free type is a `param`); vacuous `childStep`.  Derived from
its bounded twin. -/
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
      Conv pinned (listNilIntroRule.outputType scope args params) :=
  listNilIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
    childSubjectReduction.toBelow wellFormed memberEq childStep

/-! ## The recursive / grown data constructors — one arg steps, `Conv.refl` output

Each bounded twin builds the per-arg `ObligationsDriftBelow` and hands it to `introGateRowReassembleBounded`;
the rows below forget the size gate into them. -/

/-- **The `natSucc` branch** — one union-recursive child at `Nat`; when it steps, its sole obligation drifts
(`StepStar.single`), output `natType` is constant (`Conv.refl`).  Derived from its bounded twin. -/
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
      Conv pinned (natSuccIntroRule.outputType scope args params) :=
  natSuccIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
    childSubjectReduction.toBelow wellFormed memberEq childStep

/-- **The `optionSome` branch** — one grown child at the type `param`; when it steps, its sole obligation drifts,
output `option(param)` is param-determined (`Conv.refl`).  Derived from its bounded twin. -/
theorem optionSomeIntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren optionSomeIntroRule.argShifts scope)
    (params : RawTermChildren optionSomeIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ optionSomeIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    -- ★ A1-CONJUNCT-WIRE: before-args usability threaded from the gate's `usabilityHolds`; after-args usability by
    -- step-preservation (`usabilityHoldsUnderObligationsDrift`) — no oracle, no interval refuter.
    (usabilityHolds : ∀ obligation ∈ optionSomeIntroRule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : optionSomeIntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (optionSomeIntroRule.outputType scope args params) :=
  optionSomeIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
    childSubjectReduction.toBelow wellFormed memberEq childStep usabilityHolds

/-- **The `eitherInl` branch** — one grown value at the LEFT type; the two type-`param` formedness obligations are
unchanged when the value steps, output `either(param0, param1)` param-determined (`Conv.refl`).  Derived from its
bounded twin. -/
theorem eitherInlIntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren eitherInlIntroRule.argShifts scope)
    (params : RawTermChildren eitherInlIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ eitherInlIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    -- ★ A1-CONJUNCT-WIRE: before-args usability threaded from the gate's `usabilityHolds`; after-args usability by
    -- step-preservation (`usabilityHoldsUnderObligationsDrift`).
    (usabilityHolds : ∀ obligation ∈ eitherInlIntroRule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : eitherInlIntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (eitherInlIntroRule.outputType scope args params) :=
  eitherInlIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
    childSubjectReduction.toBelow wellFormed memberEq childStep usabilityHolds

/-- **The `eitherInr` branch** — the `eitherInl` twin (value at the RIGHT type, output puts the free side first);
same one-arg drift.  Derived from its bounded twin. -/
theorem eitherInrIntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren eitherInrIntroRule.argShifts scope)
    (params : RawTermChildren eitherInrIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ eitherInrIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    -- ★ A1-CONJUNCT-WIRE: before-args usability threaded from the gate's `usabilityHolds`; after-args usability by
    -- step-preservation (`usabilityHoldsUnderObligationsDrift`).
    (usabilityHolds : ∀ obligation ∈ eitherInrIntroRule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : eitherInrIntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (eitherInrIntroRule.outputType scope args params) :=
  eitherInrIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
    childSubjectReduction.toBelow wellFormed memberEq childStep usabilityHolds

/-- **The `pair` branch** — two grown children at the two type `param`s plus two formedness obligations; either
child can step (cases the two `args` positions), the other obligations stay `refl`, output `product(param0, param1)`
param-determined (`Conv.refl`).  Derived from its bounded twin. -/
theorem pairIntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren pairIntroRule.argShifts scope)
    (params : RawTermChildren pairIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ pairIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    -- ★ A1-CONJUNCT-WIRE: before-args usability threaded from the gate's `usabilityHolds`; after-args usability by
    -- step-preservation (`usabilityHoldsUnderObligationsDrift`).
    (usabilityHolds : ∀ obligation ∈ pairIntroRule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : pairIntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (pairIntroRule.outputType scope args params) :=
  pairIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
    childSubjectReduction.toBelow wellFormed memberEq childStep usabilityHolds

/-- **The `listCons` branch** — a grown head at the element type and a union-recursive tail at `List(element)`;
either can step, output `List(element)` param-determined (`Conv.refl`).  Derived from its bounded twin. -/
theorem listConsIntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren listConsIntroRule.argShifts scope)
    (params : RawTermChildren listConsIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ listConsIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    -- ★ A1-CONJUNCT-WIRE: before-args usability threaded from the gate's `usabilityHolds`; after-args usability by
    -- step-preservation (`usabilityHoldsUnderObligationsDrift`).
    (usabilityHolds : ∀ obligation ∈ listConsIntroRule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : listConsIntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (listConsIntroRule.outputType scope args params) :=
  listConsIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
    childSubjectReduction.toBelow wellFormed memberEq childStep usabilityHolds

/-! ## The output-drifting grown constructor — `refl` (the witness flows into the `idType` output) -/

/-- **The `refl` branch** — output `idType(param, witness, witness)` reads the stepping `witness` TWICE, so a witness
step drifts the output: `idType A w w` reduces (both endpoint children of `gen_idCode`) to `idType A w' w'`, giving
`Conv (idType A w' w') (idType A w w)` via a two-step `gen_idCode` congruence chain (left endpoint, then right).
The sole obligation `witness : param` drifts as for `optionSome`.  Derived from its bounded twin. -/
theorem reflIntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren reflIntroRule.argShifts scope)
    (params : RawTermChildren reflIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ reflIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    -- ★ A1-CONJUNCT-WIRE: before-args usability threaded from the gate's `usabilityHolds`; after-args usability by
    -- step-preservation (`usabilityHoldsUnderObligationsDrift`).
    (usabilityHolds : ∀ obligation ∈ reflIntroRule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : reflIntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (reflIntroRule.outputType scope args params) :=
  reflIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
    childSubjectReduction.toBelow wellFormed memberEq childStep usabilityHolds

/-! ## The graded binder — `lam` (domain-step context drift + `piTyCode` output drift)

The bounded twin cases `childStep` at top level and passes `argsAfter` explicitly (concrete), splitting the two arg
positions:

  * **domain steps** — obligation 0 (`domainCode : Type@l0`) is context-fixed (`cons`); obligations 1 / 2 live at
    `context.cons domainCode`, whose head drifts to `cons domainCode'` (`consContextHeadConv`); the codomain
    formedness at the new binder comes via `convertHeadBinding`; and the output `piTyCode(domainCode, codomainCode)`
    drifts at the domain child (a single `gen_piTyCode` congruence step);
  * **body steps** — only obligation 2 (`body : codomainCode`) drifts, context-fixed; the output is unchanged
    (`Conv.refl`). -/

/-- **The `lam` branch** — the unrestricted (`.omega`) graded binder.  A domain step drifts the codomain / body
obligation CONTEXTS (`cons domainCode ⟶ cons domainCode'`) via `consContextHeadConv` plus the `piTyCode` output; a
body step is a single context-fixed obligation drift with unchanged output.  Derived from its bounded twin. -/
theorem lamIntroGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren lamIntroRule.argShifts scope)
    (params : RawTermChildren lamIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ lamIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    -- ★ A1-CONJUNCT-WIRE: the before-args obligation usability threaded from the gate's `usabilityHolds` (the native
    -- `intro` arm's field); every `lam` obligation (domain / codomain formedness, body) is FIBRANT, so the whole
    -- after-args usability is closed by step-preservation (`usabilityHoldsUnderObligationsDrift`).
    (usabilityHolds : ∀ obligation ∈ lamIntroRule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : lamIntroRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (lamIntroRule.outputType scope args params) :=
  lamIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
    childSubjectReduction.toBelow wellFormed memberEq childStep usabilityHolds

end FX1Poly.Typed
