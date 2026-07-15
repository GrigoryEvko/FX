import FX1Poly.Typed.Engine.RuleTables.CellTemplate
import FX1Poly.Typed.Metatheory.SubjectReduction.TemplateConvUnderChildStep
import FX1Poly.Typed.Metatheory.SubjectReduction.StepStarCellCongruence
import FX1Poly.Core.Rewriting.Reduction.Step.StepSubst
import FX1Poly.Typed.Cell.NatElimDependentSuccType
import FX1Poly.Typed.Cell.OptionMatchDependentSomeBranchType
import FX1Poly.Typed.Cell.EitherMatchDependentBranchType
import FX1Poly.Typed.Cell.ListElimDependentConsType

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/TemplateStepStarUnderChildStep
    — SR-DSL-2: generic DIRECTED type-SR over CellTemplate (the table-driven type-SR keystone)

The DIRECTED (`Step` ↝ `StepStar`) twin of SR-DSL-1's `templateConvUnderChildStep`.  When the cell's children
(`args`) and type-index params step pointwise (`StepStarChildren`: the congruence-SR situation — one child of the
subject steps, the rest fixed → `StepStar.single`/`StepStar.refl`), the `interpret?`-produced type/classifier
REDUCES (`StepStar`) to the post-step term.  Composed with `UnionClassifierIsType.preservedUnderStepStar` (universe
rigidity) this gives `templateTypeStepPreservesUniverse`: the drifted branch classifier stays a well-formed type.

This DISSOLVES the locked design's flag-coherence frontier (SR-DSL-3) and its honest relative-conservativity
caveat: type-formedness transfers across the DIRECTED reduction via subject reduction at the universe, never
re-forming a `piTyCode` from its legs, so no `isFlagCoherent`, no flag threading, no universe-flag uniqueness.

ONE mutual induction on `CellTemplate` / `CellTemplateSpine` — every arm a single dispatch to a shipped directed
congruence (`StepStar.subst0Both` / `substPairAll` / `piTyCode_cong` / `weakenBy*Star` / `ofStepStarChildren`).
SUBSUMES the per-eliminator type-SR corpus (`*_formedUnderMotiveStep`, `natElimDependentSuccBranchType_formed_of-
Motive`): a new eliminator row's branch type is a `CellTemplate`, so the generic lemma covers it with ZERO new
proof.

The pointwise `StepStarChildren` mirrors `ConvChildren` exactly, so every projection lemma and the mutual
induction transcribe verbatim from `TemplateConvUnderChildStep.lean` with `Conv` ↝ `StepStar`.  The bridge
`StepStarChildren.toChildrenStar` lifts the pointwise relation to the existing chain machinery
(`StepStar.ofChildrenStar`) with the shift as a BOUND variable, dodging the `scope`-vs-`scope+0` head-shift
unification wall that blocks a hand-built children spine.

## Zero-axiom

The shipped directed `StepStar.*` congruences over structural `Nat` / `StepStarChildren` / `CellTemplate`
inductions, with the propext-clean `bindEqSomeIff` (reused from SR-DSL-1).  No `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, or `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Axis.Syntax

/-! ## Pointwise directed children relation (the `ConvChildren` directed twin) -/

/-- Two children vectors related POINTWISE by `StepStar` (each position's child reduces).  The directed twin of
`ConvChildren`; the congruence-SR caller builds it with `StepStar.refl` at the fixed positions and
`StepStar.single` at the one stepping child. -/
inductive StepStarChildren : ∀ {binderShifts : List Nat} {scope : Nat},
    RawTermChildren binderShifts scope → RawTermChildren binderShifts scope → Prop where
  | nilS {scope : Nat} :
      StepStarChildren (.childNil : RawTermChildren [] scope) .childNil
  | consS {scope shift : Nat} {restShifts : List Nat}
      {headBefore headAfter : RawTerm (scope + shift)}
      {restBefore restAfter : RawTermChildren restShifts scope}
      (headChain : StepStar headBefore headAfter)
      (restChain : StepStarChildren restBefore restAfter) :
      StepStarChildren (.childCons headBefore restBefore)
                       (.childCons headAfter restAfter)

/-- Bridge the pointwise relation to the chain machinery: step each head (rest fixed at the start) then each
rest (head fixed at the target), composed.  The `StepChildrenStar.here`/`there` shifts are inferred from the
chains' endpoint types (bound `shift`), so the `scope`-vs-`scope+0` wall never appears. -/
theorem StepStarChildren.toChildrenStar {binderShifts : List Nat} {scope : Nat}
    {before after : RawTermChildren binderShifts scope}
    (pointwise : StepStarChildren before after) : StepChildrenStar before after := by
  induction pointwise with
  | nilS => exact StepChildrenStar.refl _
  | consS headChain _ restToChildrenStar =>
      exact StepChildrenStar.trans_compose
        (StepChildrenStar.here _ headChain)
        (StepChildrenStar.there _ restToChildrenStar)

/-- Cell congruence from the pointwise children relation: `StepStar (mkGen gen p before) (mkGen gen p after)`.
The directed twin of `Conv.ofChildren`. -/
theorem StepStar.ofStepStarChildren {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {before after : RawTermChildren generator.binderShifts scope}
    (pointwise : StepStarChildren before after) :
    StepStar (.mkGen generator payload before) (.mkGen generator payload after) :=
  StepStar.ofChildrenStar pointwise.toChildrenStar

/-- Reflexivity of the pointwise directed children relation — every position reduces by `StepStar.refl`.
Structural recursion on `binderShifts` (the binder-form children fold), so propext-clean. -/
theorem StepStarChildren.refl {scope : Nat} :
    ∀ {binderShifts : List Nat} (children : RawTermChildren binderShifts scope),
      StepStarChildren children children := by
  intro binderShifts
  induction binderShifts with
  | nil => intro children; cases children; exact StepStarChildren.nilS
  | cons _shift _restShifts restRefl =>
      intro children
      cases children with
      | childCons head rest => exact StepStarChildren.consS (StepStar.refl head) (restRefl rest)

/-- **The single-child congruence step lifts to the pointwise directed relation.**  A `StepChildren` (exactly
one child of the spine `Step`-reduces, the rest fixed) is a `StepStarChildren` with that one child carrying
`StepStar.single` and every other position carrying `StepStarChildren.refl`.  This is the bridge from the
congruence gate's INPUT (`StepChildren args argsAfter`) to the directed engine's INPUT
(`StepStarChildren args argsAfter`).  Structural recursion on `binderShifts` + `cases` on the (mutual-inductive,
`induction`-rejecting) `StepChildren` — `here` lifts the head step, `there` recurses into the tail. -/
theorem StepChildren.toStepStarChildren {scope : Nat} :
    ∀ {binderShifts : List Nat} {before after : RawTermChildren binderShifts scope},
      StepChildren before after → StepStarChildren before after := by
  intro binderShifts
  induction binderShifts with
  | nil => intro before _after step; cases before; cases step
  | cons _shift _restShifts restToStepStar =>
      intro before _after step
      cases before with
      | childCons head rest =>
          cases step with
          | here _ childStep =>
              exact StepStarChildren.consS (StepStar.single childStep) (StepStarChildren.refl rest)
          | there _ restStep =>
              exact StepStarChildren.consS (StepStar.refl head) (restToStepStar restStep)

/-! ## `StepStarChildren` projection at a fixed shift (verbatim `ConvChildren.projectShift*` mirror) -/

/-- Slot projection at shift 0 respects `StepStarChildren`. -/
theorem StepStarChildren.projectShiftZero {argShifts : List Nat} {scope : Nat}
    {vecBefore vecAfter : RawTermChildren argShifts scope}
    (vecStepStar : StepStarChildren vecBefore vecAfter) :
    (slot : Nat) → {projBefore : RawTerm scope} →
    (scopedChildAt? vecBefore.toScopedChildren slot).bind ScopedChild.atShiftZero? = some projBefore →
    ∃ projAfter,
      (scopedChildAt? vecAfter.toScopedChildren slot).bind ScopedChild.atShiftZero? = some projAfter ∧
      StepStar projBefore projAfter := by
  induction vecStepStar with
  | nilS =>
      intro slot projBefore projEq
      cases slot <;> exact absurd projEq (by intro h; cases h)
  | @consS scope shift restShifts headBefore headAfter restBefore restAfter headChain _ restIH =>
      intro slot projBefore projEq
      cases slot with
      | zero =>
          cases shift with
          | zero =>
              refine ⟨headAfter, rfl, ?_⟩
              have projBeforeEq : projBefore = headBefore := (Option.some.inj projEq).symm
              rw [projBeforeEq]; exact headChain
          | succ _ => exact absurd projEq (by intro h; cases h)
      | succ priorSlot => exact restIH priorSlot projEq

/-- Slot projection at shift 1 (a one-binder body) respects `StepStarChildren`. -/
theorem StepStarChildren.projectShiftOne {argShifts : List Nat} {scope : Nat}
    {vecBefore vecAfter : RawTermChildren argShifts scope}
    (vecStepStar : StepStarChildren vecBefore vecAfter) :
    (slot : Nat) → {projBefore : RawTerm (scope + 1)} →
    (scopedChildAt? vecBefore.toScopedChildren slot).bind ScopedChild.atShiftOne? = some projBefore →
    ∃ projAfter,
      (scopedChildAt? vecAfter.toScopedChildren slot).bind ScopedChild.atShiftOne? = some projAfter ∧
      StepStar projBefore projAfter := by
  induction vecStepStar with
  | nilS =>
      intro slot projBefore projEq
      cases slot <;> exact absurd projEq (by intro h; cases h)
  | @consS scope shift restShifts headBefore headAfter restBefore restAfter headChain _ restIH =>
      intro slot projBefore projEq
      cases slot with
      | zero =>
          cases shift with
          | zero => exact absurd projEq (by intro h; cases h)
          | succ priorShift =>
              cases priorShift with
              | zero =>
                  refine ⟨headAfter, rfl, ?_⟩
                  have projBeforeEq : projBefore = headBefore := (Option.some.inj projEq).symm
                  rw [projBeforeEq]; exact headChain
              | succ _ => exact absurd projEq (by intro h; cases h)
      | succ priorSlot => exact restIH priorSlot projEq

/-- Slot projection at shift 2 (a two-binder body) respects `StepStarChildren`. -/
theorem StepStarChildren.projectShiftTwo {argShifts : List Nat} {scope : Nat}
    {vecBefore vecAfter : RawTermChildren argShifts scope}
    (vecStepStar : StepStarChildren vecBefore vecAfter) :
    (slot : Nat) → {projBefore : RawTerm (scope + 2)} →
    (scopedChildAt? vecBefore.toScopedChildren slot).bind ScopedChild.atShiftTwo? = some projBefore →
    ∃ projAfter,
      (scopedChildAt? vecAfter.toScopedChildren slot).bind ScopedChild.atShiftTwo? = some projAfter ∧
      StepStar projBefore projAfter := by
  induction vecStepStar with
  | nilS =>
      intro slot projBefore projEq
      cases slot <;> exact absurd projEq (by intro h; cases h)
  | @consS scope shift restShifts headBefore headAfter restBefore restAfter headChain _ restIH =>
      intro slot projBefore projEq
      cases slot with
      | zero =>
          cases shift with
          | zero => exact absurd projEq (by intro h; cases h)
          | succ priorShift =>
              cases priorShift with
              | zero => exact absurd projEq (by intro h; cases h)
              | succ priorPriorShift =>
                  cases priorPriorShift with
                  | zero =>
                      refine ⟨headAfter, rfl, ?_⟩
                      have projBeforeEq : projBefore = headBefore := (Option.some.inj projEq).symm
                      rw [projBeforeEq]; exact headChain
                  | succ _ => exact absurd projEq (by intro h; cases h)
      | succ priorSlot => exact restIH priorSlot projEq

/-! ## `resolveChildRef?` projection agreement (verbatim `resolveProjectShift*` mirror) -/

/-- Shift-0 resolved-projection agreement. -/
theorem resolveProjectShiftStarZero {argShifts paramShifts : List Nat} {scope : Nat}
    {argsLeft argsRight : RawTermChildren argShifts scope}
    {paramsLeft paramsRight : RawTermChildren paramShifts scope}
    (argsStepStar : StepStarChildren argsLeft argsRight) (paramsStepStar : StepStarChildren paramsLeft paramsRight)
    (childReference : ChildRef) {leftProj : RawTerm scope}
    (projEq : (resolveChildRef? argsLeft paramsLeft childReference).bind ScopedChild.atShiftZero? = some leftProj) :
    ∃ rightProj,
      (resolveChildRef? argsRight paramsRight childReference).bind ScopedChild.atShiftZero? = some rightProj ∧
      StepStar leftProj rightProj := by
  cases childReference with
  | argChild slot => exact StepStarChildren.projectShiftZero argsStepStar slot projEq
  | paramChild slot => exact StepStarChildren.projectShiftZero paramsStepStar slot projEq

/-- Shift-1 resolved-projection agreement. -/
theorem resolveProjectShiftStarOne {argShifts paramShifts : List Nat} {scope : Nat}
    {argsLeft argsRight : RawTermChildren argShifts scope}
    {paramsLeft paramsRight : RawTermChildren paramShifts scope}
    (argsStepStar : StepStarChildren argsLeft argsRight) (paramsStepStar : StepStarChildren paramsLeft paramsRight)
    (childReference : ChildRef) {leftProj : RawTerm (scope + 1)}
    (projEq : (resolveChildRef? argsLeft paramsLeft childReference).bind ScopedChild.atShiftOne? = some leftProj) :
    ∃ rightProj,
      (resolveChildRef? argsRight paramsRight childReference).bind ScopedChild.atShiftOne? = some rightProj ∧
      StepStar leftProj rightProj := by
  cases childReference with
  | argChild slot => exact StepStarChildren.projectShiftOne argsStepStar slot projEq
  | paramChild slot => exact StepStarChildren.projectShiftOne paramsStepStar slot projEq

/-- Shift-2 resolved-projection agreement. -/
theorem resolveProjectShiftStarTwo {argShifts paramShifts : List Nat} {scope : Nat}
    {argsLeft argsRight : RawTermChildren argShifts scope}
    {paramsLeft paramsRight : RawTermChildren paramShifts scope}
    (argsStepStar : StepStarChildren argsLeft argsRight) (paramsStepStar : StepStarChildren paramsLeft paramsRight)
    (childReference : ChildRef) {leftProj : RawTerm (scope + 2)}
    (projEq : (resolveChildRef? argsLeft paramsLeft childReference).bind ScopedChild.atShiftTwo? = some leftProj) :
    ∃ rightProj,
      (resolveChildRef? argsRight paramsRight childReference).bind ScopedChild.atShiftTwo? = some rightProj ∧
      StepStar leftProj rightProj := by
  cases childReference with
  | argChild slot => exact StepStarChildren.projectShiftTwo argsStepStar slot projEq
  | paramChild slot => exact StepStarChildren.projectShiftTwo paramsStepStar slot projEq

/-! ## Branch-type `StepStar`-congruence in BOTH arguments (the `listConsBranchType` macro arm) -/

/-- `listElimDependentConsBranchType` reduces in BOTH the motive and the element type — the directed twin of
`listElimDependentConsBranchType_convStable`.  Verbatim mirror with `Conv` ↝ `StepStar`. -/
theorem listElimDependentConsBranchType_stepStable {scope : Nat}
    {motiveLeft motiveRight : RawTerm (scope + 1)} {eltLeft eltRight : RawTerm scope}
    (motiveChain : StepStar motiveLeft motiveRight) (eltChain : StepStar eltLeft eltRight) :
    StepStar (listElimDependentConsBranchType motiveLeft eltLeft)
             (listElimDependentConsBranchType motiveRight eltRight) := by
  unfold listElimDependentConsBranchType
  refine StepStar.piTyCode_cong eltChain (StepStar.piTyCode_cong ?_ (StepStar.piTyCode_cong ?_ ?_))
  · exact StepStar.ofStepStarChildren (StepStarChildren.consS (StepStar.weaken eltChain) StepStarChildren.nilS)
  · unfold listElimDependentRecBinderType; exact StepStar.subst _ motiveChain
  · unfold listElimDependentConsBranchCodomain; exact StepStar.subst _ motiveChain

/-! ## SR-DSL-2 ★ the generic directed type-SR master (`templateStepStarUnderChildStep`)

Verbatim directed mirror of SR-DSL-1's `templateConvUnderChildStep`: `ConvChildren` ↝ `StepStarChildren`,
`Conv` ↝ `StepStar`, the `Conv.*` congruences ↝ the shipped `StepStar.*` twins.  ONE mutual induction on
`CellTemplate` / `CellTemplateSpine`; SUBSUMES the per-eliminator type-SR corpus. -/

mutual

/-- The generic directed type-SR over a `CellTemplate` (existential form: if the left interpretation succeeds,
the right succeeds at a `StepStar`-reachable term).  Mutual with `spineStepStarUnderChildStep`; structural on the
template. -/
theorem templateStepStarUnderChildStep {argShifts paramShifts : List Nat} {scope : Nat}
    {argsLeft argsRight : RawTermChildren argShifts scope}
    {paramsLeft paramsRight : RawTermChildren paramShifts scope}
    (argsStepStar : StepStarChildren argsLeft argsRight)
    (paramsStepStar : StepStarChildren paramsLeft paramsRight)
    (levels : List LevelExpr) (level0 level1 carrierLevel : LevelExpr) (flag : UniverseFlag) :
    (depth : Nat) → (template : CellTemplate) → (leftTerm : RawTerm (scope + depth)) →
    CellTemplate.interpret? argsLeft paramsLeft levels level0 level1 carrierLevel flag depth template = some leftTerm →
    ∃ rightTerm,
      CellTemplate.interpret? argsRight paramsRight levels level0 level1 carrierLevel flag depth template
        = some rightTerm ∧ StepStar leftTerm rightTerm
  | depth, .childAt ref, leftTerm, projEq => by
      obtain ⟨childL, resolveEq, restEq⟩ := bindEqSomeIff.mp projEq
      obtain ⟨childTermL, atShiftEq, weakEq⟩ := bindEqSomeIff.mp restEq
      have projInput : (resolveChildRef? argsLeft paramsLeft ref).bind ScopedChild.atShiftZero? = some childTermL := by
        rw [resolveEq]; exact atShiftEq
      obtain ⟨childTermR, projRightEq, childStepStar⟩ := resolveProjectShiftStarZero argsStepStar paramsStepStar ref projInput
      obtain ⟨childR, resolveRightEq, atShiftRightEq⟩ := bindEqSomeIff.mp projRightEq
      refine ⟨RawTerm.weakenBy depth childTermR, ?_, ?_⟩
      · exact bindEqSomeIff.mpr ⟨childR, resolveRightEq,
          bindEqSomeIff.mpr ⟨childTermR, atShiftRightEq, rfl⟩⟩
      · rw [(Option.some.inj weakEq).symm]; exact StepStar.weakenByStar childStepStar depth
  | depth, .childBodyAt ref, leftTerm, projEq => by
      cases depth with
      | zero => exact absurd projEq (by intro h; cases h)
      | succ innerDepth =>
          obtain ⟨childL, resolveEq, restEq⟩ := bindEqSomeIff.mp projEq
          obtain ⟨childBodyL, atShiftEq, weakEq⟩ := bindEqSomeIff.mp restEq
          have projInput : (resolveChildRef? argsLeft paramsLeft ref).bind ScopedChild.atShiftOne? = some childBodyL := by
            rw [resolveEq]; exact atShiftEq
          obtain ⟨childBodyR, projRightEq, bodyStepStar⟩ := resolveProjectShiftStarOne argsStepStar paramsStepStar ref projInput
          obtain ⟨childR, resolveRightEq, atShiftRightEq⟩ := bindEqSomeIff.mp projRightEq
          refine ⟨RawTerm.weakenBodyUnderOneBinderBy innerDepth childBodyR, ?_, ?_⟩
          · exact bindEqSomeIff.mpr ⟨childR, resolveRightEq,
              bindEqSomeIff.mpr ⟨childBodyR, atShiftRightEq, rfl⟩⟩
          · rw [(Option.some.inj weakEq).symm]; exact StepStar.weakenBodyUnderOneBinderByStar bodyStepStar innerDepth
  | _depth, .boundVarAt _binderIndex, leftTerm, projEq =>
      ⟨leftTerm, projEq, StepStar.refl leftTerm⟩
  | _depth, .universeCode _levelSource _flagSource, leftTerm, projEq =>
      ⟨leftTerm, projEq, StepStar.refl leftTerm⟩
  | depth, .builtGen head payloadFamily childTemplates, leftTerm, projEq => by
      obtain ⟨childrenL, spineEq, mkEq⟩ := bindEqSomeIff.mp projEq
      obtain ⟨childrenR, spineRightEq, childrenStepStar⟩ :=
        spineStepStarUnderChildStep argsStepStar paramsStepStar levels level0 level1 carrierLevel flag
          depth head.binderShifts childTemplates childrenL spineEq
      refine ⟨RawTerm.mkGen head (payloadFamily (scope + depth)) childrenR, ?_, ?_⟩
      · exact bindEqSomeIff.mpr ⟨childrenR, spineRightEq, rfl⟩
      · rw [(Option.some.inj mkEq).symm]; exact StepStar.ofStepStarChildren childrenStepStar
  | depth, .subst0Into bodyRef argTemplate, leftTerm, projEq => by
      obtain ⟨argTermL, argEq, restEq1⟩ := bindEqSomeIff.mp projEq
      obtain ⟨bodyChildL, resolveEq, restEq2⟩ := bindEqSomeIff.mp restEq1
      obtain ⟨bodyTermL, atShiftEq, substEq⟩ := bindEqSomeIff.mp restEq2
      obtain ⟨argTermR, argRightEq, argStepStar⟩ :=
        templateStepStarUnderChildStep argsStepStar paramsStepStar levels level0 level1 carrierLevel flag
          depth argTemplate argTermL argEq
      have projInput : (resolveChildRef? argsLeft paramsLeft bodyRef).bind ScopedChild.atShiftOne? = some bodyTermL := by
        rw [resolveEq]; exact atShiftEq
      obtain ⟨bodyTermR, projRightEq, bodyStepStar⟩ := resolveProjectShiftStarOne argsStepStar paramsStepStar bodyRef projInput
      obtain ⟨bodyChildR, resolveRightEq, atShiftRightEq⟩ := bindEqSomeIff.mp projRightEq
      refine ⟨RawTerm.subst0 (RawTerm.weakenBodyUnderOneBinderBy depth bodyTermR) argTermR, ?_, ?_⟩
      · exact bindEqSomeIff.mpr ⟨argTermR, argRightEq,
          bindEqSomeIff.mpr ⟨bodyChildR, resolveRightEq,
            bindEqSomeIff.mpr ⟨bodyTermR, atShiftRightEq, rfl⟩⟩⟩
      · rw [(Option.some.inj substEq).symm]
        exact StepStar.subst0Both (StepStar.weakenBodyUnderOneBinderByStar bodyStepStar depth) argStepStar
  | depth, .substPairInto bodyRef innerTemplate outerTemplate, leftTerm, projEq => by
      obtain ⟨innerTermL, innerEq, restEq1⟩ := bindEqSomeIff.mp projEq
      obtain ⟨outerTermL, outerEq, restEq2⟩ := bindEqSomeIff.mp restEq1
      obtain ⟨bodyChildL, resolveEq, restEq3⟩ := bindEqSomeIff.mp restEq2
      obtain ⟨bodyTermL, atShiftEq, substEq⟩ := bindEqSomeIff.mp restEq3
      obtain ⟨innerTermR, innerRightEq, innerStepStar⟩ :=
        templateStepStarUnderChildStep argsStepStar paramsStepStar levels level0 level1 carrierLevel flag
          depth innerTemplate innerTermL innerEq
      obtain ⟨outerTermR, outerRightEq, outerStepStar⟩ :=
        templateStepStarUnderChildStep argsStepStar paramsStepStar levels level0 level1 carrierLevel flag
          depth outerTemplate outerTermL outerEq
      have projInput : (resolveChildRef? argsLeft paramsLeft bodyRef).bind ScopedChild.atShiftTwo? = some bodyTermL := by
        rw [resolveEq]; exact atShiftEq
      obtain ⟨bodyTermR, projRightEq, bodyStepStar⟩ := resolveProjectShiftStarTwo argsStepStar paramsStepStar bodyRef projInput
      obtain ⟨bodyChildR, resolveRightEq, atShiftRightEq⟩ := bindEqSomeIff.mp projRightEq
      refine ⟨RawTerm.substPair (RawTerm.weakenBodyUnderTwoBindersBy depth bodyTermR) innerTermR outerTermR, ?_, ?_⟩
      · exact bindEqSomeIff.mpr ⟨innerTermR, innerRightEq,
          bindEqSomeIff.mpr ⟨outerTermR, outerRightEq,
            bindEqSomeIff.mpr ⟨bodyChildR, resolveRightEq,
              bindEqSomeIff.mpr ⟨bodyTermR, atShiftRightEq, rfl⟩⟩⟩⟩
      · rw [(Option.some.inj substEq).symm]
        exact StepStar.substPairAll (StepStar.weakenBodyUnderTwoBindersByStar bodyStepStar depth) innerStepStar outerStepStar
  | depth, .macroReBasing reBasingMacro, leftTerm, projEq => by
      cases reBasingMacro with
      | natSuccBranchType motiveRef =>
          cases depth with
          | zero => exact absurd projEq (by intro h; cases h)
          | succ d1 =>
              cases d1 with
              | zero => exact absurd projEq (by intro h; cases h)
              | succ innerDepth =>
                  obtain ⟨motiveChildL, resolveEq, restEq⟩ := bindEqSomeIff.mp projEq
                  obtain ⟨motiveBodyL, atShiftEq, weakEq⟩ := bindEqSomeIff.mp restEq
                  have projInput : (resolveChildRef? argsLeft paramsLeft motiveRef).bind ScopedChild.atShiftOne?
                      = some motiveBodyL := by rw [resolveEq]; exact atShiftEq
                  obtain ⟨motiveBodyR, projRightEq, motiveStepStar⟩ :=
                    resolveProjectShiftStarOne argsStepStar paramsStepStar motiveRef projInput
                  obtain ⟨motiveChildR, resolveRightEq, atShiftRightEq⟩ := bindEqSomeIff.mp projRightEq
                  refine ⟨RawTerm.weakenBodyUnderTwoBindersBy innerDepth
                    (natElimDependentSuccBranchType motiveBodyR), ?_, ?_⟩
                  · exact bindEqSomeIff.mpr ⟨motiveChildR, resolveRightEq,
                      bindEqSomeIff.mpr ⟨motiveBodyR, atShiftRightEq, rfl⟩⟩
                  · rw [(Option.some.inj weakEq).symm]
                    refine StepStar.weakenBodyUnderTwoBindersByStar ?_ innerDepth
                    unfold natElimDependentSuccBranchType; exact StepStar.subst _ motiveStepStar
      | injectionBranchCodomain injHead motiveRef =>
          cases depth with
          | zero => exact absurd projEq (by intro h; cases h)
          | succ innerDepth =>
              obtain ⟨motiveChildL, resolveEq, restEq⟩ := bindEqSomeIff.mp projEq
              obtain ⟨motiveBodyL, atShiftEq, restEq2⟩ := bindEqSomeIff.mp restEq
              have projInput : (resolveChildRef? argsLeft paramsLeft motiveRef).bind ScopedChild.atShiftOne?
                  = some motiveBodyL := by rw [resolveEq]; exact atShiftEq
              obtain ⟨motiveBodyR, projRightEq, motiveStepStar⟩ :=
                resolveProjectShiftStarOne argsStepStar paramsStepStar motiveRef projInput
              obtain ⟨motiveChildR, resolveRightEq, atShiftRightEq⟩ := bindEqSomeIff.mp projRightEq
              split at restEq2
              · rename_i hcond; subst hcond
                rw [(Option.some.inj restEq2).symm]
                exact ⟨RawTerm.weakenBodyUnderOneBinderBy innerDepth
                    (optionMatchDependentSomeBranchCodomain motiveBodyR),
                  bindEqSomeIff.mpr ⟨motiveChildR, resolveRightEq,
                    bindEqSomeIff.mpr ⟨motiveBodyR, atShiftRightEq, rfl⟩⟩,
                  StepStar.weakenBodyUnderOneBinderByStar
                    (by unfold optionMatchDependentSomeBranchCodomain; exact StepStar.subst _ motiveStepStar) innerDepth⟩
              · split at restEq2
                · rename_i hcond; subst hcond
                  rw [(Option.some.inj restEq2).symm]
                  exact ⟨RawTerm.weakenBodyUnderOneBinderBy innerDepth
                      (eitherMatchDependentInlBranchCodomain motiveBodyR),
                    bindEqSomeIff.mpr ⟨motiveChildR, resolveRightEq,
                      bindEqSomeIff.mpr ⟨motiveBodyR, atShiftRightEq, rfl⟩⟩,
                    StepStar.weakenBodyUnderOneBinderByStar
                      (by unfold eitherMatchDependentInlBranchCodomain; exact StepStar.subst _ motiveStepStar) innerDepth⟩
                · split at restEq2
                  · rename_i hcond; subst hcond
                    rw [(Option.some.inj restEq2).symm]
                    exact ⟨RawTerm.weakenBodyUnderOneBinderBy innerDepth
                        (eitherMatchDependentInrBranchCodomain motiveBodyR),
                      bindEqSomeIff.mpr ⟨motiveChildR, resolveRightEq,
                        bindEqSomeIff.mpr ⟨motiveBodyR, atShiftRightEq, rfl⟩⟩,
                      StepStar.weakenBodyUnderOneBinderByStar
                        (by unfold eitherMatchDependentInrBranchCodomain; exact StepStar.subst _ motiveStepStar) innerDepth⟩
                  · exact absurd restEq2 (by intro h; cases h)
      | listConsBranchType motiveRef elementTypeRef =>
          obtain ⟨motiveChildL, resolveEq, restEq1⟩ := bindEqSomeIff.mp projEq
          obtain ⟨motiveBodyL, atShiftMEq, restEq2⟩ := bindEqSomeIff.mp restEq1
          obtain ⟨eltChildL, resolveEEq, restEq3⟩ := bindEqSomeIff.mp restEq2
          obtain ⟨eltL, atShiftEEq, weakEq⟩ := bindEqSomeIff.mp restEq3
          have projInputM : (resolveChildRef? argsLeft paramsLeft motiveRef).bind ScopedChild.atShiftOne?
              = some motiveBodyL := by rw [resolveEq]; exact atShiftMEq
          have projInputE : (resolveChildRef? argsLeft paramsLeft elementTypeRef).bind ScopedChild.atShiftZero?
              = some eltL := by rw [resolveEEq]; exact atShiftEEq
          obtain ⟨motiveBodyR, projRightMEq, motiveStepStar⟩ :=
            resolveProjectShiftStarOne argsStepStar paramsStepStar motiveRef projInputM
          obtain ⟨eltR, projRightEEq, eltStepStar⟩ := resolveProjectShiftStarZero argsStepStar paramsStepStar elementTypeRef projInputE
          obtain ⟨motiveChildR, resolveRightMEq, atShiftRightMEq⟩ := bindEqSomeIff.mp projRightMEq
          obtain ⟨eltChildR, resolveRightEEq, atShiftRightEEq⟩ := bindEqSomeIff.mp projRightEEq
          refine ⟨RawTerm.weakenBy depth (listElimDependentConsBranchType motiveBodyR eltR), ?_, ?_⟩
          · exact bindEqSomeIff.mpr ⟨motiveChildR, resolveRightMEq,
              bindEqSomeIff.mpr ⟨motiveBodyR, atShiftRightMEq,
                bindEqSomeIff.mpr ⟨eltChildR, resolveRightEEq,
                  bindEqSomeIff.mpr ⟨eltR, atShiftRightEEq, rfl⟩⟩⟩⟩
          · rw [(Option.some.inj weakEq).symm]
            exact StepStar.weakenByStar (listElimDependentConsBranchType_stepStable motiveStepStar eltStepStar) depth

/-- The generic directed type-SR over a `CellTemplateSpine` (a `builtGen` node's children).  Mutual with
`templateStepStarUnderChildStep`; structural on the spine. -/
theorem spineStepStarUnderChildStep {argShifts paramShifts : List Nat} {scope : Nat}
    {argsLeft argsRight : RawTermChildren argShifts scope}
    {paramsLeft paramsRight : RawTermChildren paramShifts scope}
    (argsStepStar : StepStarChildren argsLeft argsRight)
    (paramsStepStar : StepStarChildren paramsLeft paramsRight)
    (levels : List LevelExpr) (level0 level1 carrierLevel : LevelExpr) (flag : UniverseFlag) :
    (depth : Nat) → (childShifts : List Nat) → (spine : CellTemplateSpine) →
    (leftChildren : RawTermChildren childShifts (scope + depth)) →
    interpretSpine? argsLeft paramsLeft levels level0 level1 carrierLevel flag depth childShifts spine
        = some leftChildren →
    ∃ rightChildren,
      interpretSpine? argsRight paramsRight levels level0 level1 carrierLevel flag depth childShifts spine
        = some rightChildren ∧ StepStarChildren leftChildren rightChildren
  | _depth, [], .spineNil, leftChildren, projEq =>
      ⟨leftChildren, projEq, by rw [(Option.some.inj projEq).symm]; exact StepStarChildren.nilS⟩
  | _depth, [], .spineCons _ _, _leftChildren, projEq => by exact absurd projEq (by intro h; cases h)
  | _depth, _ :: _, .spineNil, _leftChildren, projEq => by exact absurd projEq (by intro h; cases h)
  | depth, 0 :: restShifts, .spineCons headTemplate restTemplates, leftChildren, projEq => by
      obtain ⟨headTermL, headEq, restEq⟩ := bindEqSomeIff.mp projEq
      obtain ⟨restChildrenL, restRowEq, consEq⟩ := bindEqSomeIff.mp restEq
      obtain ⟨headTermR, headRightEq, headStepStar⟩ :=
        templateStepStarUnderChildStep argsStepStar paramsStepStar levels level0 level1 carrierLevel flag
          depth headTemplate headTermL headEq
      obtain ⟨restChildrenR, restRowRightEq, restStepStar⟩ :=
        spineStepStarUnderChildStep argsStepStar paramsStepStar levels level0 level1 carrierLevel flag
          depth restShifts restTemplates restChildrenL restRowEq
      refine ⟨RawTermChildren.childCons headTermR restChildrenR, ?_, ?_⟩
      · exact bindEqSomeIff.mpr ⟨headTermR, headRightEq,
          bindEqSomeIff.mpr ⟨restChildrenR, restRowRightEq, rfl⟩⟩
      · rw [(Option.some.inj consEq).symm]; exact StepStarChildren.consS headStepStar restStepStar
  | depth, 1 :: restShifts, .spineCons headTemplate restTemplates, leftChildren, projEq => by
      obtain ⟨headTermL, headEq, restEq⟩ := bindEqSomeIff.mp projEq
      obtain ⟨restChildrenL, restRowEq, consEq⟩ := bindEqSomeIff.mp restEq
      obtain ⟨headTermR, headRightEq, headStepStar⟩ :=
        templateStepStarUnderChildStep argsStepStar paramsStepStar levels level0 level1 carrierLevel flag
          (depth + 1) headTemplate headTermL headEq
      obtain ⟨restChildrenR, restRowRightEq, restStepStar⟩ :=
        spineStepStarUnderChildStep argsStepStar paramsStepStar levels level0 level1 carrierLevel flag
          depth restShifts restTemplates restChildrenL restRowEq
      refine ⟨RawTermChildren.childCons headTermR restChildrenR, ?_, ?_⟩
      · exact bindEqSomeIff.mpr ⟨headTermR, headRightEq,
          bindEqSomeIff.mpr ⟨restChildrenR, restRowRightEq, rfl⟩⟩
      · rw [(Option.some.inj consEq).symm]; exact StepStarChildren.consS headStepStar restStepStar
  | depth, 2 :: restShifts, .spineCons headTemplate restTemplates, leftChildren, projEq => by
      obtain ⟨headTermL, headEq, restEq⟩ := bindEqSomeIff.mp projEq
      obtain ⟨restChildrenL, restRowEq, consEq⟩ := bindEqSomeIff.mp restEq
      obtain ⟨headTermR, headRightEq, headStepStar⟩ :=
        templateStepStarUnderChildStep argsStepStar paramsStepStar levels level0 level1 carrierLevel flag
          (depth + 2) headTemplate headTermL headEq
      obtain ⟨restChildrenR, restRowRightEq, restStepStar⟩ :=
        spineStepStarUnderChildStep argsStepStar paramsStepStar levels level0 level1 carrierLevel flag
          depth restShifts restTemplates restChildrenL restRowEq
      refine ⟨RawTermChildren.childCons headTermR restChildrenR, ?_, ?_⟩
      · exact bindEqSomeIff.mpr ⟨headTermR, headRightEq,
          bindEqSomeIff.mpr ⟨restChildrenR, restRowRightEq, rfl⟩⟩
      · rw [(Option.some.inj consEq).symm]; exact StepStarChildren.consS headStepStar restStepStar
  | _depth, (_ + 3) :: _, .spineCons _ _, _leftChildren, projEq => by exact absurd projEq (by intro h; cases h)

end

end FX1Poly.Typed
