import FX1Poly.Typed.Engine.RuleTables.CellTemplate
import FX1Poly.Core.Rewriting.Conversion.ConvCongruence
import FX1Poly.Core.Rewriting.Conversion.ConvSubstRename
import FX1Poly.Core.Rewriting.Conversion.ConvSubstPair
import FX1Poly.Typed.Metatheory.Universe.ConvCodeInjectivity
import FX1Poly.Typed.Cell.NatElimDependentSuccType
import FX1Poly.Typed.Cell.OptionMatchDependentSomeBranchType
import FX1Poly.Typed.Cell.EitherMatchDependentBranchType
import FX1Poly.Typed.Cell.ListElimDependentConsType

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/TemplateConvUnderChildStep
    — SR-DSL-1: generic Conv-drift over CellTemplate (the unconditional drift keystone)

When a child of a cell steps, the cell's `interpret?`-produced type/classifier DRIFTS to a `Conv`-equal term.
The design lock's keystone: this is UNCONDITIONAL (no SN, no flag-uniqueness) because `Conv := StepStar.Join`,
so every `interpret?` arm lifts a children-level `Conv` to an output `Conv` by the shipped congruences
(`Conv.ofChildren` / `Conv.subst0` / `Conv.substPair` / `Conv.subst` / `Conv.rename` / `Conv.piTyCode_cong`).
ONE induction on `CellTemplate` SUBSUMES the per-row drift corpus (`ElimOutputTypeCongruence` for outputs +
`DependentBranchTypeMotiveCongruence` for branch classifiers): a new eliminator row needs NO new drift lemma.

This file ships the substrate in layers: the weakening-preserves-`Conv` helpers (this section), the
`ConvChildren`-projection-at-shift helpers, then the mutual `templateConvUnderChildStep` / `spineConvUnderChildStep`.

## Zero-axiom

The shipped `Conv` congruences (`Conv.weaken`/`rename`/`subst`/`subst0`/`substPair`/`ofChildren`/`piTyCode_cong`)
over structural `Nat`/`ConvChildren`/`CellTemplate` inductions, with a propext-clean `Option.bind … = some`
deconstruction (`bindEqSomeIff`, since the stdlib `Option.bind_eq_some_iff` carries `propext`+`Quot.sound`) — no
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax

/-! ## Propext-clean `Option.bind … = some` deconstruction

The stdlib `bindEqSomeIff` pulls `propext` + `Quot.sound`; these `cases`/`subst`-based replacements are
axiom-free (the SR-DSL proofs are zero-axiom), and `Iff.intro` is a structure constructor so the packaged `Iff`
stays clean too. -/

/-- Forward (deconstruct) — `cases` on the option, the `none` case refuted by `cases` on `none = some`. -/
theorem optionBindSome_mp {valueType resultType : Type _} {scrutinee : Option valueType}
    {continuation : valueType → Option resultType} {result : resultType}
    (bindEq : scrutinee.bind continuation = some result) :
    ∃ value, scrutinee = some value ∧ continuation value = some result := by
  cases scrutinee with
  | none => exact absurd bindEq (by intro impossible; cases impossible)
  | some value => exact ⟨value, rfl, bindEq⟩

/-- Reverse (construct) — `subst` the scrutinee, then `(some _).bind` reduces definitionally. -/
theorem optionBindSome_mpr {valueType resultType : Type _} {scrutinee : Option valueType}
    {continuation : valueType → Option resultType} {value : valueType} {result : resultType}
    (scrutineeEq : scrutinee = some value) (continuationEq : continuation value = some result) :
    scrutinee.bind continuation = some result := by
  subst scrutineeEq; exact continuationEq

/-- The clean `Iff` packaging of the two directions. -/
theorem bindEqSomeIff {valueType resultType : Type _} {scrutinee : Option valueType}
    {continuation : valueType → Option resultType} {result : resultType} :
    scrutinee.bind continuation = some result ↔
      ∃ value, scrutinee = some value ∧ continuation value = some result :=
  ⟨optionBindSome_mp, fun ⟨_, scrutineeEq, continuationEq⟩ => optionBindSome_mpr scrutineeEq continuationEq⟩

/-! ## Weakening preserves `Conv` (the depth-grading substrate) -/

/-- `RawTerm.weakenBy depth` preserves `Conv` — iterated `Conv.weaken` over the depth.  Used by the `childAt`
and `universeCode` arms (which weaken a projected/built term to the current depth). -/
theorem Conv.weakenByConv {scope : Nat} {leftTerm rightTerm : RawTerm scope}
    (convProof : Conv leftTerm rightTerm) :
    (depth : Nat) → Conv (RawTerm.weakenBy depth leftTerm) (RawTerm.weakenBy depth rightTerm)
  | 0 => convProof
  | depth + 1 => Conv.weaken (Conv.weakenByConv convProof depth)

/-- `RawTerm.weakenBodyUnderOneBinderBy depth` preserves `Conv` — iterated `Conv.rename (lift weaken)` keeping
the body's own binder innermost.  Used by the `childBodyAt` and `+1`-macro arms. -/
theorem Conv.weakenBodyUnderOneBinderByConv {scope : Nat} {leftBody rightBody : RawTerm (scope + 1)}
    (convProof : Conv leftBody rightBody) :
    (depth : Nat) →
    Conv (RawTerm.weakenBodyUnderOneBinderBy depth leftBody)
         (RawTerm.weakenBodyUnderOneBinderBy depth rightBody)
  | 0 => convProof
  | depth + 1 =>
      Conv.rename (RawRenaming.lift RawRenaming.weaken)
        (Conv.weakenBodyUnderOneBinderByConv convProof depth)

/-- `RawTerm.weakenBodyUnderTwoBindersBy depth` preserves `Conv` — iterated `Conv.rename (lift (lift weaken))`
keeping both of the body's binders innermost.  Used by the `substPairInto` and `+2`-macro (`natSucc`) arms. -/
theorem Conv.weakenBodyUnderTwoBindersByConv {scope : Nat} {leftBody rightBody : RawTerm (scope + 2)}
    (convProof : Conv leftBody rightBody) :
    (depth : Nat) →
    Conv (RawTerm.weakenBodyUnderTwoBindersBy depth leftBody)
         (RawTerm.weakenBodyUnderTwoBindersBy depth rightBody)
  | 0 => convProof
  | depth + 1 =>
      Conv.rename (RawRenaming.lift (RawRenaming.lift RawRenaming.weaken))
        (Conv.weakenBodyUnderTwoBindersByConv convProof depth)

/-! ## `ConvChildren` projection at a fixed shift (the `childAt` / body-projection substrate)

When two children-vectors are pointwise `Conv`, projecting the same slot at the same binder shift yields
`Conv`-equal terms (and the projection succeeds on the right exactly when it does on the left).  These are the
`atShift{Zero,One,Two}?` analogues the `interpret?` arms read children through. -/

/-- Slot projection at shift 0 respects `ConvChildren`: if the left vector's slot projects (at shift 0) to
`leftProj`, the right vector's same slot projects to a `Conv`-equal `rightProj`.  Induction on the `ConvChildren`
witness, casing the slot then the head shift. -/
theorem ConvChildren.projectShiftZero {argShifts : List Nat} {scope : Nat}
    {vecLeft vecRight : RawTermChildren argShifts scope}
    (vecConv : ConvChildren vecLeft vecRight) :
    (slot : Nat) → {leftProj : RawTerm scope} →
    (scopedChildAt? vecLeft.toScopedChildren slot).bind ScopedChild.atShiftZero? = some leftProj →
    ∃ rightProj,
      (scopedChildAt? vecRight.toScopedChildren slot).bind ScopedChild.atShiftZero? = some rightProj ∧
      Conv leftProj rightProj := by
  induction vecConv with
  | nilC =>
      intro slot leftProj projEq
      cases slot <;> exact absurd projEq (by intro h; cases h)
  | @consC scope shift restShifts headLeft headRight restLeft restRight headConv _ restIH =>
      intro slot leftProj projEq
      cases slot with
      | zero =>
          cases shift with
          | zero =>
              refine ⟨headRight, rfl, ?_⟩
              have leftProjEq : leftProj = headLeft := (Option.some.inj projEq).symm
              rw [leftProjEq]; exact headConv
          | succ _ => exact absurd projEq (by intro h; cases h)
      | succ priorSlot => exact restIH priorSlot projEq

/-- Slot projection at shift 1 (a one-binder body) respects `ConvChildren`.  The shift-1 twin of
`projectShiftZero`; the head shift must be exactly 1 for the projection to succeed. -/
theorem ConvChildren.projectShiftOne {argShifts : List Nat} {scope : Nat}
    {vecLeft vecRight : RawTermChildren argShifts scope}
    (vecConv : ConvChildren vecLeft vecRight) :
    (slot : Nat) → {leftProj : RawTerm (scope + 1)} →
    (scopedChildAt? vecLeft.toScopedChildren slot).bind ScopedChild.atShiftOne? = some leftProj →
    ∃ rightProj,
      (scopedChildAt? vecRight.toScopedChildren slot).bind ScopedChild.atShiftOne? = some rightProj ∧
      Conv leftProj rightProj := by
  induction vecConv with
  | nilC =>
      intro slot leftProj projEq
      cases slot <;> exact absurd projEq (by intro h; cases h)
  | @consC scope shift restShifts headLeft headRight restLeft restRight headConv _ restIH =>
      intro slot leftProj projEq
      cases slot with
      | zero =>
          cases shift with
          | zero => exact absurd projEq (by intro h; cases h)
          | succ priorShift =>
              cases priorShift with
              | zero =>
                  refine ⟨headRight, rfl, ?_⟩
                  have leftProjEq : leftProj = headLeft := (Option.some.inj projEq).symm
                  rw [leftProjEq]; exact headConv
              | succ _ => exact absurd projEq (by intro h; cases h)
      | succ priorSlot => exact restIH priorSlot projEq

/-- Slot projection at shift 2 (a two-binder body) respects `ConvChildren`.  The shift-2 twin; the head shift
must be exactly 2 for the projection to succeed. -/
theorem ConvChildren.projectShiftTwo {argShifts : List Nat} {scope : Nat}
    {vecLeft vecRight : RawTermChildren argShifts scope}
    (vecConv : ConvChildren vecLeft vecRight) :
    (slot : Nat) → {leftProj : RawTerm (scope + 2)} →
    (scopedChildAt? vecLeft.toScopedChildren slot).bind ScopedChild.atShiftTwo? = some leftProj →
    ∃ rightProj,
      (scopedChildAt? vecRight.toScopedChildren slot).bind ScopedChild.atShiftTwo? = some rightProj ∧
      Conv leftProj rightProj := by
  induction vecConv with
  | nilC =>
      intro slot leftProj projEq
      cases slot <;> exact absurd projEq (by intro h; cases h)
  | @consC scope shift restShifts headLeft headRight restLeft restRight headConv _ restIH =>
      intro slot leftProj projEq
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
                      refine ⟨headRight, rfl, ?_⟩
                      have leftProjEq : leftProj = headLeft := (Option.some.inj projEq).symm
                      rw [leftProjEq]; exact headConv
                  | succ _ => exact absurd projEq (by intro h; cases h)
      | succ priorSlot => exact restIH priorSlot projEq

/-! ## `resolveChildRef?` projection agreement (dispatching arg/param vectors)

`interpret?` reads children via `resolveChildRef?` (which routes `argChild` to `args`, `paramChild` to
`params`) followed by an `atShift{Zero,One,Two}?`.  Given `ConvChildren` on BOTH vectors, the resolved
projection respects `Conv` — by `cases` on the `ChildRef`, dispatching to the right vector's `projectShift…`. -/

/-- Shift-0 resolved-projection agreement. -/
theorem resolveProjectShiftZero {argShifts paramShifts : List Nat} {scope : Nat}
    {argsLeft argsRight : RawTermChildren argShifts scope}
    {paramsLeft paramsRight : RawTermChildren paramShifts scope}
    (argsConv : ConvChildren argsLeft argsRight) (paramsConv : ConvChildren paramsLeft paramsRight)
    (childReference : ChildRef) {leftProj : RawTerm scope}
    (projEq : (resolveChildRef? argsLeft paramsLeft childReference).bind ScopedChild.atShiftZero? = some leftProj) :
    ∃ rightProj,
      (resolveChildRef? argsRight paramsRight childReference).bind ScopedChild.atShiftZero? = some rightProj ∧
      Conv leftProj rightProj := by
  cases childReference with
  | argChild slot => exact ConvChildren.projectShiftZero argsConv slot projEq
  | paramChild slot => exact ConvChildren.projectShiftZero paramsConv slot projEq

/-- Shift-1 resolved-projection agreement. -/
theorem resolveProjectShiftOne {argShifts paramShifts : List Nat} {scope : Nat}
    {argsLeft argsRight : RawTermChildren argShifts scope}
    {paramsLeft paramsRight : RawTermChildren paramShifts scope}
    (argsConv : ConvChildren argsLeft argsRight) (paramsConv : ConvChildren paramsLeft paramsRight)
    (childReference : ChildRef) {leftProj : RawTerm (scope + 1)}
    (projEq : (resolveChildRef? argsLeft paramsLeft childReference).bind ScopedChild.atShiftOne? = some leftProj) :
    ∃ rightProj,
      (resolveChildRef? argsRight paramsRight childReference).bind ScopedChild.atShiftOne? = some rightProj ∧
      Conv leftProj rightProj := by
  cases childReference with
  | argChild slot => exact ConvChildren.projectShiftOne argsConv slot projEq
  | paramChild slot => exact ConvChildren.projectShiftOne paramsConv slot projEq

/-- Shift-2 resolved-projection agreement. -/
theorem resolveProjectShiftTwo {argShifts paramShifts : List Nat} {scope : Nat}
    {argsLeft argsRight : RawTermChildren argShifts scope}
    {paramsLeft paramsRight : RawTermChildren paramShifts scope}
    (argsConv : ConvChildren argsLeft argsRight) (paramsConv : ConvChildren paramsLeft paramsRight)
    (childReference : ChildRef) {leftProj : RawTerm (scope + 2)}
    (projEq : (resolveChildRef? argsLeft paramsLeft childReference).bind ScopedChild.atShiftTwo? = some leftProj) :
    ∃ rightProj,
      (resolveChildRef? argsRight paramsRight childReference).bind ScopedChild.atShiftTwo? = some rightProj ∧
      Conv leftProj rightProj := by
  cases childReference with
  | argChild slot => exact ConvChildren.projectShiftTwo argsConv slot projEq
  | paramChild slot => exact ConvChildren.projectShiftTwo paramsConv slot projEq

/-! ## Branch-type Conv-congruence in BOTH arguments (the `listConsBranchType` macro arm) -/

/-- `listElimDependentConsBranchType` is `Conv`-stable in BOTH the motive and the element type — the both-argument
generalization of the shipped motive-only `…_isConvStableUnderMotiveStep`.  The three nested `piTyCodeCell`s lift
componentwise: the element-type domain by `eltConv`, the weakened `listTypeCell` domain by `Conv.weaken eltConv`,
and the two motive re-basings by `Conv.subst _ motiveConv`. -/
theorem listElimDependentConsBranchType_convStable {scope : Nat}
    {motiveLeft motiveRight : RawTerm (scope + 1)} {eltLeft eltRight : RawTerm scope}
    (motiveConv : Conv motiveLeft motiveRight) (eltConv : Conv eltLeft eltRight) :
    Conv (listElimDependentConsBranchType motiveLeft eltLeft)
         (listElimDependentConsBranchType motiveRight eltRight) := by
  unfold listElimDependentConsBranchType
  refine Conv.piTyCode_cong eltConv (Conv.piTyCode_cong ?_ (Conv.piTyCode_cong ?_ ?_))
  · exact Conv.ofChildren (ConvChildren.consC (Conv.weaken eltConv) ConvChildren.nilC)
  · unfold listElimDependentRecBinderType; exact Conv.subst _ motiveConv
  · unfold listElimDependentConsBranchCodomain; exact Conv.subst _ motiveConv

/-! ## SR-DSL-1 ★ the generic Conv-drift master (`templateConvUnderChildStep`)

When the cell's children (`args`) and type-index params drift pointwise `Conv` (the congruence-SR situation: one
child of the subject steps, the rest fixed → all pointwise `Conv` via `Conv.refl`/`Conv.fromStep`), the
`interpret?`-produced type/classifier drifts to a `Conv`-equal term.  ONE mutual induction on `CellTemplate` /
`CellTemplateSpine` — every arm a single dispatch to a shipped congruence.  SUBSUMES the per-row drift corpus. -/

mutual

/-- The generic Conv-drift over a `CellTemplate` (existential form: if the left interpretation succeeds, the right
succeeds at a `Conv`-equal term).  Mutual with `spineConvUnderChildStep`; structural recursion on the template. -/
theorem templateConvUnderChildStep {argShifts paramShifts : List Nat} {scope : Nat}
    {argsLeft argsRight : RawTermChildren argShifts scope}
    {paramsLeft paramsRight : RawTermChildren paramShifts scope}
    (argsConv : ConvChildren argsLeft argsRight) (paramsConv : ConvChildren paramsLeft paramsRight)
    (levels : List LevelExpr) (level0 level1 carrierLevel : LevelExpr) (flag : UniverseFlag) :
    (depth : Nat) → (template : CellTemplate) → (leftTerm : RawTerm (scope + depth)) →
    CellTemplate.interpret? argsLeft paramsLeft levels level0 level1 carrierLevel flag depth template = some leftTerm →
    ∃ rightTerm,
      CellTemplate.interpret? argsRight paramsRight levels level0 level1 carrierLevel flag depth template
        = some rightTerm ∧ Conv leftTerm rightTerm
  | depth, .childAt ref, leftTerm, projEq => by
      obtain ⟨childL, resolveEq, restEq⟩ := bindEqSomeIff.mp projEq
      obtain ⟨childTermL, atShiftEq, weakEq⟩ := bindEqSomeIff.mp restEq
      have projInput : (resolveChildRef? argsLeft paramsLeft ref).bind ScopedChild.atShiftZero? = some childTermL := by
        rw [resolveEq]; exact atShiftEq
      obtain ⟨childTermR, projRightEq, childConv⟩ := resolveProjectShiftZero argsConv paramsConv ref projInput
      obtain ⟨childR, resolveRightEq, atShiftRightEq⟩ := bindEqSomeIff.mp projRightEq
      refine ⟨RawTerm.weakenBy depth childTermR, ?_, ?_⟩
      · exact bindEqSomeIff.mpr ⟨childR, resolveRightEq,
          bindEqSomeIff.mpr ⟨childTermR, atShiftRightEq, rfl⟩⟩
      · rw [(Option.some.inj weakEq).symm]; exact Conv.weakenByConv childConv depth
  | depth, .childBodyAt ref, leftTerm, projEq => by
      cases depth with
      | zero => exact absurd projEq (by intro h; cases h)
      | succ innerDepth =>
          obtain ⟨childL, resolveEq, restEq⟩ := bindEqSomeIff.mp projEq
          obtain ⟨childBodyL, atShiftEq, weakEq⟩ := bindEqSomeIff.mp restEq
          have projInput : (resolveChildRef? argsLeft paramsLeft ref).bind ScopedChild.atShiftOne? = some childBodyL := by
            rw [resolveEq]; exact atShiftEq
          obtain ⟨childBodyR, projRightEq, bodyConv⟩ := resolveProjectShiftOne argsConv paramsConv ref projInput
          obtain ⟨childR, resolveRightEq, atShiftRightEq⟩ := bindEqSomeIff.mp projRightEq
          refine ⟨RawTerm.weakenBodyUnderOneBinderBy innerDepth childBodyR, ?_, ?_⟩
          · exact bindEqSomeIff.mpr ⟨childR, resolveRightEq,
              bindEqSomeIff.mpr ⟨childBodyR, atShiftRightEq, rfl⟩⟩
          · rw [(Option.some.inj weakEq).symm]; exact Conv.weakenBodyUnderOneBinderByConv bodyConv innerDepth
  | _depth, .boundVarAt _binderIndex, leftTerm, projEq =>
      ⟨leftTerm, projEq, Conv.refl leftTerm⟩
  | _depth, .universeCode _levelSource _flagSource, leftTerm, projEq =>
      ⟨leftTerm, projEq, Conv.refl leftTerm⟩
  | depth, .builtGen head payloadFamily childTemplates, leftTerm, projEq => by
      obtain ⟨childrenL, spineEq, mkEq⟩ := bindEqSomeIff.mp projEq
      obtain ⟨childrenR, spineRightEq, childrenConv⟩ :=
        spineConvUnderChildStep argsConv paramsConv levels level0 level1 carrierLevel flag
          depth head.binderShifts childTemplates childrenL spineEq
      refine ⟨RawTerm.mkGen head (payloadFamily (scope + depth)) childrenR, ?_, ?_⟩
      · exact bindEqSomeIff.mpr ⟨childrenR, spineRightEq, rfl⟩
      · rw [(Option.some.inj mkEq).symm]; exact Conv.ofChildren childrenConv
  | depth, .subst0Into bodyRef argTemplate, leftTerm, projEq => by
      obtain ⟨argTermL, argEq, restEq1⟩ := bindEqSomeIff.mp projEq
      obtain ⟨bodyChildL, resolveEq, restEq2⟩ := bindEqSomeIff.mp restEq1
      obtain ⟨bodyTermL, atShiftEq, substEq⟩ := bindEqSomeIff.mp restEq2
      obtain ⟨argTermR, argRightEq, argConv⟩ :=
        templateConvUnderChildStep argsConv paramsConv levels level0 level1 carrierLevel flag
          depth argTemplate argTermL argEq
      have projInput : (resolveChildRef? argsLeft paramsLeft bodyRef).bind ScopedChild.atShiftOne? = some bodyTermL := by
        rw [resolveEq]; exact atShiftEq
      obtain ⟨bodyTermR, projRightEq, bodyConv⟩ := resolveProjectShiftOne argsConv paramsConv bodyRef projInput
      obtain ⟨bodyChildR, resolveRightEq, atShiftRightEq⟩ := bindEqSomeIff.mp projRightEq
      refine ⟨RawTerm.subst0 (RawTerm.weakenBodyUnderOneBinderBy depth bodyTermR) argTermR, ?_, ?_⟩
      · exact bindEqSomeIff.mpr ⟨argTermR, argRightEq,
          bindEqSomeIff.mpr ⟨bodyChildR, resolveRightEq,
            bindEqSomeIff.mpr ⟨bodyTermR, atShiftRightEq, rfl⟩⟩⟩
      · rw [(Option.some.inj substEq).symm]
        exact Conv.subst0 (Conv.weakenBodyUnderOneBinderByConv bodyConv depth) argConv
  | depth, .substPairInto bodyRef innerTemplate outerTemplate, leftTerm, projEq => by
      obtain ⟨innerTermL, innerEq, restEq1⟩ := bindEqSomeIff.mp projEq
      obtain ⟨outerTermL, outerEq, restEq2⟩ := bindEqSomeIff.mp restEq1
      obtain ⟨bodyChildL, resolveEq, restEq3⟩ := bindEqSomeIff.mp restEq2
      obtain ⟨bodyTermL, atShiftEq, substEq⟩ := bindEqSomeIff.mp restEq3
      obtain ⟨innerTermR, innerRightEq, innerConv⟩ :=
        templateConvUnderChildStep argsConv paramsConv levels level0 level1 carrierLevel flag
          depth innerTemplate innerTermL innerEq
      obtain ⟨outerTermR, outerRightEq, outerConv⟩ :=
        templateConvUnderChildStep argsConv paramsConv levels level0 level1 carrierLevel flag
          depth outerTemplate outerTermL outerEq
      have projInput : (resolveChildRef? argsLeft paramsLeft bodyRef).bind ScopedChild.atShiftTwo? = some bodyTermL := by
        rw [resolveEq]; exact atShiftEq
      obtain ⟨bodyTermR, projRightEq, bodyConv⟩ := resolveProjectShiftTwo argsConv paramsConv bodyRef projInput
      obtain ⟨bodyChildR, resolveRightEq, atShiftRightEq⟩ := bindEqSomeIff.mp projRightEq
      refine ⟨RawTerm.substPair (RawTerm.weakenBodyUnderTwoBindersBy depth bodyTermR) innerTermR outerTermR, ?_, ?_⟩
      · exact bindEqSomeIff.mpr ⟨innerTermR, innerRightEq,
          bindEqSomeIff.mpr ⟨outerTermR, outerRightEq,
            bindEqSomeIff.mpr ⟨bodyChildR, resolveRightEq,
              bindEqSomeIff.mpr ⟨bodyTermR, atShiftRightEq, rfl⟩⟩⟩⟩
      · rw [(Option.some.inj substEq).symm]
        exact Conv.substPair (Conv.weakenBodyUnderTwoBindersByConv bodyConv depth) innerConv outerConv
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
                  obtain ⟨motiveBodyR, projRightEq, motiveConv⟩ :=
                    resolveProjectShiftOne argsConv paramsConv motiveRef projInput
                  obtain ⟨motiveChildR, resolveRightEq, atShiftRightEq⟩ := bindEqSomeIff.mp projRightEq
                  refine ⟨RawTerm.weakenBodyUnderTwoBindersBy innerDepth
                    (natElimDependentSuccBranchType motiveBodyR), ?_, ?_⟩
                  · exact bindEqSomeIff.mpr ⟨motiveChildR, resolveRightEq,
                      bindEqSomeIff.mpr ⟨motiveBodyR, atShiftRightEq, rfl⟩⟩
                  · rw [(Option.some.inj weakEq).symm]
                    refine Conv.weakenBodyUnderTwoBindersByConv ?_ innerDepth
                    unfold natElimDependentSuccBranchType; exact Conv.subst _ motiveConv
      | injectionBranchCodomain injHead motiveRef =>
          cases depth with
          | zero => exact absurd projEq (by intro h; cases h)
          | succ innerDepth =>
              obtain ⟨motiveChildL, resolveEq, restEq⟩ := bindEqSomeIff.mp projEq
              obtain ⟨motiveBodyL, atShiftEq, restEq2⟩ := bindEqSomeIff.mp restEq
              have projInput : (resolveChildRef? argsLeft paramsLeft motiveRef).bind ScopedChild.atShiftOne?
                  = some motiveBodyL := by rw [resolveEq]; exact atShiftEq
              obtain ⟨motiveBodyR, projRightEq, motiveConv⟩ :=
                resolveProjectShiftOne argsConv paramsConv motiveRef projInput
              obtain ⟨motiveChildR, resolveRightEq, atShiftRightEq⟩ := bindEqSomeIff.mp projRightEq
              -- the codomain bind was pushed INSIDE the injHead if-chain by the do-notation; nest-split it,
              -- and `subst` the head equality so the if-chain reduces by computation (`rfl`) on both sides
              split at restEq2
              · rename_i hcond; subst hcond
                rw [(Option.some.inj restEq2).symm]
                exact ⟨RawTerm.weakenBodyUnderOneBinderBy innerDepth
                    (optionMatchDependentSomeBranchCodomain motiveBodyR),
                  bindEqSomeIff.mpr ⟨motiveChildR, resolveRightEq,
                    bindEqSomeIff.mpr ⟨motiveBodyR, atShiftRightEq, rfl⟩⟩,
                  Conv.weakenBodyUnderOneBinderByConv
                    (by unfold optionMatchDependentSomeBranchCodomain; exact Conv.subst _ motiveConv) innerDepth⟩
              · split at restEq2
                · rename_i hcond; subst hcond
                  rw [(Option.some.inj restEq2).symm]
                  exact ⟨RawTerm.weakenBodyUnderOneBinderBy innerDepth
                      (eitherMatchDependentInlBranchCodomain motiveBodyR),
                    bindEqSomeIff.mpr ⟨motiveChildR, resolveRightEq,
                      bindEqSomeIff.mpr ⟨motiveBodyR, atShiftRightEq, rfl⟩⟩,
                    Conv.weakenBodyUnderOneBinderByConv
                      (by unfold eitherMatchDependentInlBranchCodomain; exact Conv.subst _ motiveConv) innerDepth⟩
                · split at restEq2
                  · rename_i hcond; subst hcond
                    rw [(Option.some.inj restEq2).symm]
                    exact ⟨RawTerm.weakenBodyUnderOneBinderBy innerDepth
                        (eitherMatchDependentInrBranchCodomain motiveBodyR),
                      bindEqSomeIff.mpr ⟨motiveChildR, resolveRightEq,
                        bindEqSomeIff.mpr ⟨motiveBodyR, atShiftRightEq, rfl⟩⟩,
                      Conv.weakenBodyUnderOneBinderByConv
                        (by unfold eitherMatchDependentInrBranchCodomain; exact Conv.subst _ motiveConv) innerDepth⟩
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
          obtain ⟨motiveBodyR, projRightMEq, motiveConv⟩ :=
            resolveProjectShiftOne argsConv paramsConv motiveRef projInputM
          obtain ⟨eltR, projRightEEq, eltConv⟩ := resolveProjectShiftZero argsConv paramsConv elementTypeRef projInputE
          obtain ⟨motiveChildR, resolveRightMEq, atShiftRightMEq⟩ := bindEqSomeIff.mp projRightMEq
          obtain ⟨eltChildR, resolveRightEEq, atShiftRightEEq⟩ := bindEqSomeIff.mp projRightEEq
          refine ⟨RawTerm.weakenBy depth (listElimDependentConsBranchType motiveBodyR eltR), ?_, ?_⟩
          · exact bindEqSomeIff.mpr ⟨motiveChildR, resolveRightMEq,
              bindEqSomeIff.mpr ⟨motiveBodyR, atShiftRightMEq,
                bindEqSomeIff.mpr ⟨eltChildR, resolveRightEEq,
                  bindEqSomeIff.mpr ⟨eltR, atShiftRightEEq, rfl⟩⟩⟩⟩
          · rw [(Option.some.inj weakEq).symm]
            exact Conv.weakenByConv (listElimDependentConsBranchType_convStable motiveConv eltConv) depth

/-- The generic Conv-drift over a `CellTemplateSpine` (a `builtGen` node's children).  Mutual with
`templateConvUnderChildStep`; structural recursion on the spine. -/
theorem spineConvUnderChildStep {argShifts paramShifts : List Nat} {scope : Nat}
    {argsLeft argsRight : RawTermChildren argShifts scope}
    {paramsLeft paramsRight : RawTermChildren paramShifts scope}
    (argsConv : ConvChildren argsLeft argsRight) (paramsConv : ConvChildren paramsLeft paramsRight)
    (levels : List LevelExpr) (level0 level1 carrierLevel : LevelExpr) (flag : UniverseFlag) :
    (depth : Nat) → (childShifts : List Nat) → (spine : CellTemplateSpine) →
    (leftChildren : RawTermChildren childShifts (scope + depth)) →
    interpretSpine? argsLeft paramsLeft levels level0 level1 carrierLevel flag depth childShifts spine
        = some leftChildren →
    ∃ rightChildren,
      interpretSpine? argsRight paramsRight levels level0 level1 carrierLevel flag depth childShifts spine
        = some rightChildren ∧ ConvChildren leftChildren rightChildren
  | _depth, [], .spineNil, leftChildren, projEq =>
      ⟨leftChildren, projEq, by rw [(Option.some.inj projEq).symm]; exact ConvChildren.nilC⟩
  | _depth, [], .spineCons _ _, _leftChildren, projEq => by exact absurd projEq (by intro h; cases h)
  | _depth, _ :: _, .spineNil, _leftChildren, projEq => by exact absurd projEq (by intro h; cases h)
  | depth, 0 :: restShifts, .spineCons headTemplate restTemplates, leftChildren, projEq => by
      obtain ⟨headTermL, headEq, restEq⟩ := bindEqSomeIff.mp projEq
      obtain ⟨restChildrenL, restRowEq, consEq⟩ := bindEqSomeIff.mp restEq
      obtain ⟨headTermR, headRightEq, headConv⟩ :=
        templateConvUnderChildStep argsConv paramsConv levels level0 level1 carrierLevel flag
          depth headTemplate headTermL headEq
      obtain ⟨restChildrenR, restRowRightEq, restConv⟩ :=
        spineConvUnderChildStep argsConv paramsConv levels level0 level1 carrierLevel flag
          depth restShifts restTemplates restChildrenL restRowEq
      refine ⟨RawTermChildren.childCons headTermR restChildrenR, ?_, ?_⟩
      · exact bindEqSomeIff.mpr ⟨headTermR, headRightEq,
          bindEqSomeIff.mpr ⟨restChildrenR, restRowRightEq, rfl⟩⟩
      · rw [(Option.some.inj consEq).symm]; exact ConvChildren.consC headConv restConv
  | depth, 1 :: restShifts, .spineCons headTemplate restTemplates, leftChildren, projEq => by
      obtain ⟨headTermL, headEq, restEq⟩ := bindEqSomeIff.mp projEq
      obtain ⟨restChildrenL, restRowEq, consEq⟩ := bindEqSomeIff.mp restEq
      obtain ⟨headTermR, headRightEq, headConv⟩ :=
        templateConvUnderChildStep argsConv paramsConv levels level0 level1 carrierLevel flag
          (depth + 1) headTemplate headTermL headEq
      obtain ⟨restChildrenR, restRowRightEq, restConv⟩ :=
        spineConvUnderChildStep argsConv paramsConv levels level0 level1 carrierLevel flag
          depth restShifts restTemplates restChildrenL restRowEq
      refine ⟨RawTermChildren.childCons headTermR restChildrenR, ?_, ?_⟩
      · exact bindEqSomeIff.mpr ⟨headTermR, headRightEq,
          bindEqSomeIff.mpr ⟨restChildrenR, restRowRightEq, rfl⟩⟩
      · rw [(Option.some.inj consEq).symm]; exact ConvChildren.consC headConv restConv
  | depth, 2 :: restShifts, .spineCons headTemplate restTemplates, leftChildren, projEq => by
      obtain ⟨headTermL, headEq, restEq⟩ := bindEqSomeIff.mp projEq
      obtain ⟨restChildrenL, restRowEq, consEq⟩ := bindEqSomeIff.mp restEq
      obtain ⟨headTermR, headRightEq, headConv⟩ :=
        templateConvUnderChildStep argsConv paramsConv levels level0 level1 carrierLevel flag
          (depth + 2) headTemplate headTermL headEq
      obtain ⟨restChildrenR, restRowRightEq, restConv⟩ :=
        spineConvUnderChildStep argsConv paramsConv levels level0 level1 carrierLevel flag
          depth restShifts restTemplates restChildrenL restRowEq
      refine ⟨RawTermChildren.childCons headTermR restChildrenR, ?_, ?_⟩
      · exact bindEqSomeIff.mpr ⟨headTermR, headRightEq,
          bindEqSomeIff.mpr ⟨restChildrenR, restRowRightEq, rfl⟩⟩
      · rw [(Option.some.inj consEq).symm]; exact ConvChildren.consC headConv restConv
  | _depth, (_ + 3) :: _, .spineCons _ _, _leftChildren, projEq => by exact absurd projEq (by intro h; cases h)

end

end FX1Poly.Typed
