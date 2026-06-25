import FX1Poly.Typed.Engine.RuleTables.CellTemplate
import FX1Poly.Core.Rewriting.Conversion.ConvCongruence
import FX1Poly.Core.Rewriting.Conversion.ConvSubstRename
import FX1Poly.Core.Rewriting.Conversion.ConvSubstPair
import FX1Poly.Typed.Metatheory.Universe.ConvCodeInjectivity

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

`Conv.weaken` / `Conv.rename` / `Conv.refl` over structural `Nat`/`ConvChildren` inductions — no `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax

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

end FX1Poly.Typed
