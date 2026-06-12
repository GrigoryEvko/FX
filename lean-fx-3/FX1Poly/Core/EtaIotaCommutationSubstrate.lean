import FX1Poly.Core.EtaTableOrthogonality
import FX1Poly.Core.StepTable

/-! # EtaIotaCommutationSubstrate — ETA-T5 increment 1: positional
iota steps under shift-checked lookups

The eta/iota quasi-commutation's root-eta case reorders
`introCell → core → target` into a chain of iota steps replacing each
observation's core copy inside the intro cell, capped by one table eta
contraction.  This file ships the positional workhorse: a successful
`childAtShift?` lookup plus a table step on the found child yields a
ONE-STEP spine reduction to a spine that holds the stepped child at
that slot and is untouched everywhere else.

The existential keeps the replaced spine abstract — consumers chain
through the lookup equations, never through a concrete builder.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditEtaIotaCommutationSubstrate.lean`. -/

namespace FX1Poly.Core

/-- **Positional step under a shift-checked lookup**: a table step on a
looked-up child lifts to a one-step spine reduction; the new spine
holds the stepped child at the slot and agrees with the old spine at
every other slot. -/
theorem StepOverTableChildren.ofChildAtShiftStep
    {table : List IotaRuleDesc} {parentScope : Nat} :
    {binderShifts : List Nat} →
    (children : RawTermChildren binderShifts parentScope) →
    (slot expectedShift : Nat) →
    {oldChild newChild : RawTerm (parentScope + expectedShift)} →
    RawTermChildren.childAtShift? children slot expectedShift
      = some oldChild →
    StepOverTable table oldChild newChild →
    ∃ replacedChildren : RawTermChildren binderShifts parentScope,
      StepOverTableChildren table children replacedChildren
      ∧ RawTermChildren.childAtShift? replacedChildren slot expectedShift
          = some newChild
      ∧ ∀ otherSlot otherShift : Nat, otherSlot ≠ slot →
          RawTermChildren.childAtShift? replacedChildren otherSlot
              otherShift
            = RawTermChildren.childAtShift? children otherSlot otherShift
  | _, .childNil, _, _, _, _, lookupEq, _ => nomatch lookupEq
  | headShift :: _restShifts, .childCons head rest, 0, expectedShift,
      oldChild, newChild, lookupEq, childStep => by
      by_cases shiftMatches : headShift = expectedShift
      case pos =>
          have computed :
              RawTermChildren.childAtShift?
                (RawTermChildren.childCons head rest) 0 expectedShift
              = (if shiftEq : headShift = expectedShift then
                  some (shiftEq ▸ head)
                else none) := rfl
          rw [computed, dif_pos shiftMatches] at lookupEq
          have headIsOld : shiftMatches ▸ head = oldChild :=
            Option.some.inj lookupEq
          subst headIsOld
          cases shiftMatches
          refine ⟨RawTermChildren.childCons newChild rest,
            StepOverTableChildren.here rest childStep, ?_, ?_⟩
          · have computedNew :
                RawTermChildren.childAtShift?
                  (RawTermChildren.childCons newChild rest) 0 headShift
                = (if shiftEq : headShift = headShift then
                    some (shiftEq ▸ newChild)
                  else none) := rfl
            rw [computedNew, dif_pos rfl]
          · intro otherSlot otherShift otherIsNotSlot
            match otherSlot with
            | 0 => exact absurd rfl otherIsNotSlot
            | nextSlot + 1 => rfl
      case neg =>
          have computed :
              RawTermChildren.childAtShift?
                (RawTermChildren.childCons head rest) 0 expectedShift
              = (if shiftEq : headShift = expectedShift then
                  some (shiftEq ▸ head)
                else none) := rfl
          rw [computed, dif_neg shiftMatches] at lookupEq
          exact nomatch lookupEq
  | _headShift :: _restShifts, .childCons head rest, nextSlot + 1,
      expectedShift, oldChild, newChild, lookupEq, childStep => by
      obtain ⟨replacedRest, restStep, newLookup, restPreserved⟩ :=
        StepOverTableChildren.ofChildAtShiftStep rest nextSlot
          expectedShift lookupEq childStep
      refine ⟨RawTermChildren.childCons head replacedRest,
        StepOverTableChildren.there head restStep, newLookup, ?_⟩
      intro otherSlot otherShift otherIsNotSlot
      match otherSlot with
      | 0 => rfl
      | otherNext + 1 =>
          exact restPreserved otherNext otherShift
            (fun nextCollides =>
              otherIsNotSlot (congrArg Nat.succ nextCollides))

end FX1Poly.Core
