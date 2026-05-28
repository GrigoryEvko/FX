import LeanFX2.Foundation.PolyCell.Core.RawTermFresh

/-! # Foundation/PolyCell/Core/RawTermFreeVars

Computable free-variable support for the v2 raw PolyCell substrate.

The project kernel deliberately avoids importing a host finite-set
library here.  A raw variable set is therefore a characteristic
function over the current scope.  This is enough for closure checks,
fresh-position decisions, and downstream complexity witnesses, while
keeping the code first-principles and auditable.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-- Computable finite support for variables in a fixed scope, encoded
as a characteristic function. -/
def RawVarSet (scope : Nat) : Type :=
  Fin scope → Bool

namespace RawVarSet

/-- Empty variable set. -/
def empty {scope : Nat} : RawVarSet scope :=
  fun _ => false

/-- Singleton variable set. -/
def singleton {scope : Nat} (targetPosition : Fin scope) : RawVarSet scope :=
  fun candidatePosition =>
    if candidatePosition = targetPosition then true else false

/-- Boolean union of two variable sets. -/
def union {scope : Nat}
    (firstSet secondSet : RawVarSet scope) : RawVarSet scope :=
  fun candidatePosition => firstSet candidatePosition || secondSet candidatePosition

/-- Membership as a proposition. -/
def contains {scope : Nat}
    (variableSet : RawVarSet scope) (candidatePosition : Fin scope) : Prop :=
  variableSet candidatePosition = true

/-- Membership is decidable because `RawVarSet` is boolean-valued. -/
instance instDecidableContains {scope : Nat}
    (variableSet : RawVarSet scope) (candidatePosition : Fin scope) :
    Decidable (RawVarSet.contains variableSet candidatePosition) := by
  unfold RawVarSet.contains
  exact inferInstance

/-- Raise a parent-scope variable position through `binderShift`
fresh child binders. -/
def raiseParentPosition {scope : Nat} (binderShift : Nat)
    (parentPosition : Fin scope) : Fin (scope + binderShift) :=
  Fin.cast (Nat.add_comm binderShift scope)
    (Fin.natAdd binderShift parentPosition)

/-- Pull a child variable set back to the parent scope.  A parent
position is free in the child contribution exactly when its raised
position is free in the child. -/
def fromChild {scope : Nat} (binderShift : Nat)
    (childSet : RawVarSet (scope + binderShift)) : RawVarSet scope :=
  fun parentPosition =>
    childSet (RawVarSet.raiseParentPosition binderShift parentPosition)

/-- Empty-set membership is impossible. -/
theorem contains_empty_false {scope : Nat} (candidatePosition : Fin scope) :
    RawVarSet.contains RawVarSet.empty candidatePosition → False := by
  intro containsEmpty
  cases containsEmpty

/-- Singleton membership is equality with the singleton target. -/
theorem contains_singleton_iff {scope : Nat}
    (targetPosition candidatePosition : Fin scope) :
    RawVarSet.contains (RawVarSet.singleton targetPosition)
        candidatePosition ↔
      candidatePosition = targetPosition := by
  unfold RawVarSet.contains RawVarSet.singleton
  by_cases positionsEqual : candidatePosition = targetPosition
  · rw [if_pos positionsEqual]
    exact ⟨fun _ => positionsEqual, fun _ => rfl⟩
  · rw [if_neg positionsEqual]
    constructor
    · intro falseEq
      cases falseEq
    · intro candidateEq
      exact False.elim (positionsEqual candidateEq)

/-- Union membership is disjunction of membership in either side. -/
theorem contains_union_iff {scope : Nat}
    (firstSet secondSet : RawVarSet scope) (candidatePosition : Fin scope) :
    RawVarSet.contains (RawVarSet.union firstSet secondSet)
        candidatePosition ↔
      RawVarSet.contains firstSet candidatePosition ∨
        RawVarSet.contains secondSet candidatePosition := by
  unfold RawVarSet.contains RawVarSet.union
  cases firstValue : firstSet candidatePosition <;>
    cases secondValue : secondSet candidatePosition
  · constructor
    · intro falseEq
      cases falseEq
    · intro eitherContains
      cases eitherContains with
      | inl firstContains =>
          cases firstContains
      | inr secondContains =>
          cases secondContains
  · constructor
    · intro _containsUnion
      exact Or.inr rfl
    · intro _eitherContains
      rfl
  · constructor
    · intro _containsUnion
      exact Or.inl rfl
    · intro _eitherContains
      rfl
  · constructor
    · intro _containsUnion
      exact Or.inl rfl
    · intro _eitherContains
      rfl

end RawVarSet

mutual

/-- Computable free-variable set for a raw term. -/
def RawTerm.freeVars {scope : Nat} (sourceTerm : RawTerm scope) :
    RawVarSet scope :=
  match sourceTerm with
  | .mkGen generator payload children =>
      if generatorIsVar : generator = .gen_var then
        let variablePosition : Fin scope :=
          Eq.rec
            (motive := fun targetGenerator _generatorEq =>
              Generator.payload targetGenerator scope)
            payload generatorIsVar
        RawVarSet.singleton variablePosition
      else
        RawTermChildren.freeVars children

/-- Computable free-variable set for a raw child spine.  Child heads
live under their own binder shifts, so the child contribution is pulled
back to parent scope through `RawVarSet.fromChild`. -/
def RawTermChildren.freeVars {binderShifts : List Nat} {scope : Nat}
    (sourceChildren : RawTermChildren binderShifts scope) :
    RawVarSet scope :=
  match binderShifts, sourceChildren with
  | [], .childNil => RawVarSet.empty
  | binderShift :: _, .childCons childHead childTail =>
      RawVarSet.union
        (RawVarSet.fromChild binderShift (RawTerm.freeVars childHead))
        (RawTermChildren.freeVars childTail)

end

mutual

/-- Structural free-use predicate for raw terms. -/
def RawTerm.UsesPosition {scope : Nat}
    (sourceTerm : RawTerm scope) (candidatePosition : Fin scope) : Prop :=
  match sourceTerm with
  | .mkGen generator payload children =>
      if generatorIsVar : generator = .gen_var then
        let variablePosition : Fin scope :=
          Eq.rec
            (motive := fun targetGenerator _generatorEq =>
              Generator.payload targetGenerator scope)
            payload generatorIsVar
        candidatePosition = variablePosition
      else
        RawTermChildren.UsesPosition children candidatePosition

/-- Structural free-use predicate for raw child spines. -/
def RawTermChildren.UsesPosition {binderShifts : List Nat} {scope : Nat}
    (sourceChildren : RawTermChildren binderShifts scope)
    (candidatePosition : Fin scope) : Prop :=
  match binderShifts, sourceChildren with
  | [], .childNil => False
  | binderShift :: _, .childCons childHead childTail =>
      RawTerm.UsesPosition childHead
          (RawVarSet.raiseParentPosition binderShift candidatePosition) ∨
        RawTermChildren.UsesPosition childTail candidatePosition

end

/-- Non-variable generators compute free variables from their child
spine.  The impossible variable arm is discharged explicitly so the
main structural theorem does not duplicate the generator split. -/
theorem RawTerm.freeVars_nonVar
    {scope : Nat} {generator : Generator}
    (generatorIsNotVar : generator ≠ .gen_var)
    (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) :
    RawTerm.freeVars (.mkGen generator payload children) =
      RawTermChildren.freeVars children := by
  dsimp only [RawTerm.freeVars]
  rw [dif_neg generatorIsNotVar]

/-- Non-variable structural use is exactly structural use in the child
spine. -/
theorem RawTerm.usesPosition_nonVar_iff
    {scope : Nat} {generator : Generator}
    (generatorIsNotVar : generator ≠ .gen_var)
    (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope)
    (candidatePosition : Fin scope) :
    RawTerm.UsesPosition (.mkGen generator payload children)
        candidatePosition ↔
      RawTermChildren.UsesPosition children candidatePosition := by
  dsimp only [RawTerm.UsesPosition]
  rw [dif_neg generatorIsNotVar]

mutual

/-- The computable free-variable set is sound and complete for the
structural free-use predicate on raw terms. -/
theorem RawTerm.freeVars_iff_uses {scope : Nat}
    (sourceTerm : RawTerm scope) (candidatePosition : Fin scope) :
    RawVarSet.contains (RawTerm.freeVars sourceTerm) candidatePosition ↔
      RawTerm.UsesPosition sourceTerm candidatePosition := by
  match sourceTerm with
  | .mkGen generator payload children =>
      by_cases generatorIsVar : generator = .gen_var
      · subst generator
        cases children
        dsimp only [RawTerm.freeVars]
        rw [dif_pos rfl]
        change
          RawVarSet.contains (RawVarSet.singleton payload)
              candidatePosition ↔
            candidatePosition = payload
        exact RawVarSet.contains_singleton_iff payload candidatePosition
      · rw [RawTerm.freeVars_nonVar generatorIsVar payload children]
        constructor
        · intro containsChildren
          exact (RawTerm.usesPosition_nonVar_iff generatorIsVar payload
            children candidatePosition).mpr
            ((RawTermChildren.freeVars_iff_uses children
              candidatePosition).mp containsChildren)
        · intro usesSource
          exact (RawTermChildren.freeVars_iff_uses children
            candidatePosition).mpr
            ((RawTerm.usesPosition_nonVar_iff generatorIsVar payload
              children candidatePosition).mp usesSource)

/-- The computable free-variable set is sound and complete for the
structural free-use predicate on raw child spines. -/
theorem RawTermChildren.freeVars_iff_uses {binderShifts : List Nat}
    {scope : Nat} (sourceChildren : RawTermChildren binderShifts scope)
    (candidatePosition : Fin scope) :
    RawVarSet.contains (RawTermChildren.freeVars sourceChildren)
        candidatePosition ↔
      RawTermChildren.UsesPosition sourceChildren candidatePosition := by
  match binderShifts, sourceChildren with
  | [], .childNil =>
      change
        RawVarSet.contains RawVarSet.empty candidatePosition ↔ False
      dsimp only [RawVarSet.contains, RawVarSet.empty]
      constructor
      · intro falseEq
        cases falseEq
      · intro impossibleUse
        cases impossibleUse
  | binderShift :: _, .childCons childHead childTail =>
      change
        RawVarSet.contains
            (RawVarSet.union
              (RawVarSet.fromChild binderShift
                (RawTerm.freeVars childHead))
              (RawTermChildren.freeVars childTail))
            candidatePosition ↔
          (RawTerm.UsesPosition childHead
              (RawVarSet.raiseParentPosition binderShift
                candidatePosition) ∨
            RawTermChildren.UsesPosition childTail candidatePosition)
      have containsUnionIff :=
        RawVarSet.contains_union_iff
          (RawVarSet.fromChild binderShift (RawTerm.freeVars childHead))
          (RawTermChildren.freeVars childTail)
          candidatePosition
      constructor
      · intro containsUnion
        have containsHeadOrTail := containsUnionIff.mp containsUnion
        cases containsHeadOrTail with
        | inl containsHead =>
            exact Or.inl
              ((RawTerm.freeVars_iff_uses childHead
                  (RawVarSet.raiseParentPosition binderShift
                    candidatePosition)).mp
                  containsHead)
        | inr containsTail =>
            exact Or.inr
              ((RawTermChildren.freeVars_iff_uses childTail
                  candidatePosition).mp containsTail)
      · intro usesPosition
        cases usesPosition with
        | inl headUses =>
            exact containsUnionIff.mpr (Or.inl
              ((RawTerm.freeVars_iff_uses childHead
                (RawVarSet.raiseParentPosition binderShift
                  candidatePosition)).mpr
                headUses))
        | inr tailUses =>
            exact containsUnionIff.mpr (Or.inr
              ((RawTermChildren.freeVars_iff_uses childTail
                candidatePosition).mpr tailUses))

end

/-- Unit has no free variable in any scope. -/
theorem RawTerm.freeVars_unit_smoke {scope : Nat}
    (candidatePosition : Fin scope) :
    RawVarSet.contains
        (RawTerm.freeVars
          (.mkGen .gen_unit () .childNil : RawTerm scope))
        candidatePosition → False := by
  intro impossiblePosition
  have generatorIsNotVar : Generator.gen_unit ≠ .gen_var := by
    intro generatorEq
    cases generatorEq
  have usesPosition :=
    (RawTerm.freeVars_iff_uses
      (.mkGen .gen_unit () .childNil : RawTerm scope)
      candidatePosition).mp impossiblePosition
  have childUses :
      RawTermChildren.UsesPosition
        (.childNil : RawTermChildren [] scope) candidatePosition :=
    (RawTerm.usesPosition_nonVar_iff generatorIsNotVar () .childNil
      candidatePosition).mp usesPosition
  dsimp only [RawTermChildren.UsesPosition] at childUses

/-- A variable's free-variable set contains its own payload. -/
theorem RawTerm.freeVars_var_self_smoke {scope : Nat}
    (variablePosition : Fin scope) :
    RawVarSet.contains
      (RawTerm.freeVars
        (.mkGen .gen_var variablePosition .childNil))
      variablePosition := by
  dsimp only [RawTerm.freeVars]
  rw [dif_pos rfl]
  exact (RawVarSet.contains_singleton_iff
    variablePosition variablePosition).mpr rfl

end LeanFX2.Foundation.PolyCell.Core
