import LeanFX2.Foundation.PolyCell.Core.RawTermSubst0Commute
import LeanFX2.Foundation.PolyCell.Core.RawTermSubstRenameCommute

/-! # Foundation/PolyCell/Core/RawTermStrengthen

Eta rules need a computational check that a term in `scope + 1` does
not use the newest variable.  For child spines under binders, the
variable being dropped is lifted past the child binders, so this file
implements strengthening as a lifted partial renaming rather than as a
naive "drop local var 0 everywhere" traversal.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-- Partial renaming for the V2 raw-term substrate.  `none` means that
the source variable cannot be represented in the target scope. -/
def PartialRawRenaming (sourceScope targetScope : Nat) : Type :=
  Fin sourceScope -> Option (Fin targetScope)

namespace PartialRawRenaming

/-- Lift a partial renaming under one binder.  The new binder variable is
preserved; older variables are delegated to the original partial
renaming and shifted when they survive. -/
@[reducible] def lift {sourceScope targetScope : Nat}
    (partialRenaming : PartialRawRenaming sourceScope targetScope) :
    PartialRawRenaming (sourceScope + 1) (targetScope + 1)
  | ⟨0, _⟩ => some ⟨0, Nat.zero_lt_succ targetScope⟩
  | ⟨positionValue + 1, positionBound⟩ =>
      match partialRenaming
          ⟨positionValue, Nat.lt_of_succ_lt_succ positionBound⟩ with
      | some targetPosition => some (Fin.succ targetPosition)
      | none => none

/-- Drop the newest variable from a scope.  Position 0 is rejected;
position `k + 1` lowers to `k`. -/
@[reducible] def dropNewest {scope : Nat} :
    PartialRawRenaming (scope + 1) scope
  | ⟨0, _⟩ => none
  | ⟨positionValue + 1, positionBound⟩ =>
      some ⟨positionValue, Nat.lt_of_succ_lt_succ positionBound⟩

/-- Partial renamings lift through raw binders. -/
instance instLiftsRawPartialRawRenaming : LiftsRaw PartialRawRenaming where
  liftForRaw := lift

/-- Dropping after weakening recovers the original variable. -/
theorem dropNewest_weaken {scope : Nat} (position : Fin scope) :
    dropNewest (RawRenaming.weaken position) = some position := rfl

/-- Lifting preserves the pointwise survival condition used when a
partial renaming is applied after an ordinary renaming. -/
theorem lift_rename_some
    {sourceScope middleScope targetScope : Nat}
    {sourceRenaming : RawRenaming sourceScope middleScope}
    {targetRenaming : RawRenaming sourceScope targetScope}
    {partialRenaming : PartialRawRenaming middleScope targetScope}
    (renamingSurvives :
      ∀ position,
        partialRenaming (sourceRenaming position) =
          some (targetRenaming position)) :
    ∀ position,
      partialRenaming.lift (sourceRenaming.lift position) =
        some (targetRenaming.lift position)
  | ⟨0, _⟩ => rfl
  | ⟨positionValue + 1, positionBound⟩ => by
      cases sourceRenaming
          ⟨positionValue, Nat.lt_of_succ_lt_succ positionBound⟩ with
      | mk middleValue middleBound =>
          dsimp only [PartialRawRenaming.lift, RawRenaming.lift, Fin.succ]
          rw [renamingSurvives
            ⟨positionValue, Nat.lt_of_succ_lt_succ positionBound⟩]

/-- Iterated binder lifting preserves the pointwise survival condition. -/
theorem iterateLiftRaw_rename_some
    {sourceScope middleScope targetScope : Nat}
    {sourceRenaming : RawRenaming sourceScope middleScope}
    {targetRenaming : RawRenaming sourceScope targetScope}
    {partialRenaming : PartialRawRenaming middleScope targetScope}
    (renamingSurvives :
      ∀ position,
        partialRenaming (sourceRenaming position) =
          some (targetRenaming position))
    (binderDepth : Nat) :
    ∀ position,
      iterateLiftRaw partialRenaming binderDepth
          (iterateLiftRaw sourceRenaming binderDepth position) =
        some (iterateLiftRaw targetRenaming binderDepth position) := by
  induction binderDepth with
  | zero => exact renamingSurvives
  | succ _priorDepth priorIH =>
      exact lift_rename_some priorIH

/-- If a partial renaming result survives, it is in the image of the
forward weakening used by `RawTerm.strengthen`. -/
theorem dropNewest_renamingInjectsBack {scope : Nat} :
    ∀ (intermediatePosition : Fin (scope + 1)) (sourcePosition : Fin scope),
      dropNewest intermediatePosition = some sourcePosition →
        intermediatePosition = RawRenaming.weaken sourcePosition
  | ⟨0, _⟩, _, success => by
      cases success
  | ⟨positionValue + 1, positionBound⟩, sourcePosition, success => by
      injection success with sourceEq
      rw [← sourceEq]
      rfl

/-- The image-inversion condition is stable under binder lifting. -/
theorem lift_renamingInjectsBack
    {sourceScope intermediateScope : Nat}
    {forwardRenaming : RawRenaming sourceScope intermediateScope}
    {partialRenaming : PartialRawRenaming intermediateScope sourceScope}
    (renamingInjectsBack :
      ∀ (intermediatePosition : Fin intermediateScope)
        (sourcePosition : Fin sourceScope),
        partialRenaming intermediatePosition = some sourcePosition →
          intermediatePosition = forwardRenaming sourcePosition) :
    ∀ (intermediatePosition : Fin (intermediateScope + 1))
      (sourcePosition : Fin (sourceScope + 1)),
      partialRenaming.lift intermediatePosition = some sourcePosition →
        intermediatePosition = forwardRenaming.lift sourcePosition
  | ⟨0, _⟩, ⟨0, _⟩, _ => rfl
  | ⟨0, _⟩, ⟨sourceValue + 1, _⟩, success => by
      injection success with finEq
      injection finEq with valueEq
      cases valueEq
  | ⟨intermediateValue + 1, intermediateBound⟩, sourcePosition, success => by
      let priorIntermediate : Fin intermediateScope :=
        ⟨intermediateValue, Nat.lt_of_succ_lt_succ intermediateBound⟩
      cases hInner : partialRenaming priorIntermediate with
      | none =>
          have liftedNone :
              partialRenaming.lift
                  ⟨intermediateValue + 1, intermediateBound⟩ =
                (none : Option (Fin (sourceScope + 1))) := by
            show (match partialRenaming priorIntermediate with
                  | some targetPosition => some (Fin.succ targetPosition)
                  | none => none) = none
            rw [hInner]
          rw [liftedNone] at success
          cases success
      | some priorSource =>
          have liftedSome :
              partialRenaming.lift
                  ⟨intermediateValue + 1, intermediateBound⟩ =
                some (Fin.succ priorSource) := by
            show (match partialRenaming priorIntermediate with
                  | some targetPosition => some (Fin.succ targetPosition)
                  | none => none) = some (Fin.succ priorSource)
            rw [hInner]
          rw [liftedSome] at success
          injection success with sourceEq
          rw [← sourceEq]
          have priorEq :=
            renamingInjectsBack priorIntermediate priorSource hInner
          show (⟨intermediateValue + 1, intermediateBound⟩
              : Fin (intermediateScope + 1)) =
            Fin.succ (forwardRenaming priorSource)
          apply Fin.ext
          exact congrArg (· + 1) (congrArg Fin.val priorEq)

/-- Iterated binder lifting preserves the image-inversion condition. -/
theorem iterateLiftRaw_renamingInjectsBack
    {sourceScope intermediateScope : Nat}
    {forwardRenaming : RawRenaming sourceScope intermediateScope}
    {partialRenaming : PartialRawRenaming intermediateScope sourceScope}
    (renamingInjectsBack :
      ∀ (intermediatePosition : Fin intermediateScope)
        (sourcePosition : Fin sourceScope),
        partialRenaming intermediatePosition = some sourcePosition →
          intermediatePosition = forwardRenaming sourcePosition)
    (binderDepth : Nat) :
    ∀ (intermediatePosition : Fin (intermediateScope + binderDepth))
      (sourcePosition : Fin (sourceScope + binderDepth)),
      iterateLiftRaw partialRenaming binderDepth intermediatePosition =
        some sourcePosition →
        intermediatePosition =
          iterateLiftRaw forwardRenaming binderDepth sourcePosition := by
  induction binderDepth with
  | zero => exact renamingInjectsBack
  | succ _priorDepth priorIH =>
      exact lift_renamingInjectsBack priorIH

end PartialRawRenaming

/-- Iterated lifting of the identity renaming is pointwise identity. -/
theorem iterateLiftRaw_RawRenaming_identity_pointwise {scope : Nat}
    (binderDepth : Nat) :
    RawRenaming.PointwiseEq
      (iterateLiftRaw (RawRenaming.identity (scope := scope)) binderDepth)
      (RawRenaming.identity (scope := scope + binderDepth)) := by
  induction binderDepth with
  | zero => exact RawRenaming.PointwiseEq.refl _
  | succ _priorDepth priorIH =>
      intro position
      match position with
      | ⟨0, _⟩ => rfl
      | ⟨positionValue + 1, positionBound⟩ =>
          let priorPosition : Fin (scope + _priorDepth) :=
            ⟨positionValue, Nat.lt_of_succ_lt_succ positionBound⟩
          show Fin.succ
              (iterateLiftRaw (RawRenaming.identity (scope := scope))
                _priorDepth priorPosition) =
            Fin.succ priorPosition
          rw [priorIH priorPosition]

structure PartialRenameTermResult (targetScope : Nat) where
  hasSucceeded : Bool
  term : RawTerm targetScope

structure PartialRenameChildrenResult (binderShifts : List Nat)
    (targetScope : Nat) where
  hasSucceeded : Bool
  children : RawTermChildren binderShifts targetScope

namespace PartialRenameTermResult

def toOption {targetScope : Nat}
    (result : PartialRenameTermResult targetScope) :
    Option (RawTerm targetScope) :=
  if result.hasSucceeded then some result.term else none

theorem toOption_eq_some
    {targetScope : Nat} {result : PartialRenameTermResult targetScope}
    {term : RawTerm targetScope}
    (success : result.toOption = some term) :
    result.hasSucceeded = true ∧ result.term = term := by
  unfold toOption at success
  cases result with
  | mk hasSucceeded resultTerm =>
      cases hasSucceeded
      · cases success
      · injection success with termEq
        exact ⟨rfl, termEq⟩

end PartialRenameTermResult

namespace PartialRenameChildrenResult

def toOption {targetScope : Nat} {binderShifts : List Nat}
    (result : PartialRenameChildrenResult binderShifts targetScope) :
    Option (RawTermChildren binderShifts targetScope) :=
  if result.hasSucceeded then some result.children else none

theorem toOption_eq_some
    {targetScope : Nat} {binderShifts : List Nat}
    {result : PartialRenameChildrenResult binderShifts targetScope}
    {children : RawTermChildren binderShifts targetScope}
    (success : result.toOption = some children) :
    result.hasSucceeded = true ∧ result.children = children := by
  unfold toOption at success
  cases result with
  | mk hasSucceeded resultChildren =>
      cases hasSucceeded
      · cases success
      · injection success with childrenEq
        exact ⟨rfl, childrenEq⟩

end PartialRenameChildrenResult

mutual

/-- Apply a partial renaming to a V2 raw term, retaining a total
placeholder term for failed branches so the mutual recursion stays
axiom-free. -/
def RawTerm.partialRenameResult {sourceScope targetScope : Nat}
    (partialRenaming : PartialRawRenaming sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope) :
    PartialRenameTermResult targetScope :=
  match sourceTerm with
  | .mkGen generator payload children =>
      if hVar : generator = .gen_var then
        let sourcePosition : Fin sourceScope :=
          Eq.rec (motive := fun targetGenerator _ =>
            Generator.payload targetGenerator sourceScope) payload hVar
        match partialRenaming sourcePosition with
        | some targetPosition =>
            { hasSucceeded := true
              term := .mkGen .gen_var targetPosition .childNil }
        | none =>
            { hasSucceeded := false
              term := .mkGen .gen_unit () .childNil }
      else
        let renamedChildren :=
          RawTermChildren.partialRenameResult partialRenaming children
        let payloadEquality :=
          Generator.payload_scope_invariant_of_not_var
            hVar sourceScope targetScope
        let payloadAtTarget : generator.payload targetScope :=
          payloadEquality ▸ payload
        { hasSucceeded := renamedChildren.hasSucceeded
          term := .mkGen generator payloadAtTarget renamedChildren.children }

/-- Apply a partial renaming to a V2 raw-term children spine, lifting
the partial renaming through each child's binder shift.  Failed
branches retain rebuilt placeholder children so the recursive return
type is a structure rather than an indexed `Option`. -/
def RawTermChildren.partialRenameResult
    {parentSourceScope parentTargetScope : Nat}
    {binderShifts : List Nat}
    (partialRenaming : PartialRawRenaming parentSourceScope parentTargetScope)
    (children : RawTermChildren binderShifts parentSourceScope) :
    PartialRenameChildrenResult binderShifts parentTargetScope :=
  match children with
  | .childNil =>
      { hasSucceeded := true
        children := .childNil }
  | .childCons (shift := headShift) childHead childTail =>
      let renamedHead :=
        RawTerm.partialRenameResult
          (iterateLiftRaw partialRenaming headShift) childHead
      let renamedTail :=
        RawTermChildren.partialRenameResult partialRenaming childTail
      { hasSucceeded := renamedHead.hasSucceeded && renamedTail.hasSucceeded
        children := .childCons renamedHead.term renamedTail.children }

end

/-- Apply a partial renaming to a V2 raw term. -/
def RawTerm.partialRename? {sourceScope targetScope : Nat}
    (partialRenaming : PartialRawRenaming sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope) :
    Option (RawTerm targetScope) :=
  (RawTerm.partialRenameResult partialRenaming sourceTerm).toOption

/-- Apply a partial renaming to a V2 raw-term children spine. -/
def RawTermChildren.partialRename?
    {parentSourceScope parentTargetScope : Nat}
    {binderShifts : List Nat}
    (partialRenaming : PartialRawRenaming parentSourceScope parentTargetScope)
    (children : RawTermChildren binderShifts parentSourceScope) :
    Option (RawTermChildren binderShifts parentTargetScope) :=
  (RawTermChildren.partialRenameResult partialRenaming children).toOption

/-- Drop the newest variable from a raw term when it is unused. -/
@[reducible] def RawTerm.strengthen {scope : Nat}
    (sourceTerm : RawTerm (scope + 1)) : Option (RawTerm scope) :=
  RawTerm.partialRename? PartialRawRenaming.dropNewest sourceTerm

/-- Drop the newest parent-scope variable from a child spine. -/
@[reducible] def RawTermChildren.strengthen {parentScope : Nat}
    {binderShifts : List Nat}
    (children : RawTermChildren binderShifts (parentScope + 1)) :
    Option (RawTermChildren binderShifts parentScope) :=
  RawTermChildren.partialRename? PartialRawRenaming.dropNewest children

mutual

/-- Renaming by identity leaves a V2 raw term unchanged. -/
theorem RawTerm.rename_identity_apply {scope : Nat}
    (sourceTerm : RawTerm scope) :
    RawTerm.rename RawRenaming.identity sourceTerm = sourceTerm := by
  match sourceTerm with
  | .mkGen generator payload children =>
      by_cases hVar : generator = .gen_var
      · subst hVar
        cases children
        rfl
      · dsimp only [RawTerm.rename, fold]
        simp only [dif_neg hVar]
        rw [GenAlgebra.canonical_algebra_eq_mkGen]
        congr 1
        exact RawTermChildren.rename_identity_apply children

/-- Renaming a children spine by identity leaves it unchanged. -/
theorem RawTermChildren.rename_identity_apply {scope : Nat}
    {binderShifts : List Nat}
    (children : RawTermChildren binderShifts scope) :
    RawTermChildren.rename RawRenaming.identity children = children := by
  match binderShifts, children with
  | [], .childNil => rfl
  | headShift :: _, .childCons childHead childTail =>
      show RawTermChildren.childCons
              (RawTerm.rename
                (iterateLiftRaw RawRenaming.identity headShift) childHead)
              (RawTermChildren.rename RawRenaming.identity childTail) =
            RawTermChildren.childCons childHead childTail
      have liftedIdentity :
          RawRenaming.PointwiseEq
            (sourceScope := scope + headShift)
            (targetScope := scope + headShift)
            (iterateLiftRaw (RawRenaming.identity (scope := scope))
              headShift)
            (RawRenaming.identity (scope := scope + headShift)) :=
        iterateLiftRaw_RawRenaming_identity_pointwise
          (scope := scope) headShift
      have headIdentity :
          RawTerm.rename (iterateLiftRaw RawRenaming.identity headShift)
              childHead =
            RawTerm.rename RawRenaming.identity childHead :=
        RawTerm.rename_pointwise liftedIdentity childHead
      rw [headIdentity, RawTerm.rename_identity_apply childHead,
        RawTermChildren.rename_identity_apply childTail]

end

mutual

/-- Result-record form of `RawTerm.partialRename?_rename_some`. -/
theorem RawTerm.partialRenameResult_rename_some
    {sourceScope middleScope targetScope : Nat}
    (sourceTerm : RawTerm sourceScope)
    (sourceRenaming : RawRenaming sourceScope middleScope)
    (targetRenaming : RawRenaming sourceScope targetScope)
    (partialRenaming : PartialRawRenaming middleScope targetScope)
    (renamingSurvives :
      ∀ position,
        partialRenaming (sourceRenaming position) =
          some (targetRenaming position)) :
    RawTerm.partialRenameResult partialRenaming
        (RawTerm.rename sourceRenaming sourceTerm) =
      { hasSucceeded := true
        term := RawTerm.rename targetRenaming sourceTerm } := by
  match sourceTerm with
  | .mkGen generator payload children =>
      by_cases hVar : generator = .gen_var
      · subst hVar
        show RawTerm.partialRenameResult partialRenaming
              (ActsOnRawTermVar.varToRawTerm sourceRenaming payload) =
            { hasSucceeded := true
              term := ActsOnRawTermVar.varToRawTerm targetRenaming payload }
        show RawTerm.partialRenameResult partialRenaming
              (.mkGen .gen_var (sourceRenaming payload) .childNil) =
            { hasSucceeded := true
              term := .mkGen .gen_var (targetRenaming payload) .childNil }
        dsimp only [RawTerm.partialRenameResult]
        rw [dif_pos rfl]
        change
          (match partialRenaming (sourceRenaming payload) with
          | some targetPosition =>
              PartialRenameTermResult.mk true
                (RawTerm.mkGen .gen_var targetPosition .childNil)
          | none =>
              PartialRenameTermResult.mk false
                (RawTerm.mkGen .gen_unit () .childNil)) =
            PartialRenameTermResult.mk true
              (RawTerm.mkGen .gen_var (targetRenaming payload) .childNil)
        rw [renamingSurvives payload]
      · dsimp only [RawTerm.rename, fold]
        simp only [dif_neg hVar]
        rw [GenAlgebra.canonical_algebra_eq_mkGen]
        dsimp only [RawTerm.partialRenameResult]
        simp only [dif_neg hVar]
        have childrenRenameSome :=
          RawTermChildren.partialRenameResult_rename_some children
          sourceRenaming targetRenaming partialRenaming renamingSurvives
        rw [RawTermChildren.rename_eq_foldChildren sourceRenaming children]
          at childrenRenameSome
        rw [RawTermChildren.rename_eq_foldChildren targetRenaming children]
          at childrenRenameSome
        rw [childrenRenameSome]
        rw [GenAlgebra.canonical_algebra_eq_mkGen]
        cases generator <;> try rfl
        exact absurd rfl hVar

/-- Children-spine result-record form of
`RawTerm.partialRename?_rename_some`. -/
theorem RawTermChildren.partialRenameResult_rename_some
    {sourceScope middleScope targetScope : Nat}
    {binderShifts : List Nat}
    (children : RawTermChildren binderShifts sourceScope)
    (sourceRenaming : RawRenaming sourceScope middleScope)
    (targetRenaming : RawRenaming sourceScope targetScope)
    (partialRenaming : PartialRawRenaming middleScope targetScope)
    (renamingSurvives :
      ∀ position,
        partialRenaming (sourceRenaming position) =
          some (targetRenaming position)) :
    RawTermChildren.partialRenameResult partialRenaming
        (RawTermChildren.rename sourceRenaming children) =
      { hasSucceeded := true
        children := RawTermChildren.rename targetRenaming children } := by
  match binderShifts, children with
  | [], .childNil => rfl
  | headShift :: _, .childCons childHead childTail =>
      show
        PartialRenameChildrenResult.mk
            ((RawTerm.partialRenameResult
              (iterateLiftRaw partialRenaming headShift)
              (RawTerm.rename (iterateLiftRaw sourceRenaming headShift)
                childHead)).hasSucceeded &&
            (RawTermChildren.partialRenameResult partialRenaming
              (RawTermChildren.rename sourceRenaming childTail)).hasSucceeded)
            (RawTermChildren.childCons
              (RawTerm.partialRenameResult
                (iterateLiftRaw partialRenaming headShift)
                (RawTerm.rename (iterateLiftRaw sourceRenaming headShift)
                  childHead)).term
              (RawTermChildren.partialRenameResult partialRenaming
                (RawTermChildren.rename sourceRenaming childTail)).children) =
          PartialRenameChildrenResult.mk true
            (RawTermChildren.childCons
              (RawTerm.rename (iterateLiftRaw targetRenaming headShift)
                childHead)
              (RawTermChildren.rename targetRenaming childTail))
      rw [RawTerm.partialRenameResult_rename_some childHead
          (iterateLiftRaw sourceRenaming headShift)
          (iterateLiftRaw targetRenaming headShift)
          (iterateLiftRaw partialRenaming headShift)
          (PartialRawRenaming.iterateLiftRaw_rename_some
            renamingSurvives headShift),
        RawTermChildren.partialRenameResult_rename_some childTail
          sourceRenaming targetRenaming partialRenaming renamingSurvives]
      rfl

end

/-- If all variables produced by a total renaming survive a partial
renaming, the whole renamed term survives and produces the corresponding
target-renamed term. -/
theorem RawTerm.partialRename?_rename_some
    {sourceScope middleScope targetScope : Nat}
    (sourceTerm : RawTerm sourceScope)
    (sourceRenaming : RawRenaming sourceScope middleScope)
    (targetRenaming : RawRenaming sourceScope targetScope)
    (partialRenaming : PartialRawRenaming middleScope targetScope)
    (renamingSurvives :
      ∀ position,
        partialRenaming (sourceRenaming position) =
          some (targetRenaming position)) :
    RawTerm.partialRename? partialRenaming
        (RawTerm.rename sourceRenaming sourceTerm) =
      some (RawTerm.rename targetRenaming sourceTerm) := by
  unfold RawTerm.partialRename?
  rw [RawTerm.partialRenameResult_rename_some sourceTerm sourceRenaming
    targetRenaming partialRenaming renamingSurvives]
  rfl

/-- Children-spine form of `RawTerm.partialRename?_rename_some`. -/
theorem RawTermChildren.partialRename?_rename_some
    {sourceScope middleScope targetScope : Nat}
    {binderShifts : List Nat}
    (children : RawTermChildren binderShifts sourceScope)
    (sourceRenaming : RawRenaming sourceScope middleScope)
    (targetRenaming : RawRenaming sourceScope targetScope)
    (partialRenaming : PartialRawRenaming middleScope targetScope)
    (renamingSurvives :
      ∀ position,
        partialRenaming (sourceRenaming position) =
          some (targetRenaming position)) :
    RawTermChildren.partialRename? partialRenaming
        (RawTermChildren.rename sourceRenaming children) =
      some (RawTermChildren.rename targetRenaming children) := by
  unfold RawTermChildren.partialRename?
  rw [RawTermChildren.partialRenameResult_rename_some children sourceRenaming
    targetRenaming partialRenaming renamingSurvives]
  rfl

mutual

/-- A successful partial renaming reconstructs the original term by
renaming the extracted term through the supplied forward renaming. -/
theorem RawTerm.partialRename?_imp_rename
    {sourceScope intermediateScope : Nat}
    (body : RawTerm intermediateScope)
    (forwardRenaming : RawRenaming sourceScope intermediateScope)
    (partialRenaming : PartialRawRenaming intermediateScope sourceScope)
    (renamingInjectsBack :
      ∀ (intermediatePosition : Fin intermediateScope)
        (sourcePosition : Fin sourceScope),
        partialRenaming intermediatePosition = some sourcePosition →
          intermediatePosition = forwardRenaming sourcePosition)
    (extracted : RawTerm sourceScope)
    (success : RawTerm.partialRename? partialRenaming body = some extracted) :
    RawTerm.rename forwardRenaming extracted = body := by
  match body with
  | .mkGen generator payload children =>
      by_cases hVar : generator = .gen_var
      · subst hVar
        cases children
        unfold RawTerm.partialRename? at success
        have resultFields :=
          PartialRenameTermResult.toOption_eq_some success
        dsimp only [RawTerm.partialRenameResult] at resultFields
        rw [dif_pos rfl] at resultFields
        change
          (match partialRenaming payload with
          | some targetPosition =>
              PartialRenameTermResult.mk true
                (RawTerm.mkGen .gen_var targetPosition .childNil)
          | none =>
              PartialRenameTermResult.mk false
                (RawTerm.mkGen .gen_unit () .childNil)).hasSucceeded =
            true ∧
          (match partialRenaming payload with
          | some targetPosition =>
              PartialRenameTermResult.mk true
                (RawTerm.mkGen .gen_var targetPosition .childNil)
          | none =>
              PartialRenameTermResult.mk false
                (RawTerm.mkGen .gen_unit () .childNil)).term =
            extracted at resultFields
        cases hPartial : partialRenaming payload with
        | none =>
            rw [hPartial] at resultFields
            cases resultFields.left
        | some sourcePosition =>
            rw [hPartial] at resultFields
            rw [← resultFields.right]
            show RawTerm.rename forwardRenaming
                (.mkGen .gen_var sourcePosition .childNil) =
              (.mkGen .gen_var payload .childNil)
            show (.mkGen .gen_var (forwardRenaming sourcePosition)
                .childNil : RawTerm intermediateScope) =
              (.mkGen .gen_var payload .childNil)
            rw [← renamingInjectsBack payload sourcePosition hPartial]
      · unfold RawTerm.partialRename? at success
        have resultFields :=
          PartialRenameTermResult.toOption_eq_some success
        dsimp only [RawTerm.partialRenameResult] at resultFields
        rw [dif_neg hVar] at resultFields
        let childResult :=
          RawTermChildren.partialRenameResult partialRenaming children
        change
          childResult.hasSucceeded = true ∧
          (let payloadEquality :=
            Generator.payload_scope_invariant_of_not_var
              hVar intermediateScope sourceScope
           let payloadAtTarget : generator.payload sourceScope :=
            payloadEquality ▸ payload
           RawTerm.mkGen generator payloadAtTarget childResult.children) =
            extracted at resultFields
        have childSucceeded : childResult.hasSucceeded = true := by
          exact resultFields.left
        have childOption :
            RawTermChildren.partialRename? partialRenaming children =
              some childResult.children := by
          unfold RawTermChildren.partialRename?
          unfold PartialRenameChildrenResult.toOption
          change
            (if childResult.hasSucceeded = true then some childResult.children
              else none) = some childResult.children
          rw [childSucceeded]
          rfl
        have childrenEq :=
          RawTermChildren.partialRename?_imp_rename children
            forwardRenaming partialRenaming renamingInjectsBack
            childResult.children childOption
        rw [← resultFields.right]
        dsimp only [RawTerm.rename, fold]
        simp only [dif_neg hVar]
        rw [GenAlgebra.canonical_algebra_eq_mkGen]
        rw [← RawTermChildren.rename_eq_foldChildren forwardRenaming
          childResult.children]
        rw [childrenEq]
        cases generator <;> try rfl
        exact absurd rfl hVar

/-- Children-spine form of `RawTerm.partialRename?_imp_rename`. -/
theorem RawTermChildren.partialRename?_imp_rename
    {sourceScope intermediateScope : Nat}
    {binderShifts : List Nat}
    (children : RawTermChildren binderShifts intermediateScope)
    (forwardRenaming : RawRenaming sourceScope intermediateScope)
    (partialRenaming : PartialRawRenaming intermediateScope sourceScope)
    (renamingInjectsBack :
      ∀ (intermediatePosition : Fin intermediateScope)
        (sourcePosition : Fin sourceScope),
        partialRenaming intermediatePosition = some sourcePosition →
          intermediatePosition = forwardRenaming sourcePosition)
    (extracted : RawTermChildren binderShifts sourceScope)
    (success :
      RawTermChildren.partialRename? partialRenaming children =
        some extracted) :
    RawTermChildren.rename forwardRenaming extracted = children := by
  match binderShifts, children with
  | [], .childNil =>
      cases extracted
      rfl
  | headShift :: _, .childCons childHead childTail =>
      unfold RawTermChildren.partialRename? at success
      have resultFields :=
        PartialRenameChildrenResult.toOption_eq_some success
      dsimp only [RawTermChildren.partialRenameResult] at resultFields
      let headResult :=
        RawTerm.partialRenameResult
          (iterateLiftRaw partialRenaming headShift) childHead
      let tailResult :=
        RawTermChildren.partialRenameResult partialRenaming childTail
      change
        ((headResult.hasSucceeded && tailResult.hasSucceeded) = true ∧
          RawTermChildren.childCons headResult.term tailResult.children =
            extracted) at resultFields
      have headAndTailSucceeded :
          (headResult.hasSucceeded && tailResult.hasSucceeded) = true := by
        exact resultFields.left
      cases hHeadSucceeded : headResult.hasSucceeded <;>
        rw [hHeadSucceeded] at headAndTailSucceeded
      · cases headAndTailSucceeded
      · cases hTailSucceeded : tailResult.hasSucceeded <;>
          rw [hTailSucceeded] at headAndTailSucceeded
        · cases headAndTailSucceeded
        · have hHead :
              RawTerm.partialRename?
                (iterateLiftRaw partialRenaming headShift) childHead =
                some headResult.term := by
            unfold RawTerm.partialRename?
            unfold PartialRenameTermResult.toOption
            change
              (if headResult.hasSucceeded = true then some headResult.term
                else none) = some headResult.term
            rw [hHeadSucceeded]
            rfl
          have hTail :
              RawTermChildren.partialRename? partialRenaming childTail =
                some tailResult.children := by
            unfold RawTermChildren.partialRename?
            unfold PartialRenameChildrenResult.toOption
            change
              (if tailResult.hasSucceeded = true then some tailResult.children
                else none) = some tailResult.children
            rw [hTailSucceeded]
            rfl
          rw [← resultFields.right]
          show RawTermChildren.childCons
                  (RawTerm.rename
                    (iterateLiftRaw forwardRenaming headShift)
                    headResult.term)
                  (RawTermChildren.rename forwardRenaming
                    tailResult.children) =
                RawTermChildren.childCons childHead childTail
          have headEq :=
            RawTerm.partialRename?_imp_rename childHead
              (iterateLiftRaw forwardRenaming headShift)
              (iterateLiftRaw partialRenaming headShift)
              (PartialRawRenaming.iterateLiftRaw_renamingInjectsBack
                renamingInjectsBack headShift)
              headResult.term hHead
          have tailEq :=
            RawTermChildren.partialRename?_imp_rename childTail
              forwardRenaming partialRenaming renamingInjectsBack
              tailResult.children hTail
          rw [headEq, tailEq]

end

/-- Weakening followed by strengthening recovers the original term. -/
theorem RawTerm.strengthen_weaken {scope : Nat}
    (sourceTerm : RawTerm scope) :
    RawTerm.strengthen (RawTerm.weaken sourceTerm) = some sourceTerm := by
  unfold RawTerm.strengthen RawTerm.weaken
  rw [RawTerm.partialRename?_rename_some sourceTerm
    RawRenaming.weaken RawRenaming.identity
    PartialRawRenaming.dropNewest
    PartialRawRenaming.dropNewest_weaken]
  rw [RawTerm.rename_identity_apply sourceTerm]

/-- Successful strengthening reconstructs the original term by weakening
the extracted term. -/
theorem RawTerm.strengthen_sound {scope : Nat}
    (body : RawTerm (scope + 1)) (extracted : RawTerm scope)
    (success : RawTerm.strengthen body = some extracted) :
    RawTerm.weaken extracted = body := by
  unfold RawTerm.strengthen at success
  unfold RawTerm.weaken
  exact RawTerm.partialRename?_imp_rename body RawRenaming.weaken
    PartialRawRenaming.dropNewest
    PartialRawRenaming.dropNewest_renamingInjectsBack
    extracted success

/-- Strengthening commutes with renaming lifted under the newest slot. -/
theorem RawTerm.strengthen_commutes_rename
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (body : RawTerm (sourceScope + 1)) (extracted : RawTerm sourceScope)
    (success : RawTerm.strengthen body = some extracted) :
    RawTerm.strengthen
        (RawTerm.rename rawRenaming.lift body) =
      some (RawTerm.rename rawRenaming extracted) := by
  have weakenedBody := RawTerm.strengthen_sound body extracted success
  rw [← weakenedBody]
  unfold RawTerm.weaken
  rw [RawTerm.rename_compose RawRenaming.weaken rawRenaming.lift extracted]
  have composedRenamingsAgree :
      RawRenaming.PointwiseEq
        (RawRenaming.compose RawRenaming.weaken rawRenaming.lift)
        (RawRenaming.compose rawRenaming RawRenaming.weaken) := by
    intro position
    exact RawRenaming.weaken_lift_commute rawRenaming position
  rw [RawTerm.rename_pointwise composedRenamingsAgree extracted]
  rw [← RawTerm.rename_compose rawRenaming RawRenaming.weaken extracted]
  exact RawTerm.strengthen_weaken (RawTerm.rename rawRenaming extracted)

/-- A term that strengthens is invariant under singleton substitution. -/
theorem RawTerm.strengthen_commutes_subst0 {scope : Nat}
    (body : RawTerm (scope + 1)) (extracted rawArg : RawTerm scope)
    (success : RawTerm.strengthen body = some extracted) :
    RawTerm.subst0 body rawArg = extracted := by
  have weakenedBody := RawTerm.strengthen_sound body extracted success
  rw [← weakenedBody]
  unfold RawTerm.subst0
  exact RawTerm.weaken_subst_singleton extracted rawArg

end LeanFX2.Foundation.PolyCell.Core
