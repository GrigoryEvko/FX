import FX1Poly.Core.RawSize
import FX1Poly.Core.StepEta

/-! # Foundation/PolyCell/Core/StrongNormalizationEta
    - eta-only accessibility for the raw eta sibling relation

Root eta is easier than beta+iota: every eta constructor strictly
contracts raw size.  This file proves the eta-only well-foundedness
substrate (the harder beta-only-to-betaEta SN transfer is handled
elsewhere).
-/

namespace FX1Poly.Core

-- `RawRenaming` lives in `FX1Poly.Foundation`, which does not enclose
-- `FX1Poly.Core`, so open it explicitly.
open FX1Poly.Foundation

mutual

/-- Renaming preserves raw-term size.  The proof follows the fold
dispatcher: variables rebuild as variables, and non-variable generators
preserve size by recursively preserving their child spine size. -/
theorem RawTerm.size_rename {sourceScope targetScope : Nat}
    (someRenaming : FX1Poly.Foundation.RawRenaming sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope) :
    (RawTerm.rename someRenaming sourceTerm).size = sourceTerm.size := by
  match sourceTerm with
  | .mkGen someGenerator somePayload someChildren =>
      by_cases hVar : someGenerator = .gen_var
      · subst hVar
        cases someChildren
        rfl
      · dsimp only [RawTerm.rename, fold]
        simp only [dif_neg hVar]
        rw [GenAlgebra.canonical_algebra_eq_mkGen]
        dsimp only [RawTerm.size]
        rw [← RawTermChildren.rename_eq_foldChildren someRenaming
          someChildren]
        rw [RawTermChildren.size_rename someRenaming someChildren]

/-- Renaming preserves raw child-spine size. -/
theorem RawTermChildren.size_rename {sourceScope targetScope : Nat}
    {binderShifts : List Nat}
    (someRenaming : FX1Poly.Foundation.RawRenaming sourceScope targetScope)
    (someChildren : RawTermChildren binderShifts sourceScope) :
    (RawTermChildren.rename someRenaming someChildren).size =
      someChildren.size := by
  match binderShifts, someChildren with
  | [], .childNil => rfl
  | headShift :: _, .childCons childHead childTail =>
      show (RawTerm.rename (iterateLiftRaw someRenaming headShift)
            childHead).size +
          (RawTermChildren.rename someRenaming childTail).size + 1 =
        childHead.size + childTail.size + 1
      rw [RawTerm.size_rename (iterateLiftRaw someRenaming headShift)
        childHead]
      rw [RawTermChildren.size_rename someRenaming childTail]

end

/-- Weakening is a renaming, hence preserves raw-term size. -/
theorem RawTerm.size_weaken {scope : Nat} (sourceTerm : RawTerm scope) :
    (RawTerm.weaken sourceTerm).size = sourceTerm.size := by
  rw [RawTerm.weaken_eq_rename]
  exact RawTerm.size_rename RawRenaming.weaken sourceTerm

private theorem lt_etaLamSource_size (sizeValue : Nat) :
    sizeValue < sizeValue + (0 + 1 + 0 + 1) + 1 + 1 + 0 + 1 + 1 := by
  rw [Nat.add_assoc sizeValue (0 + 1 + 0 + 1) 1]
  rw [Nat.add_assoc sizeValue ((0 + 1 + 0 + 1) + 1) 1]
  rw [Nat.add_assoc sizeValue (((0 + 1 + 0 + 1) + 1) + 1) 0]
  rw [Nat.add_assoc sizeValue ((((0 + 1 + 0 + 1) + 1) + 1) + 0) 1]
  rw [Nat.add_assoc sizeValue
    (((((0 + 1 + 0 + 1) + 1) + 1) + 0) + 1) 1]
  exact Nat.lt_add_of_pos_right (Nat.succ_pos _)

private theorem lt_etaLamAnnotatedSource_size
    (annotationSize sizeValue : Nat) :
    sizeValue <
      annotationSize + (sizeValue + (0 + 1 + 0 + 1) + 1 + 1 + 0 + 1) +
        1 + 1 := by
  have innerBound :
      sizeValue < sizeValue + (0 + 1 + 0 + 1) + 1 + 1 + 0 + 1 := by
    rw [Nat.add_assoc sizeValue (0 + 1 + 0 + 1) 1]
    rw [Nat.add_assoc sizeValue ((0 + 1 + 0 + 1) + 1) 1]
    rw [Nat.add_assoc sizeValue (((0 + 1 + 0 + 1) + 1) + 1) 0]
    rw [Nat.add_assoc sizeValue ((((0 + 1 + 0 + 1) + 1) + 1) + 0) 1]
    exact Nat.lt_add_of_pos_right (Nat.succ_pos _)
  exact
    Nat.lt_of_lt_of_le innerBound
      (Nat.le_trans (Nat.le_add_left _ annotationSize)
        (Nat.le_trans (Nat.le_add_right _ 1) (Nat.le_add_right _ 1)))

private theorem lt_etaPairSource_size (sizeValue : Nat) :
    sizeValue <
      sizeValue + 0 + 1 + 1 + (sizeValue + 0 + 1 + 1 + 0 + 1) + 1 + 1 := by
  rw [Nat.add_assoc sizeValue 0 1]
  rw [Nat.add_assoc sizeValue (0 + 1) 1]
  rw [Nat.add_assoc sizeValue ((0 + 1) + 1)
    (sizeValue + 0 + 1 + 1 + 0 + 1)]
  rw [Nat.add_assoc sizeValue
    (((0 + 1) + 1) + (sizeValue + 0 + 1 + 1 + 0 + 1)) 1]
  rw [Nat.add_assoc sizeValue
    ((((0 + 1) + 1) + (sizeValue + 0 + 1 + 1 + 0 + 1)) + 1) 1]
  exact Nat.lt_add_of_pos_right (Nat.succ_pos _)

private theorem lt_etaModIntroSource_size (sizeValue : Nat) :
    sizeValue < sizeValue + 0 + 1 + 1 + 0 + 1 + 1 := by
  rw [Nat.add_assoc sizeValue 0 1]
  rw [Nat.add_assoc sizeValue (0 + 1) 1]
  rw [Nat.add_assoc sizeValue ((0 + 1) + 1) 0]
  rw [Nat.add_assoc sizeValue (((0 + 1) + 1) + 0) 1]
  rw [Nat.add_assoc sizeValue ((((0 + 1) + 1) + 0) + 1) 1]
  exact Nat.lt_add_of_pos_right (Nat.succ_pos _)

private theorem lt_etaGlueIntroSource_size (sizeValue : Nat) :
    sizeValue < sizeValue + 0 + 1 + 1 + (sizeValue + 0 + 1) + 1 + 1 := by
  rw [Nat.add_assoc sizeValue 0 1]
  rw [Nat.add_assoc sizeValue (0 + 1) 1]
  rw [Nat.add_assoc sizeValue ((0 + 1) + 1) (sizeValue + 0 + 1)]
  rw [Nat.add_assoc sizeValue
    (((0 + 1) + 1) + (sizeValue + 0 + 1)) 1]
  rw [Nat.add_assoc sizeValue
    ((((0 + 1) + 1) + (sizeValue + 0 + 1)) + 1) 1]
  exact Nat.lt_add_of_pos_right (Nat.succ_pos _)

namespace Step.eta

/-- Every current root eta constructor strictly decreases raw-term size. -/
theorem size_decreases {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (etaStep : Step.eta sourceTerm targetTerm) :
    targetTerm.size < sourceTerm.size := by
  cases etaStep with
  | etaLam =>
      dsimp only [RawTerm.etaLamSource, RawTerm.newestVar, RawTerm.size, RawTermChildren.size]
      rw [RawTerm.size_weaken targetTerm]
      exact lt_etaLamAnnotatedSource_size _ targetTerm.size
  | etaPair =>
      dsimp only [RawTerm.etaPairSource, RawTerm.size, RawTermChildren.size]
      exact lt_etaPairSource_size targetTerm.size
  | etaPathLam =>
      dsimp only [RawTerm.etaPathLamSource, RawTerm.newestVar, RawTerm.size, RawTermChildren.size]
      rw [RawTerm.size_weaken targetTerm]
      exact lt_etaLamSource_size targetTerm.size
  | etaModIntro =>
      dsimp only [RawTerm.etaModIntroSource, RawTerm.size, RawTermChildren.size]
      exact lt_etaModIntroSource_size targetTerm.size
  | etaGlueIntro =>
      dsimp only [RawTerm.etaGlueIntroSource, RawTerm.size, RawTermChildren.size]
      exact lt_etaGlueIntroSource_size targetTerm.size

end Step.eta

namespace Step

/-- Eta-only successor relation for accessibility: `laterTerm` is below
`earlierTerm` when `earlierTerm` contracts by one eta step. -/
def etaSuccessor {scope : Nat}
    (laterTerm earlierTerm : RawTerm scope) : Prop :=
  Step.eta earlierTerm laterTerm

namespace etaStar

/-- Strong normalization for eta-only reduction. -/
def IsStronglyNormalizing {scope : Nat} (sourceTerm : RawTerm scope) :
    Prop :=
  Acc Step.etaSuccessor sourceTerm

/-- Eta-only strong normalization at every scope. -/
def HasStrongNormalization : Prop :=
  ∀ {scope : Nat} (sourceTerm : RawTerm scope),
    IsStronglyNormalizing sourceTerm

/-- Eta-only successor is well-founded because every eta step decreases
`RawTerm.size`. -/
theorem etaSuccessor_wellFounded {scope : Nat} :
    WellFounded (Step.etaSuccessor (scope := scope)) :=
  Subrelation.wf
    (q := Step.etaSuccessor (scope := scope))
    (r := InvImage (fun leftSize rightSize : Nat =>
      leftSize < rightSize) RawTerm.size)
    (fun etaStep => Step.eta.size_decreases etaStep)
    (InvImage.wf RawTerm.size
      (Nat.lt_wfRel.wf :
        WellFounded (fun leftSize rightSize : Nat =>
          leftSize < rightSize)))

/-- Every raw term is eta-only strongly normalizing. -/
theorem isStronglyNormalizing {scope : Nat}
    (sourceTerm : RawTerm scope) :
    IsStronglyNormalizing sourceTerm :=
  etaSuccessor_wellFounded.apply sourceTerm

/-- Eta-only strong normalization at every scope. -/
theorem hasStrongNormalization : HasStrongNormalization := by
  intro scope sourceTerm
  exact isStronglyNormalizing sourceTerm

end etaStar
end Step

end FX1Poly.Core
