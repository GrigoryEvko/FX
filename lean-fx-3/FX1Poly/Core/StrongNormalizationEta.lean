import FX1Poly.Core.StepBetaEtaConfluence
import FX1Poly.Core.RawSize

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
      unfold RawTerm.etaLamSource RawTerm.newestVar
      dsimp only [RawTerm.size, RawTermChildren.size]
      rw [RawTerm.size_weaken targetTerm]
      exact lt_etaLamSource_size targetTerm.size
  | etaPair =>
      unfold RawTerm.etaPairSource
      dsimp only [RawTerm.size, RawTermChildren.size]
      exact lt_etaPairSource_size targetTerm.size
  | etaPathLam =>
      unfold RawTerm.etaPathLamSource RawTerm.newestVar
      dsimp only [RawTerm.size, RawTermChildren.size]
      rw [RawTerm.size_weaken targetTerm]
      exact lt_etaLamSource_size targetTerm.size
  | etaModIntro =>
      unfold RawTerm.etaModIntroSource
      dsimp only [RawTerm.size, RawTermChildren.size]
      exact lt_etaModIntroSource_size targetTerm.size
  | etaGlueIntro =>
      unfold RawTerm.etaGlueIntroSource
      dsimp only [RawTerm.size, RawTermChildren.size]
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

/-- Function eta sources are eta-only strongly normalizing exactly when
their represented functions are.  Both directions are immediate from
global eta-only well-foundedness. -/
theorem etaLam_isStronglyNormalizing_iff {scope : Nat}
    (innerFunction : RawTerm scope) :
    IsStronglyNormalizing (RawTerm.etaLamSource innerFunction) ↔
      IsStronglyNormalizing innerFunction :=
  ⟨fun _ => isStronglyNormalizing innerFunction,
    fun _ => isStronglyNormalizing (RawTerm.etaLamSource innerFunction)⟩

/-- Pair eta sources are eta-only strongly normalizing exactly when
their represented pair terms are. -/
theorem etaPair_isStronglyNormalizing_iff {scope : Nat}
    (pairTerm : RawTerm scope) :
    IsStronglyNormalizing (RawTerm.etaPairSource pairTerm) ↔
      IsStronglyNormalizing pairTerm :=
  ⟨fun _ => isStronglyNormalizing pairTerm,
    fun _ => isStronglyNormalizing (RawTerm.etaPairSource pairTerm)⟩

/-- Path eta sources are eta-only strongly normalizing exactly when
their represented path terms are. -/
theorem etaPathLam_isStronglyNormalizing_iff {scope : Nat}
    (innerPath : RawTerm scope) :
    IsStronglyNormalizing (RawTerm.etaPathLamSource innerPath) ↔
      IsStronglyNormalizing innerPath :=
  ⟨fun _ => isStronglyNormalizing innerPath,
    fun _ => isStronglyNormalizing (RawTerm.etaPathLamSource innerPath)⟩

/-- Modal eta sources are eta-only strongly normalizing exactly when
their represented modal terms are. -/
theorem etaModIntro_isStronglyNormalizing_iff {scope : Nat}
    (modalTerm : RawTerm scope) :
    IsStronglyNormalizing (RawTerm.etaModIntroSource modalTerm) ↔
      IsStronglyNormalizing modalTerm :=
  ⟨fun _ => isStronglyNormalizing modalTerm,
    fun _ => isStronglyNormalizing (RawTerm.etaModIntroSource modalTerm)⟩

/-- Glue eta sources are eta-only strongly normalizing exactly when
their represented Glue terms are. -/
theorem etaGlueIntro_isStronglyNormalizing_iff {scope : Nat}
    (gluedTerm : RawTerm scope) :
    IsStronglyNormalizing (RawTerm.etaGlueIntroSource gluedTerm) ↔
      IsStronglyNormalizing gluedTerm :=
  ⟨fun _ => isStronglyNormalizing gluedTerm,
    fun _ => isStronglyNormalizing (RawTerm.etaGlueIntroSource gluedTerm)⟩

end etaStar
end Step

end FX1Poly.Core
