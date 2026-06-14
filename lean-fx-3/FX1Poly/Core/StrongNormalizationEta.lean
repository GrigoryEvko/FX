import FX1Poly.Tier0.Syntax.RawSize
import FX1Poly.Core.StepEtaRootTable
import FX1Poly.Core.StepEtaTableBackward
import FX1Poly.Core.StepEtaRootTableSourceShape

/-! # Foundation/PolyCell/Core/StrongNormalizationEta
    - root-table eta accessibility

Root eta is easier than beta+iota: every eta source shape strictly
contracts raw size.  This file proves the canonical root-table eta-only
well-foundedness substrate (the harder beta-only-to-betaEta SN transfer
is handled elsewhere).

The `StepEtaRootTable` size-decrease (`Step.etaRootTable_size_decreases`)
is proved NATIVELY: it inverts the contraction, reads off the raw source
SHAPE via the bespoke-construction-free `stepEtaRootTableSourceShape`
dispatcher, and discharges the strict decrease on each of the three
raw-tier shapes with per-shape size arithmetic (`lt_etaLamAnnotatedSource_size`
/ `lt_etaPairSource_size` / `lt_etaLamSource_size`) — never constructing a
`Step.eta`.  The well-foundedness and accessibility theorems
(`Step.etaRootTableSuccessor`, `IsStronglyNormalizingRootTable`, ...) build
on it.  (The full-congruence `StepEtaOverTable` already has its own
size-decrease SN in `StrongNormalizationEtaTable`; this is the ROOT-tier
counterpart so the typed-metatheory consumers can speak the canonical
relation.)
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

/-! ## The canonical-table root-eta accessibility (TABLE-CANON-ETA)

The size-decrease is proved NATIVELY over the canonical root table
relation `StepEtaRootTable`: it inverts the contraction, reads off the
raw source SHAPE via the bespoke-construction-free
`stepEtaRootTableSourceShape` dispatcher, and discharges the strict
decrease on each of the three raw-tier shapes with per-shape arithmetic
(`lt_etaLamAnnotatedSource_size` / `lt_etaPairSource_size` /
`lt_etaLamSource_size`) — never constructing a `Step.eta` and never
crossing the bespoke adequacy bridge. -/

namespace Step

/-- A canonical root-table eta contraction strictly decreases raw size,
proved natively by inverting the contraction, reading the raw source
shape, and applying the per-shape size arithmetic directly. -/
theorem etaRootTable_size_decreases {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (rootStep : StepEtaRootTable sourceTerm targetTerm) :
    targetTerm.size < sourceTerm.size := by
  obtain ⟨rule, isRow, isRawTier, introPayload, introChildren,
    sourceShape, contracts⟩ := rootStep.invert
  subst sourceShape
  rcases stepEtaRootTableSourceShape isRow isRawTier introPayload contracts
    with ⟨domainAnn, lamShape⟩ | pairShape | pathLamShape
  · rw [lamShape]
    dsimp only [RawTerm.etaLamSource, RawTerm.newestVar, RawTerm.size,
      RawTermChildren.size]
    rw [RawTerm.size_weaken targetTerm]
    exact lt_etaLamAnnotatedSource_size _ targetTerm.size
  · rw [pairShape]
    dsimp only [RawTerm.etaPairSource, RawTerm.size, RawTermChildren.size]
    exact lt_etaPairSource_size targetTerm.size
  · rw [pathLamShape]
    dsimp only [RawTerm.etaPathLamSource, RawTerm.newestVar, RawTerm.size,
      RawTermChildren.size]
    rw [RawTerm.size_weaken targetTerm]
    exact lt_etaLamSource_size targetTerm.size

namespace etaStar

/-- Root-table eta successor for accessibility: `laterTerm` is below
`earlierTerm` when `earlierTerm` contracts to it by one canonical
root-table eta step. -/
def etaRootTableSuccessor {scope : Nat}
    (laterTerm earlierTerm : RawTerm scope) : Prop :=
  StepEtaRootTable earlierTerm laterTerm

/-- Strong normalization for canonical root-table eta reduction. -/
def IsStronglyNormalizingRootTable {scope : Nat}
    (sourceTerm : RawTerm scope) : Prop :=
  Acc etaRootTableSuccessor sourceTerm

/-- Canonical root-table eta strong normalization at every scope. -/
def HasStrongNormalizationRootTable : Prop :=
  ∀ {scope : Nat} (sourceTerm : RawTerm scope),
    IsStronglyNormalizingRootTable sourceTerm

/-- Root-table eta successor is well-founded because every root-table
eta step decreases `RawTerm.size` (through the adequacy bridge). -/
theorem etaRootTableSuccessor_wellFounded {scope : Nat} :
    WellFounded (etaRootTableSuccessor (scope := scope)) :=
  Subrelation.wf
    (q := etaRootTableSuccessor (scope := scope))
    (r := InvImage (fun leftSize rightSize : Nat =>
      leftSize < rightSize) RawTerm.size)
    (fun rootStep => Step.etaRootTable_size_decreases rootStep)
    (InvImage.wf RawTerm.size
      (Nat.lt_wfRel.wf :
        WellFounded (fun leftSize rightSize : Nat =>
          leftSize < rightSize)))

/-- Every raw term is canonical root-table eta strongly normalizing. -/
theorem isStronglyNormalizingRootTable {scope : Nat}
    (sourceTerm : RawTerm scope) :
    IsStronglyNormalizingRootTable sourceTerm :=
  etaRootTableSuccessor_wellFounded.apply sourceTerm

/-- Canonical root-table eta strong normalization at every scope. -/
theorem hasStrongNormalizationRootTable :
    HasStrongNormalizationRootTable := by
  intro scope sourceTerm
  exact isStronglyNormalizingRootTable sourceTerm

end etaStar
end Step

end FX1Poly.Core
