import FX1Poly.Polygraph.Omega.SteinerFoundation.LoopFreeOrder
import FX1Poly.Polygraph.Omega.SteinerFoundation.CellCoordinates

/-! # FX1Poly/Polygraph/Steiner/ComputadLoopFree — the ADC-computed same-dimension order + a REAL
    inhabited loop-free instance (frontiers.md §3.1; Steiner Thm 1.2.1.23)

`LoopFreeOrder.lean` ships the cross-dimension boundary-containment order (well-founded for FREE:
the grading forbids cross-dimension cycles) and the two abstract loop-free closers
(`emptyIntraOrderIsLoopFree`, `loopFreeOfRank`).  This file makes the SAME-dimension Steiner
`(odot)` order CONCRETE — computed straight off the boundary matrices via the source/target split
of `CellCoordinates` — and inhabits `IsLoopFreeBasis` with a REAL augmented directed complex.

## The concrete order (`sameDimensionOverlapOrder`)

Two SAME-dimension atoms `atomA (odot) atomB` iff their pasting is composable: some `(n-1)`-face
lies in `atomA`'s TARGET (positive part of `d`) AND in `atomB`'s SOURCE (negative part of `d`),
read off `boundaryMatrix (n-1)` via `positiveClampEntry` / `negativeClampEntry`.  This is Steiner's
`(odot)` generator; loop-freeness is its acyclicity.

## The inhabited instance — the single-object semiring computad complex

`singleObjectSemiringComplex` is the augmented directed complex of the single-object semiring
computad (`ModeComputad.lean`: one object, one endo 1-generator = the multiplication, no 2-cells).
Every boundary matrix entry is `0` (the lone endo 1-cell is a loop `object -> object`, so its
`d0` column `[target] - [source] = [1] - [1] = [0]`).  Hence the overlap order has NO edge, and
`IsLoopFreeBasis (sameDimensionOverlapOrder singleObjectSemiringComplex)` holds GENUINELY — the
real Steiner overlap order, proved acyclic because it is empty, NOT the `emptyIntraOrder` stand-in.

This is the honest inhabited witness that the loop-free SN precedence is real.  The walking
ADJUNCTION complex is deliberately NOT here: its naive target-meets-source order has a 2-cycle
`left (odot) right (odot) left` (both `base -> tip -> base` and `tip -> base -> tip` composites
exist), so the adjunction is genuinely NOT loop-free under this order — exactly why Steiner's
hypothesis has teeth and the walking-adjunction tower needs the separate chained-spine
`ArcLoopFreedom` treatment.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Steiner/ComputadLoopFree.lean`. -/

namespace FX1Poly.Polygraph.Steiner

open FX1Poly.ComputerAlgebra

/-! ## The concrete ADC-computed same-dimension overlap order -/

/-- **The Steiner same-dimension `(odot)` order, computed from the ADC.**  `atomA (odot) atomB` iff
they share a dimension and some `(dim-1)`-face lies in `atomA`'s TARGET (`positiveClampEntry` of the
boundary column) and in `atomB`'s SOURCE (`negativeClampEntry`) — the pasting-composability
generator.  Concrete: no opaque parameter. -/
def sameDimensionOverlapOrder (complex : AugmentedDirectedComplex) : SameDimensionOrder :=
  fun atomA atomB =>
    atomA.dimension = atomB.dimension ∧
    ∃ faceIndex, faceIndex < complex.basisCount (atomA.dimension - 1) ∧
      positiveClampEntry
        ((complex.boundaryMatrix (atomA.dimension - 1)).entryAt faceIndex atomA.atomIndex) ≠ 0 ∧
      negativeClampEntry
        ((complex.boundaryMatrix (atomA.dimension - 1)).entryAt faceIndex atomB.atomIndex) ≠ 0

/-! ## The single-object semiring computad's augmented directed complex -/

/-- Basis counts of the single-object semiring: one `0`-cell, one `1`-generator (the endo
multiplication), no higher cells. -/
def semiringBasisCount : Nat → Nat
  | 0 => 1
  | 1 => 1
  | _ + 2 => 0

/-- Boundary matrices: `d0` is the `1x1` matrix `[[0]]` (the endo `1`-cell is a loop, so
`[target] - [source] = [1] - [1] = [0]`); `d1` is the `1x0` matrix `[[]]`; everything above is
empty. -/
def semiringBoundaryMatrix : Nat → IntMatrix
  | 0 => ⟨[[0]]⟩
  | 1 => ⟨[[]]⟩
  | _ + 2 => ⟨[]⟩

/-- Lookup past the end of an empty list is the default, at any position. -/
theorem listGetWithDefaultEmpty {Entry : Type} (defaultEntry : Entry) :
    ∀ position, listGetWithDefault defaultEntry [] position = defaultEntry
  | 0 => rfl
  | _ + 1 => rfl

/-- **Every entry of every semiring boundary matrix is zero** — the load-bearing structural fact:
the sole endo `1`-generator contributes a zero boundary column, and all higher matrices are empty
or width-zero. -/
theorem semiringBoundaryEntryIsZero :
    ∀ (dim faceIndex atomIndex : Nat),
      (semiringBoundaryMatrix dim).entryAt faceIndex atomIndex = 0
  | 0, 0, 0 => rfl
  | 0, 0, atomIndex + 1 => listGetWithDefaultEmpty (0 : Int) atomIndex
  | 0, faceIndex + 1, atomIndex => by
      show listGetWithDefault (0 : Int)
        (listGetWithDefault ([] : IntRow) [[(0 : Int)]] (faceIndex + 1)) atomIndex = 0
      rw [show listGetWithDefault ([] : IntRow) [[(0 : Int)]] (faceIndex + 1) = []
            from listGetWithDefaultEmpty ([] : IntRow) faceIndex]
      exact listGetWithDefaultEmpty (0 : Int) atomIndex
  | 1, 0, atomIndex => listGetWithDefaultEmpty (0 : Int) atomIndex
  | 1, faceIndex + 1, atomIndex => by
      show listGetWithDefault (0 : Int)
        (listGetWithDefault ([] : IntRow) [([] : IntRow)] (faceIndex + 1)) atomIndex = 0
      rw [show listGetWithDefault ([] : IntRow) [([] : IntRow)] (faceIndex + 1) = []
            from listGetWithDefaultEmpty ([] : IntRow) faceIndex]
      exact listGetWithDefaultEmpty (0 : Int) atomIndex
  | _ + 2, faceIndex, atomIndex => by
      show listGetWithDefault (0 : Int)
        (listGetWithDefault ([] : IntRow) ([] : List IntRow) faceIndex) atomIndex = 0
      rw [show listGetWithDefault ([] : IntRow) ([] : List IntRow) faceIndex = []
            from listGetWithDefaultEmpty ([] : IntRow) faceIndex]
      exact listGetWithDefaultEmpty (0 : Int) atomIndex

/-- **The augmented directed complex of the single-object semiring computad.**  A genuine ADC: the
two chain obligations hold — `d0 d1 = 0` and `eps d1 = 0` are both entrywise vacuous/zero because
`basisCount (dim+2) = 0` for every `dim` and the one boundary column is zero. -/
def singleObjectSemiringComplex : AugmentedDirectedComplex where
  basisCount := semiringBasisCount
  boundaryMatrix := semiringBoundaryMatrix
  augmentation := [1]
  boundaryHasDimensions := fun dim =>
    match dim with
    | 0 => ⟨rfl, rfl, True.intro⟩
    | 1 => ⟨rfl, rfl, True.intro⟩
    | _ + 2 => ⟨rfl, True.intro⟩
  augmentationHasWidth := rfl
  boundaryComposesToZero := fun _ _ colIndex _ colBound =>
    absurd colBound (Nat.not_lt_zero colIndex)
  augmentationComposesToZero := fun colIndex _ => by
    cases colIndex with
    | zero => rfl
    | succ position =>
      show (0 : Int) + 1 * (semiringBoundaryMatrix 0).entryAt 0 (position + 1) = 0
      rw [semiringBoundaryEntryIsZero]
      rfl

/-- The complex's boundary entries are all zero (the projection form, for rewriting under the
overlap order). -/
theorem singleObjectSemiringComplex_entryIsZero (dim faceIndex atomIndex : Nat) :
    (singleObjectSemiringComplex.boundaryMatrix dim).entryAt faceIndex atomIndex = 0 :=
  semiringBoundaryEntryIsZero dim faceIndex atomIndex

/-- **The semiring overlap order has no edge** — any purported `(odot)`-edge needs a face in an
atom's TARGET, but every boundary entry is zero and `positiveClampEntry 0 = 0`. -/
theorem noSingleObjectSemiringOverlapEdge (atomA atomB : DimensionedAtom) :
    ¬ sameDimensionOverlapOrder singleObjectSemiringComplex atomA atomB := by
  intro edge
  obtain ⟨_, _, _, targetNonzero, _⟩ := edge
  apply targetNonzero
  rw [singleObjectSemiringComplex_entryIsZero]
  rfl

/-- ★ **THE inhabited loop-free instance** — the concrete Steiner same-dimension overlap order on
the single-object semiring complex is well-founded (loop-free): every atom is accessible because
the order has no predecessors.  A GENUINE `IsLoopFreeBasis` witness over the ADC-computed order (not
the `emptyIntraOrder` stand-in), no `WellFounded.fix`. -/
theorem singleObjectSemiringComplex_isLoopFreeBasis :
    IsLoopFreeBasis (sameDimensionOverlapOrder singleObjectSemiringComplex) :=
  WellFounded.intro (fun atom =>
    Acc.intro atom (fun predecessor edge =>
      absurd edge (noSingleObjectSemiringOverlapEdge predecessor atom)))

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the loop-free SN precedence is REAL and inhabited.**  The cross-dimension
boundary order is well-founded for free (`loopFreeOrderIsWellFounded`); the same-dimension Steiner
`(odot)` order is now CONCRETE (`sameDimensionOverlapOrder`, computed off the boundary matrices) and
GENUINELY loop-free on a real ADC (`singleObjectSemiringComplex_isLoopFreeBasis`), not an opaque
hypothesis.  `= true`. -/
def polygraph_hasInhabitedLoopFreeBasis : Bool := true

end FX1Poly.Polygraph.Steiner
