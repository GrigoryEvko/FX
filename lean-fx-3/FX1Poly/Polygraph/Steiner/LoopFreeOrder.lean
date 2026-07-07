import FX1Poly.Polygraph.Steiner.AugmentedDirectedComplex

/-! # FX1Poly/Polygraph/Steiner/LoopFreeOrder — the boundary-containment order = canonical SN
    precedence (frontiers.md §3.1: retires the fib-3-floor "which LPO?" question)

The loop-free order `a (odot) b` = "atom `a` occurs in `d b`".  Its transitive closure is a
well-founded partial order — a CANONICAL strong-normalization precedence, replacing the ad-hoc
LPO choice at the fib-3 mode-side floor.

The BUILDABLE well-foundedness is the DIMENSION-GRADED containment: containment always drops
dimension by exactly one, so a strictly-decreasing `Nat` measure (`dimension`) gives `Acc`
STRUCTURALLY — by ordinary `Nat` induction, NOT `WellFounded.fix`.  This is unconditional (no
loop-free hypothesis needed): the grading already forbids cross-dimension cycles, and lowering a
cell's dimension is a legitimate SN measure (a redex strictly lowers cell dimension).

The full Steiner `(odot)` order also relates SAME-dimension atoms (via iterated boundaries); its
acyclicity is exactly the loop-free hypothesis of Steiner Thm 1.2.1.23 and is DEFERRED — here the
same-dimension relation is only NAMED (`orderWithinDimension` as an opaque `Prop` parameter) and
loop-freeness is stated as its acyclicity, not proved.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Steiner/LoopFreeOrder.lean`. -/

namespace FX1Poly.Polygraph.Steiner

open FX1Poly.ComputerAlgebra

/-- An atom tagged with its dimension — a node of the containment DAG. -/
structure DimensionedAtom where
  dimension : Nat
  atomIndex : Nat

/-- Atom `lowerIndex` (dim `dim`) occurs in the boundary of atom `higherIndex` (dim `dim+1`) iff
the boundary-matrix entry linking them is nonzero. -/
def atomOccursInBoundaryOf
    (complex : AugmentedDirectedComplex) (dim lowerIndex higherIndex : Nat) : Prop :=
  (complex.boundaryMatrix dim).entryAt lowerIndex higherIndex ≠ 0

/-- The strict boundary-containment precedence `lower (prec) higher` across the whole basis:
`higher` is one dimension up and `lower` occurs in its boundary. -/
def precedesInBoundary
    (complex : AugmentedDirectedComplex) (lower higher : DimensionedAtom) : Prop :=
  higher.dimension = lower.dimension + 1 ∧
  atomOccursInBoundaryOf complex lower.dimension lower.atomIndex higher.atomIndex

/-- Every atom below a dimension bound is accessible — structural `Nat` induction on the bound
(`Acc.intro`, no `WellFounded.fix`): a predecessor drops one dimension, so it stays under the
predecessor bound. -/
theorem boundaryContainmentAccessibleWithinDimensionBound
    (complex : AugmentedDirectedComplex) :
    ∀ (dimensionBound : Nat) (atom : DimensionedAtom),
      atom.dimension < dimensionBound → Acc (precedesInBoundary complex) atom
  | 0, _, isBelowZero => absurd isBelowZero (Nat.not_lt_zero _)
  | dimensionBound + 1, atom, isBelowSucc =>
      Acc.intro atom (fun predecessor isPredecessor =>
        have dimensionSteps : atom.dimension = predecessor.dimension + 1 := isPredecessor.left
        have predecessorBelowAtom : predecessor.dimension < atom.dimension :=
          dimensionSteps ▸ Nat.lt_succ_self predecessor.dimension
        have atomAtMostBound : atom.dimension ≤ dimensionBound := Nat.le_of_lt_succ isBelowSucc
        have predecessorBelowBound : predecessor.dimension < dimensionBound :=
          Nat.lt_of_lt_of_le predecessorBelowAtom atomAtMostBound
        boundaryContainmentAccessibleWithinDimensionBound complex dimensionBound
          predecessor predecessorBelowBound)

/-- **The loop-free (boundary-containment) order is well-founded** — the free SN measure that
retires the fib-3 "which LPO?" question.  Unconditional: the dimension grading supplies it. -/
theorem loopFreeOrderIsWellFounded (complex : AugmentedDirectedComplex) :
    WellFounded (precedesInBoundary complex) :=
  ⟨fun atom =>
    boundaryContainmentAccessibleWithinDimensionBound complex (atom.dimension + 1) atom
      (Nat.lt_succ_self atom.dimension)⟩

/-! ## Deferred: the same-dimension Steiner (odot) order and its acyclicity

The intra-dimension relation (an atom's target meets another's source) is only NAMED here as an
opaque `Prop`-valued parameter; loop-freeness is its acyclicity.  The genuine content — computing
the overlap from the ADC cell-table and proving acyclicity (Steiner's hypothesis) — is DEFERRED,
alongside the equivalence Thm 1.2.1.23 and the Gray/Koszul chain tensor. -/

/-- A same-dimension precedence supplied as an opaque parameter (the general computation from the
ADC cell-table is deferred). -/
def SameDimensionOrder := DimensionedAtom → DimensionedAtom → Prop

/-- A basis is LOOP-FREE (for a given intra-dimension order) iff that same-dimension order is
well-founded — the acyclicity hypothesis of Steiner Thm 1.2.1.23.  Stated, not proved. -/
def IsLoopFreeBasis (intraDimensionOrder : SameDimensionOrder) : Prop :=
  WellFounded intraDimensionOrder

end FX1Poly.Polygraph.Steiner
