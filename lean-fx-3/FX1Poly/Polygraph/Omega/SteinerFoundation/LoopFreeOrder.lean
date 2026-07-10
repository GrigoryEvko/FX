import FX1Poly.Polygraph.Omega.SteinerFoundation.AugmentedDirectedComplex

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

/-! ## The same-dimension Steiner (odot) order and its acyclicity — genuinely closed here

The intra-dimension relation (an atom's target meets another's source) is a `Prop`-valued relation
on `DimensionedAtom`; loop-freeness is its acyclicity (Steiner Thm 1.2.1.23).  This section supplies
the two GENUINE closers — no opaque hypothesis, no `WellFounded.fix`:

  * `emptyIntraOrderIsLoopFree` — the empty same-dimension order (the honest answer for a
    dimension-strict polygraph: no non-trivial same-dimension composability edge to orient) is
    well-founded by a one-line structural `Acc`.
  * `loopFreeOfRank` — a same-dimension order carrying a strictly-decreasing `Nat` rank is
    well-founded by the SAME structural argument as the cross-dimension proof above (a rank bound
    replaces the dimension bound).

The concrete ADC-computed overlap order (`sameDimensionOverlapOrder`) and an inhabited loop-free
instance (the single-object-semiring computad complex) live in
`FX1Poly/Polygraph/Steiner/ComputadLoopFree.lean`. -/

/-- A same-dimension precedence: a relation on the dimensioned atoms.  A concrete computation from
the ADC cell-table is `sameDimensionOverlapOrder` (ComputadLoopFree.lean). -/
def SameDimensionOrder := DimensionedAtom → DimensionedAtom → Prop

/-- A basis is LOOP-FREE (for a given intra-dimension order) iff that same-dimension order is
well-founded — the acyclicity hypothesis of Steiner Thm 1.2.1.23. -/
def IsLoopFreeBasis (intraDimensionOrder : SameDimensionOrder) : Prop :=
  WellFounded intraDimensionOrder

/-- The empty same-dimension order — no atom precedes any other within its dimension.  This is the
honest intra-dimension order for a genuine polygraph whose generator boundaries strictly drop
dimension (there is no non-trivial same-dimension composability edge to orient). -/
def emptyIntraOrder : SameDimensionOrder := fun _ _ => False

/-- **The empty intra-dimension order is loop-free** — genuinely proved (not an opaque
hypothesis), no `WellFounded.fix`: every atom is accessible because it has no predecessors. -/
theorem emptyIntraOrderIsLoopFree : IsLoopFreeBasis emptyIntraOrder :=
  WellFounded.intro (fun atom =>
    Acc.intro atom (fun _ isPredecessor => False.elim isPredecessor))

/-- Every atom below a `Nat` rank bound is accessible for an order that STRICTLY LOWERS a rank —
structural `Nat` induction on the bound (`Acc.intro`, no `WellFounded.fix`), mirroring
`boundaryContainmentAccessibleWithinDimensionBound` with `naturalRank` in place of `dimension`. -/
theorem accessibleWithinRankBound
    (order : SameDimensionOrder) (naturalRank : DimensionedAtom → Nat)
    (rankStrictlyDecreases :
      ∀ lower higher, order lower higher → naturalRank lower < naturalRank higher) :
    ∀ (rankBound : Nat) (atom : DimensionedAtom),
      naturalRank atom < rankBound → Acc order atom
  | 0, _, isBelowZero => absurd isBelowZero (Nat.not_lt_zero _)
  | rankBound + 1, atom, isBelowSucc =>
      Acc.intro atom (fun predecessor isPredecessor =>
        have predecessorBelowAtom : naturalRank predecessor < naturalRank atom :=
          rankStrictlyDecreases predecessor atom isPredecessor
        have atomAtMostBound : naturalRank atom ≤ rankBound := Nat.le_of_lt_succ isBelowSucc
        accessibleWithinRankBound order naturalRank rankStrictlyDecreases rankBound predecessor
          (Nat.lt_of_lt_of_le predecessorBelowAtom atomAtMostBound))

/-- **A same-dimension order with a strictly-decreasing `Nat` rank is loop-free** — the genuine
structural closer for a NON-empty but acyclic intra-dimension order (a topological rank witnesses
acyclicity).  No `WellFounded.fix`, no `Classical`. -/
theorem loopFreeOfRank
    (order : SameDimensionOrder) (naturalRank : DimensionedAtom → Nat)
    (rankStrictlyDecreases :
      ∀ lower higher, order lower higher → naturalRank lower < naturalRank higher) :
    IsLoopFreeBasis order :=
  WellFounded.intro (fun atom =>
    accessibleWithinRankBound order naturalRank rankStrictlyDecreases
      (naturalRank atom + 1) atom (Nat.lt_succ_self _))

end FX1Poly.Polygraph.Steiner
