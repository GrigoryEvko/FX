import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingInvariant
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # ArcNonCrossingCupPositions — cyclic-position bookkeeping for the cup step (cup rung D2a-iii, part 1)

The stepCupArc preservation of `ArcNonCrossing` (D2a-iii) rests on how `arcEndTokenPosition` moves
when the fold splices two fresh legs into `openWires` at a window position.  This file ships the
position facts: the spliced open-wire list is two longer, and — the load-bearing planarity fact —
the two new cup legs land at ADJACENT cyclic positions (`openSlot (position+1)` exactly one below
`openSlot position`), so the cup is an innermost nested arc that no other arc can interleave.

The Nat-subtraction arithmetic is hand-rolled: essentially every "cancel/pos" subtraction lemma in
`Init` (`Nat.sub_pos_of_lt`, `Nat.add_sub_cancel(_left)`, `Nat.sub_add_cancel`, `Nat.sub_sub`,
`Nat.sub_le_sub_left`) depends on `propext`, so `addSubCancelLeft` and `subPosOfLt` are proved here
by structural induction from the clean primitives (`Nat.succ_sub_succ`, `Nat.sub_succ`,
`Nat.succ_pred_eq_of_pos`).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private clean Nat-subtraction plumbing (Init's cancel/pos lemmas leak propext) -/

/-- `(start + amount) - start = amount`, hand-rolled clean. -/
private theorem addSubCancelLeft : (start amount : Nat) → (start + amount) - start = amount
  | 0, amount => by rw [Nat.zero_add, Nat.sub_zero]
  | start + 1, amount => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact addSubCancelLeft start amount

/-- A subtraction from a strictly larger minuend is positive, hand-rolled clean. -/
private theorem subPosOfLt (position bound : Nat) (posLt : position < bound) :
    0 < bound - position := by
  obtain ⟨diff, diffEq⟩ := Nat.le.dest posLt
  have reshape : position + 1 + diff = position + (diff + 1) := by
    rw [Nat.add_right_comm, Nat.add_assoc]
  rw [← diffEq, reshape, addSubCancelLeft]
  exact Nat.succ_pos diff

/-- The pure cyclic-position adjacency: over a boundary two longer, `openSlot (position+1)` sits one
below `openSlot position` (both reversed past the seed block). -/
private theorem legsAdjacentArith (seedBoundary oldLen position : Nat) (fits : position ≤ oldLen) :
    seedBoundary + ((oldLen + 2) - 1 - (position + 1)) + 1
      = seedBoundary + ((oldLen + 2) - 1 - position) := by
  have gapPos : 0 < (oldLen + 1) - position :=
    subPosOfLt position (oldLen + 1) (Nat.lt_succ_of_le fits)
  have key : (oldLen + 1) - (position + 1) + 1 = (oldLen + 1) - position := by
    rw [Nat.sub_succ]
    exact Nat.succ_pred_eq_of_pos gapPos
  show seedBoundary + ((oldLen + 1) - (position + 1)) + 1
    = seedBoundary + ((oldLen + 1) - position)
  rw [Nat.add_assoc, key]

/-! ## The spliced open-wire length and the leg positions -/

/-- A fired cup splices two legs, so the open-wire frontier grows by exactly two. -/
theorem arcCupNewOpenLength (state : ArcWireState) (position : Nat) :
    (stepCupArc state position).openWires.length = state.openWires.length + 2 :=
  natListInsertAt_length state.openWires position [state.nextFresh, state.nextFresh + 1]

/-- ★ **The two new cup legs occupy adjacent cyclic positions** — `openSlot (position+1)` is exactly
one below `openSlot position` on the spliced boundary.  The cup is therefore an innermost nested
arc, which is what makes it impossible for any third strand to interleave with it. -/
theorem arcCupLegsAdjacent (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (cupInRange : position ≤ state.openWires.length) :
    arcEndTokenPosition seedBoundary (stepCupArc state position)
        (ArcEndToken.openSlot (position + 1)) + 1
      = arcEndTokenPosition seedBoundary (stepCupArc state position)
        (ArcEndToken.openSlot position) := by
  show seedBoundary + ((stepCupArc state position).openWires.length - 1 - (position + 1)) + 1
    = seedBoundary + ((stepCupArc state position).openWires.length - 1 - position)
  rw [arcCupNewOpenLength]
  exact legsAdjacentArith seedBoundary state.openWires.length position cupInRange

/-! ## Honesty marker -/

/-- **Honesty marker — the cup-step cyclic-position bookkeeping (cup rung D2a-iii, part 1).**
`arcCupNewOpenLength` (the frontier grows by two) and `arcCupLegsAdjacent` (the two new legs land at
adjacent cyclic positions — the innermost nested cup), on a hand-rolled clean Nat-subtraction base.
What this marker does NOT claim: the stepCupArc preservation of `ArcNonCrossing` itself (the main
theorem — needs the same-component leg/old-zone classification and the old-zone monotone
position-remap), the cap step, the fold, and the extract translation to `IsNonCrossing`.  `= true`. -/
def fxMode_hasArcNonCrossingCupPositions : Bool := true

end FX1Poly.Polygraph
