import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.PureCapSurvivorFrontFail
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.PureCapSurvivorTopHit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPairSeparation

/-! # PureCapSurvivorReadoff — the survivor partner read-off (Piece II tail, 2b closed)

Combining brick (2b) step 1 (`partnerIndexOf_survivor_dropsToTop` — a survivor's partner scan drops
to the top segment) with the step-2 combinator (`findPartnerScan_mapRange_firstHit` — first passing
candidate wins over a base-shifted range), this file CLOSES (2b): a survivor bottom port `survivor`
whose node id sits at position `rank` among the final open wires has
`partnerIndexOf = bottomCount + rank`.

The reduction: on the top segment the candidate at offset is `bottomCount + offset`, which reads the
open wire at `offset` (`matchingBoundaryNodes_getAt_top`), an unlinked node so its own root; and the
exclude bang-inequality holds because `bottomCount + offset > survivor`.  So the exclude-and-root test
collapses to `openWires[offset] == survivor` — false below `rank` (open-wire distinctness), true at
`rank` (the survivor's position).  The first-hit combinator then places the partner at
`bottomCount + rank`.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- An in-range positional read is a member (local copy — the seed files' `natListGetAt_mem_inRange`
is file-private). -/
private theorem getAt_mem_of_lt : (wires : List Nat) → (index : Nat) →
    index < wires.length → natListGetAt wires index ∈ wires
  | [], _, indexInRange => absurd indexInRange (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, indexInRange =>
      List.Mem.tail _ (getAt_mem_of_lt rest index (Nat.lt_of_succ_lt_succ indexInRange))

/-- ★ **The survivor partner read-off (2b closed).**  A survivor bottom port `survivor` (`< bottomCount`,
unlinked) whose node id sits at position `rank` among the final open wires has
`partnerIndexOf = bottomCount + rank`.  The scan drops to the top segment (2b step 1), where the
per-candidate test collapses to `openWires[offset] == survivor` — the first hit is at the survivor's
own rank (open-wire distinctness), landing the first-hit combinator at `bottomCount + rank`. -/
theorem partnerIndexOf_survivor_eq_rank (links : List (Nat × Nat)) (bottomCount : Nat)
    (state : WireState) {survivor rank : Nat}
    (survivorBelow : survivor < bottomCount)
    (survivorUnlinked : ArcNodeUnlinked links survivor)
    (openDistinct : WireListDistinct state.openWires)
    (openAllUnlinked : ∀ w ∈ state.openWires, ArcNodeUnlinked links w)
    (rankLt : rank < state.openWires.length)
    (survivorAtRank : natListGetAt state.openWires rank = survivor) :
    partnerIndexOf links (matchingBoundaryNodes bottomCount state)
        (bottomCount + state.openWires.length) survivor
      = bottomCount + rank := by
  rw [partnerIndexOf_survivor_dropsToTop links bottomCount state survivorBelow survivorUnlinked
    state.openWires.length]
  refine findPartnerScan_mapRange_firstHit links (matchingBoundaryNodes bottomCount state)
    survivor survivor state.openWires.length rank bottomCount rankLt ?_ ?_
  · intro offset offsetLt
    rw [matchingBoundaryNodes_getAt_top bottomCount state offset,
      unionFindRootOf_eq_self_ofUnlinked links
        (openAllUnlinked _ (getAt_mem_of_lt state.openWires offset (Nat.lt_trans offsetLt rankLt)))]
    have offsetBeqFalse : (natListGetAt state.openWires offset == survivor) = false := by
      cases readIsSurvivor : (natListGetAt state.openWires offset == survivor) with
      | true =>
          exact absurd ((of_decide_eq_true readIsSurvivor).trans survivorAtRank.symm)
            (distinctReadNe state.openWires openDistinct offset rank
              (Nat.lt_trans offsetLt rankLt) rankLt (fun offsetEqRank => absurd offsetEqRank
                (fun eq => Nat.lt_irrefl rank (eq ▸ offsetLt))))
      | false => rfl
    rw [offsetBeqFalse]; exact Bool.and_false _
  · have survivorLt : survivor < bottomCount + rank :=
      Nat.lt_of_lt_of_le survivorBelow (Nat.le_add_right bottomCount rank)
    have excludeNeqTrue : (bottomCount + rank != survivor) = true := by
      show (!(bottomCount + rank == survivor)) = true
      cases sumIsSurvivor : (bottomCount + rank == survivor) with
      | true =>
          exact absurd (of_decide_eq_true sumIsSurvivor)
            (fun sumEq => Nat.lt_irrefl survivor (sumEq ▸ survivorLt))
      | false => rfl
    have selfBeq : (survivor == survivor) = true := by
      cases selfProbe : (survivor == survivor) with
      | true => rfl
      | false => exact absurd rfl (of_decide_eq_false selfProbe)
    rw [matchingBoundaryNodes_getAt_top bottomCount state rank, survivorAtRank,
      unionFindRootOf_eq_self_ofUnlinked links survivorUnlinked, selfBeq, Bool.and_true]
    exact excludeNeqTrue

/-! ## Honesty marker -/

/-- **Honesty marker — the survivor partner read-off (2b) is CLOSED.**  For a pure-cap block's final
state, a survivor bottom port's `partnerIndexOf` is `bottomCount + (its rank among the open wires)`,
proven by dropping the scan to the top segment (2b step 1) and resolving it with the mapped-range
first-hit combinator (2b step 2), the per-candidate test collapsing to `openWires[offset] == survivor`
via open-wire distinctness.  Instantiated at a pure-cap block from the seed (survivors unlinked by
brick 2a, distinct by the shipped `WireListDistinct`), this pins each survivor's partner top port to
its rank.  NOT yet shipped: (3) the F-assembly relating `matchingOf bc capBlock` to `F(matchingOf bc
V)` by `DiagramType.ext`, (4) the cup dual, and (5)/(6) `valleyAppend_split` /
`valleysWithEqualMatching_spineTraceEquiv`.  No gate flag is flipped.  `= true`. -/
def fxMode_hasPureCapSurvivorReadoff : Bool := true

end FX1Poly.Polygraph
