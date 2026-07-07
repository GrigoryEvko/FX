import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRangeInterleave

/-! # PureCapSurvivorTopHit — the mapped-range first-hit combinator (Piece II tail, 2b step 2 core)

The survivor read-off's top segment is `(List.range count).map (base + ·)` (with `base = bottomCount`).
Brick (2b) step 1 dropped the survivor's partner scan onto this segment; this file supplies the
generic FIRST-HIT combinator the scan then resolves with: if the exclude-and-root test fails at every
offset below `rank` and passes at `rank`, the scan over the base-shifted range returns `base + rank`.

The codebase's partner-scan kit skips a failing FRONT (`findPartnerScan_range_frontSegmentMisses`) but
had no "first passing candidate wins" combinator over a base-shifted range.  The obstruction is purely
structural: `List.range` is not cons-headed, so we first peel its front
(`mapRange_cons`: `(range (count+1)).map (base+·) = base :: (range count).map ((base+1)+·)`) via the
shipped `rangeSplit`, then recurse on `rank` — each miss skips the head, advancing `base` by one.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Peeling the front of a base-shifted range -/

/-- Two nested `(· + ·)` maps collapse: mapping `+1` then `+base` is mapping `+(base+1)`. -/
theorem mapAddCompose (base : Nat) :
    (values : List Nat) →
    (values.map (fun index => 1 + index)).map (fun index => base + index)
      = values.map (fun index => (base + 1) + index)
  | [] => rfl
  | head :: rest => by
      show (base + (1 + head))
          :: (rest.map (fun index => 1 + index)).map (fun index => base + index)
        = ((base + 1) + head) :: rest.map (fun index => (base + 1) + index)
      rw [mapAddCompose base rest, Nat.add_assoc base 1 head]

/-- ★ **The front of a base-shifted range peels off as a cons.**  `(range (count+1)).map (base + ·)`
is `base :: (range count).map ((base+1) + ·)` — the head is `base`, and the tail is the range one
shorter shifted one higher (`rangeSplit` at base `1`, then `mapAddCompose`). -/
theorem mapRange_cons (base count : Nat) :
    (List.range (count + 1)).map (fun index => base + index)
      = base :: (List.range count).map (fun index => (base + 1) + index) := by
  have split : List.range (count + 1)
      = 0 :: (List.range count).map (fun index => 1 + index) := by
    rw [Nat.add_comm count 1]; exact rangeSplit 1 count
  rw [split]
  show (base + 0)
      :: ((List.range count).map (fun index => 1 + index)).map (fun index => base + index)
    = base :: (List.range count).map (fun index => (base + 1) + index)
  rw [Nat.add_zero, mapAddCompose base (List.range count)]

/-! ## The first-hit combinator -/

/-- ★ **First passing candidate wins over a base-shifted range.**  If the exclude-and-root test
FAILS at every candidate `base + offset` with `offset < rank`, and PASSES at `base + rank`, then the
partner scan over `(List.range count).map (base + ·)` (with `rank < count`) returns `base + rank`.
By recursion on `rank`: at `0` the head hits; at `rank+1` the head fails (a below-`rank` miss) and the
scan advances to the one-higher, one-shorter tail (`mapRange_cons`), where the induction hypothesis
places the hit at `(base+1) + (rank-1) = base + rank`. -/
theorem findPartnerScan_mapRange_firstHit (links : List (Nat × Nat)) (boundaryNodes : List Nat)
    (rootHere excludeIndex : Nat) :
    (count rank base : Nat) → rank < count →
    (∀ offset, offset < rank →
      (base + offset != excludeIndex
          && unionFindRootOf links (natListGetAt boundaryNodes (base + offset)) == rootHere) = false) →
    (base + rank != excludeIndex
        && unionFindRootOf links (natListGetAt boundaryNodes (base + rank)) == rootHere) = true →
    findPartnerScan links boundaryNodes rootHere excludeIndex
        ((List.range count).map (fun index => base + index)) = base + rank
  | 0, _, _, rankLt, _, _ => absurd rankLt (Nat.not_lt_zero _)
  | count + 1, rank, base, rankLt, beforeMiss, hitAtRank => by
      rw [mapRange_cons base count]
      cases rank with
      | zero =>
          rw [findPartnerScan_cons links boundaryNodes rootHere excludeIndex base
            ((List.range count).map (fun index => (base + 1) + index))]
          exact if_pos hitAtRank
      | succ rankPred =>
          have headFails : (base != excludeIndex
              && unionFindRootOf links (natListGetAt boundaryNodes base) == rootHere) = false :=
            beforeMiss 0 (Nat.succ_pos rankPred)
          rw [findPartnerScan_cons_ofTestFails links boundaryNodes rootHere excludeIndex base
            ((List.range count).map (fun index => (base + 1) + index)) headFails]
          have shiftIndex : ∀ offset, (base + 1) + offset = base + (offset + 1) := fun offset =>
            (Nat.add_assoc base 1 offset).trans (congrArg (base + ·) (Nat.add_comm 1 offset))
          have beforeMissTail : ∀ offset, offset < rankPred →
              (base + 1 + offset != excludeIndex
                && unionFindRootOf links (natListGetAt boundaryNodes (base + 1 + offset)) == rootHere)
                = false := fun offset offsetLt =>
            (shiftIndex offset).symm ▸ beforeMiss (offset + 1) (Nat.succ_lt_succ offsetLt)
          have hitAtRankTail : (base + 1 + rankPred != excludeIndex
              && unionFindRootOf links (natListGetAt boundaryNodes (base + 1 + rankPred)) == rootHere)
              = true := (shiftIndex rankPred).symm ▸ hitAtRank
          rw [findPartnerScan_mapRange_firstHit links boundaryNodes rootHere excludeIndex
            count rankPred (base + 1) (Nat.lt_of_succ_lt_succ rankLt) beforeMissTail hitAtRankTail]
          exact shiftIndex rankPred

/-! ## Honesty marker -/

/-- **Honesty marker — the mapped-range first-hit combinator (2b step 2 core) is SHIPPED.**  The
generic "first passing candidate wins" partner scan over a base-shifted range
(`findPartnerScan_mapRange_firstHit`), built on the front-peel `mapRange_cons`.  This is the
combinator the codebase's partner-scan kit lacked.  NOT yet shipped: the survivor-specific wrapper
that instantiates it — reducing the top-candidate test to `openWires[offset] == survivor` (top read
`matchingBoundaryNodes_getAt_top`, survivor unlinked so it is its own root, and `bottomCount + offset
> survivor` so the exclude bang-inequality holds) with the miss/hit supplied by open-wire
distinctness at the survivor's rank.  That wrapper closes (2b); it feeds the F/G assembly.  No gate
flag is flipped.  `= true`. -/
def fxMode_hasPureCapSurvivorTopHit : Bool := true

end FX1Poly.Polygraph
