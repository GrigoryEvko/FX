import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # ArcWindowCommutation — disjoint-position commutation of the wire-list operations (ARC-2b brick iii-1a)

The singleton-swap simulation (the peel's arc-invariance leg) needs the two run orders' wire
bookkeeping to commute: firing the HIGH-window atom first and then the LOW-window atom must
produce the same open-wire list as firing low-first with the high position shifted by the low
atom's net width.  At the walking adjunction every atom is a cup (splice two wires) or a cap
(remove two wires), so the whole geometric content is four commutation laws on
`natListInsertAt` / `natListRemoveTwoAt` at disjoint positions, plus the two append-prefix
shift laws they bottom out in.

Orientation: every law reads "high-op applied first, then low-op" (the ORIGINAL pair order at
a mirrored swap) equals "low-op first, then high-op at the shifted position" (the SWAPPED
order).  High positions are spelled `gap + lowPosition` / `gap + 2 + lowPosition` so both the
base and the step of each induction reduce definitionally (`x + (y + 1)` unfolds to
`(x + y) + 1` by `Nat.add`'s second-argument recursion); bounds are spelled with a trailing
`+ 2` so the out-of-range arms die by `Nat.not_succ_le_zero`.  The remove/remove law is
UNCONDITIONAL — pair removals at disjoint positions commute even out of range.

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in the
audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Append-prefix shift laws -/

/-- Splicing at a position shifted past a prefix lands inside the suffix: the prefix rides
along untouched. -/
theorem natListInsertAt_appendPrefix :
    (prefixWires : List Nat) → (wires : List Nat) → (position : Nat) → (block : List Nat) →
    natListInsertAt (prefixWires ++ wires) (prefixWires.length + position) block
      = prefixWires ++ natListInsertAt wires position block
  | [], wires, position, block => by
      show natListInsertAt wires (0 + position) block = natListInsertAt wires position block
      rw [Nat.zero_add]
  | headWire :: restPrefix, wires, position, block => by
      show natListInsertAt (headWire :: (restPrefix ++ wires))
            (restPrefix.length + 1 + position) block
          = headWire :: (restPrefix ++ natListInsertAt wires position block)
      rw [Nat.add_right_comm restPrefix.length 1 position]
      exact congrArg (headWire :: ·)
        (natListInsertAt_appendPrefix restPrefix wires position block)

/-- Removing a pair at a position shifted past a prefix removes inside the suffix: the prefix
rides along untouched. -/
theorem natListRemoveTwoAt_appendPrefix :
    (prefixWires : List Nat) → (wires : List Nat) → (position : Nat) →
    natListRemoveTwoAt (prefixWires ++ wires) (prefixWires.length + position)
      = prefixWires ++ natListRemoveTwoAt wires position
  | [], wires, position => by
      show natListRemoveTwoAt wires (0 + position) = natListRemoveTwoAt wires position
      rw [Nat.zero_add]
  | headWire :: restPrefix, wires, position => by
      show natListRemoveTwoAt (headWire :: (restPrefix ++ wires))
            (restPrefix.length + 1 + position)
          = headWire :: (restPrefix ++ natListRemoveTwoAt wires position)
      rw [Nat.add_right_comm restPrefix.length 1 position,
        natListRemoveTwoAt_succ headWire (restPrefix ++ wires) (restPrefix.length + position)]
      exact congrArg (headWire :: ·)
        (natListRemoveTwoAt_appendPrefix restPrefix wires position)

/-- Splicing at position `0` is prepending the block — as a REWRITE, because the compiled
matcher cases the list before the position, so `natListInsertAt wires 0 block` is stuck on a
variable or neutral `wires`. -/
theorem natListInsertAt_zero (wires block : List Nat) :
    natListInsertAt wires 0 block = block ++ wires := by
  cases wires with
  | nil => rfl
  | cons headWire restWires => rfl

/-! ## The four disjoint-position commutation laws -/

/-- ★ **Splice below commutes past splice above.**  Inserting `highBlock` at `gap + lowPosition`
and then `lowBlock` at `lowPosition` equals inserting low-first with the high position shifted
up by `lowBlock.length`.  The in-range bound on the HIGH position is required — an out-of-range
splice lands early and breaks the shift. -/
theorem natListInsertAt_insertAbove_commute :
    (wires : List Nat) → (lowPosition gap : Nat) → (lowBlock highBlock : List Nat) →
    gap + lowPosition ≤ wires.length →
    natListInsertAt (natListInsertAt wires (gap + lowPosition) highBlock) lowPosition lowBlock
      = natListInsertAt (natListInsertAt wires lowPosition lowBlock)
          (gap + lowBlock.length + lowPosition) highBlock
  | wires, 0, gap, lowBlock, highBlock, _ => by
      show natListInsertAt (natListInsertAt wires gap highBlock) 0 lowBlock
        = natListInsertAt (natListInsertAt wires 0 lowBlock) (gap + lowBlock.length) highBlock
      rw [natListInsertAt_zero (natListInsertAt wires gap highBlock) lowBlock,
        natListInsertAt_zero wires lowBlock, Nat.add_comm gap lowBlock.length,
        natListInsertAt_appendPrefix lowBlock wires gap highBlock]
  | [], lowPosition + 1, gap, lowBlock, highBlock, boundHigh =>
      absurd boundHigh (Nat.not_succ_le_zero _)
  | headWire :: restWires, lowPosition + 1, gap, lowBlock, highBlock, boundHigh =>
      congrArg (headWire :: ·)
        (natListInsertAt_insertAbove_commute restWires lowPosition gap lowBlock highBlock
          (Nat.le_of_succ_le_succ boundHigh))

/-- ★ **Pair removal below commutes past splice above.**  Inserting `highBlock` at
`gap + 2 + lowPosition` (strictly above the removed pair) and then removing the pair at
`lowPosition` equals removing first and inserting at the position shifted down by the removed
pair's width. -/
theorem natListRemoveTwoAt_insertAbove_commute :
    (wires : List Nat) → (lowPosition gap : Nat) → (highBlock : List Nat) →
    gap + lowPosition + 2 ≤ wires.length →
    natListRemoveTwoAt (natListInsertAt wires (gap + 2 + lowPosition) highBlock) lowPosition
      = natListInsertAt (natListRemoveTwoAt wires lowPosition) (gap + lowPosition) highBlock
  | [], _, _, _, boundHigh => absurd boundHigh (Nat.not_succ_le_zero _)
  | [_], 0, gap, _, boundHigh =>
      absurd (Nat.le_of_succ_le_succ boundHigh) (Nat.not_succ_le_zero gap)
  | _ :: _ :: _, 0, _, _, _ => rfl
  | firstWire :: restWires, lowPosition + 1, gap, highBlock, boundHigh => by
      show natListRemoveTwoAt
            (firstWire :: natListInsertAt restWires (gap + 2 + lowPosition) highBlock)
            (lowPosition + 1)
          = natListInsertAt (natListRemoveTwoAt (firstWire :: restWires) (lowPosition + 1))
              (gap + lowPosition + 1) highBlock
      rw [natListRemoveTwoAt_succ firstWire
          (natListInsertAt restWires (gap + 2 + lowPosition) highBlock) lowPosition,
        natListRemoveTwoAt_succ firstWire restWires lowPosition]
      exact congrArg (firstWire :: ·)
        (natListRemoveTwoAt_insertAbove_commute restWires lowPosition gap highBlock
          (Nat.le_of_succ_le_succ boundHigh))

/-- ★ **Splice below commutes past pair removal above.**  Removing the pair at
`gap + lowPosition` and then inserting `lowBlock` at `lowPosition` equals inserting first and
removing at the position shifted up by `lowBlock.length`. -/
theorem natListInsertAt_removeAbove_commute :
    (wires : List Nat) → (lowPosition gap : Nat) → (lowBlock : List Nat) →
    gap + lowPosition + 2 ≤ wires.length →
    natListInsertAt (natListRemoveTwoAt wires (gap + lowPosition)) lowPosition lowBlock
      = natListRemoveTwoAt (natListInsertAt wires lowPosition lowBlock)
          (gap + lowBlock.length + lowPosition)
  | wires, 0, gap, lowBlock, _ => by
      show natListInsertAt (natListRemoveTwoAt wires gap) 0 lowBlock
        = natListRemoveTwoAt (natListInsertAt wires 0 lowBlock) (gap + lowBlock.length)
      rw [natListInsertAt_zero (natListRemoveTwoAt wires gap) lowBlock,
        natListInsertAt_zero wires lowBlock, Nat.add_comm gap lowBlock.length,
        natListRemoveTwoAt_appendPrefix lowBlock wires gap]
  | [], lowPosition + 1, gap, lowBlock, boundHigh =>
      absurd boundHigh (Nat.not_succ_le_zero _)
  | headWire :: restWires, lowPosition + 1, gap, lowBlock, boundHigh => by
      show natListInsertAt (natListRemoveTwoAt (headWire :: restWires) (gap + lowPosition + 1))
            (lowPosition + 1) lowBlock
          = natListRemoveTwoAt (headWire :: natListInsertAt restWires lowPosition lowBlock)
              (gap + lowBlock.length + lowPosition + 1)
      rw [natListRemoveTwoAt_succ headWire restWires (gap + lowPosition),
        natListRemoveTwoAt_succ headWire (natListInsertAt restWires lowPosition lowBlock)
          (gap + lowBlock.length + lowPosition)]
      exact congrArg (headWire :: ·)
        (natListInsertAt_removeAbove_commute restWires lowPosition gap lowBlock
          (Nat.le_of_succ_le_succ boundHigh))

/-- ★ **Pair removal below commutes past pair removal above — UNCONDITIONALLY.**  Removing the
pair at `gap + 2 + lowPosition` and then the pair at `lowPosition` equals removing low-first
and then removing at the position shifted down by the low pair's width.  No range bound: both
orders agree even when a removal lands out of range (it is a no-op on both sides). -/
theorem natListRemoveTwoAt_removeAbove_commute :
    (wires : List Nat) → (lowPosition gap : Nat) →
    natListRemoveTwoAt (natListRemoveTwoAt wires (gap + 2 + lowPosition)) lowPosition
      = natListRemoveTwoAt (natListRemoveTwoAt wires lowPosition) (gap + lowPosition)
  | [], _, _ => rfl
  | [singleWire], 0, gap => by
      cases gap with
      | zero => rfl
      | succ _ => rfl
  | [_], _ + 1, _ => rfl
  | firstWire :: secondWire :: restWires, 0, gap => by
      show natListRemoveTwoAt
            (firstWire :: natListRemoveTwoAt (secondWire :: restWires) (gap + 1)) 0
          = natListRemoveTwoAt restWires gap
      rw [natListRemoveTwoAt_succ secondWire restWires gap]
      exact rfl
  | firstWire :: secondWire :: restWires, lowPosition + 1, gap => by
      show natListRemoveTwoAt
            (firstWire :: natListRemoveTwoAt (secondWire :: restWires) (gap + 2 + lowPosition))
            (lowPosition + 1)
          = natListRemoveTwoAt
              (firstWire :: natListRemoveTwoAt (secondWire :: restWires) lowPosition)
              (gap + lowPosition + 1)
      rw [natListRemoveTwoAt_succ firstWire
          (natListRemoveTwoAt (secondWire :: restWires) (gap + 2 + lowPosition)) lowPosition,
        natListRemoveTwoAt_succ firstWire
          (natListRemoveTwoAt (secondWire :: restWires) lowPosition) (gap + lowPosition)]
      exact congrArg (firstWire :: ·)
        (natListRemoveTwoAt_removeAbove_commute (secondWire :: restWires) lowPosition gap)

/-! ## Honesty marker -/

/-- **Honesty marker — the disjoint-position wire-op commutation kit is SHIPPED (ARC-2b brick
iii-1a).**  The four commutation laws (splice/splice, removal/splice, splice/removal,
removal/removal — the last unconditional) plus the two append-prefix shift laws they bottom
out in.  This is the pure list-level geometry of the singleton block swap: firing two
disjoint-window cup/cap atoms in either order produces the same open-wire list up to the fresh
block renaming.  NOT yet shipped: the fresh-block transposition `σ` itself, the two-step
`ArcStepSimCount` core simulation over the realized swap pairs (consuming these laws plus the
freshness invariants), and the arc-structure equality along one bubble step that
`arcRenameRel_of_arcStepSimCount` + `sameArcPartition_of_renameRel` +
`extractArc_eq_of_sameArcPartition` then read off.  `= true`. -/
def fxMode_hasArcWindowOpCommutation : Bool := true

end FX1Poly.Polygraph
