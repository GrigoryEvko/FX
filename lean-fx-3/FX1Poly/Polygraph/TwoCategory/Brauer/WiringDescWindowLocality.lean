import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDesc

/-! # KEYSTONE4 leg 2 — the `natListSliceAt` window-locality geometry (the input-node correspondence core)

The cross-order disjoint-window witness needs the INPUT-node halves of the two blocks' trace correspondences:
firing a generator at a HORIZONTALLY-DISJOINT window does not change what a second generator reads.  With
`descA`'s window entirely left of `descB`'s (`positionA + descA.inputCount ≤ positionB`):

  * ★ **`natListSliceAt_spliceRight`** (Fact A) — `descA` reads the SAME input wires whether or not `descB` has
    already fired: a slice at `positionA` is invariant under a splice (`natListInsertAt ∘ natListRemoveManyAt`) at
    a disjoint RIGHT position `positionB ≥ positionA + width`.
  * ★ **`natListSliceAt_spliceLeftShift`** (Fact B) — `descB` reads the SAME input wires at its SHIFTED position:
    a slice at the shifted position `positionA + wA + extra` of the LEFT-spliced list (the splice at `positionA`
    replaces `rcA` wires with `wA`, moving everything past it) equals a slice at `positionA + rcA + extra` of the
    original.  Restated with the offset `extra = positionB - (positionA + rcA)` so the truncated subtraction never
    appears.

Both need the window to sit WITHIN the open-wire list (`… ≤ wires.length`): without it the empty-list past-end
degeneracy breaks slice-invariance (an insert past the end of an exhausted list surfaces the fresh block into an
otherwise-empty slice), which is exactly why the residual carries a range discipline.

The `natListSliceAt` / `natListInsertAt` / `natListRemoveManyAt` matchers split on the list (and count) before the
position, so the cons/zero reductions are not all `rfl`; the reduction-equation preamble below states each one and
proves it by the one `cases` the matcher needs.  Everything downstream is `rw` over those equations plus the
append-skip-prefix / drop-shift decompositions.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide`.  Per-declaration
`#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Reduction-equation preamble (the matcher splits on list/count before position) -/

/-- Slicing an exhausted list is empty, at any position / width. -/
theorem sliceAt_nil (position count : Nat) : natListSliceAt [] position count = [] := by
  cases count with
  | zero => rfl
  | succ _ => rfl

/-- A zero-width slice is empty. -/
theorem sliceAt_count_zero : (wires : List Nat) → (position : Nat) → natListSliceAt wires position 0 = []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: _, _ + 1 => rfl

/-- Slicing at a nonzero position peels the head off the list. -/
theorem sliceAt_cons_succ (headWire : Nat) (tailWires : List Nat) (position count : Nat) :
    natListSliceAt (headWire :: tailWires) (position + 1) count = natListSliceAt tailWires position count := by
  cases count with
  | zero => rw [sliceAt_count_zero (headWire :: tailWires) (position + 1), sliceAt_count_zero tailWires position]
  | succ _ => rfl

/-- Slicing a nonempty list at position `0` reads the head then recurses. -/
theorem sliceAt_cons_zero_succ (headWire : Nat) (tailWires : List Nat) (count : Nat) :
    natListSliceAt (headWire :: tailWires) 0 (count + 1) = headWire :: natListSliceAt tailWires 0 count := rfl

/-- Removing zero wires is a no-op. -/
theorem removeManyAt_zero : (wires : List Nat) → (position : Nat) → natListRemoveManyAt wires position 0 = wires
  | [], _ => rfl
  | _ :: _, _ => rfl

/-- Removing wires at a nonzero position peels the head. -/
theorem removeManyAt_succ_cons (headWire : Nat) (tailWires : List Nat) (position removeCount : Nat) :
    natListRemoveManyAt (headWire :: tailWires) (position + 1) removeCount
      = headWire :: natListRemoveManyAt tailWires position removeCount := by
  cases removeCount with
  | zero => rw [removeManyAt_zero (headWire :: tailWires) (position + 1), removeManyAt_zero tailWires position]
  | succ _ => rfl

/-- Removing at position `0` is a prefix drop. -/
theorem removeManyAt_zero_cons (headWire : Nat) (tailWires : List Nat) (removeCount : Nat) :
    natListRemoveManyAt (headWire :: tailWires) 0 (removeCount + 1)
      = natListRemoveManyAt tailWires 0 removeCount := rfl

/-- Inserting at position `0` prepends the block. -/
theorem insertAt_zero : (wires block : List Nat) → natListInsertAt wires 0 block = block ++ wires
  | [], _ => rfl
  | _ :: _, _ => rfl

/-- Inserting at a nonzero position peels the head. -/
theorem insertAt_succ_cons (headWire : Nat) (tailWires : List Nat) (position : Nat) (block : List Nat) :
    natListInsertAt (headWire :: tailWires) (position + 1) block
      = headWire :: natListInsertAt tailWires position block := rfl

/-! ## The splice-cons peel -/

/-- A splice (`natListInsertAt ∘ natListRemoveManyAt`) at a nonzero position preserves the head and recurses. -/
theorem splice_succ_cons (removeCount : Nat) (block : List Nat) (headWire : Nat) (tailWires : List Nat)
    (position : Nat) :
    natListInsertAt (natListRemoveManyAt (headWire :: tailWires) (position + 1) removeCount) (position + 1) block
      = headWire :: natListInsertAt (natListRemoveManyAt tailWires position removeCount) position block := by
  rw [removeManyAt_succ_cons headWire tailWires position removeCount,
    insertAt_succ_cons headWire (natListRemoveManyAt tailWires position removeCount) position block]

/-! ## The append-skip-prefix reduction -/

/-- Slicing past a whole prefix reads only the suffix. -/
theorem natListSliceAt_appendSkipPrefix (rest : List Nat) (extra count : Nat) :
    (front : List Nat) →
    natListSliceAt (front ++ rest) (front.length + extra) count = natListSliceAt rest extra count
  | [] => by
      show natListSliceAt rest (0 + extra) count = natListSliceAt rest extra count
      rw [Nat.zero_add]
  | frontHead :: frontRest => by
      show natListSliceAt (frontHead :: (frontRest ++ rest)) (frontRest.length + 1 + extra) count
          = natListSliceAt rest extra count
      rw [Nat.add_right_comm frontRest.length 1 extra,
        sliceAt_cons_succ frontHead (frontRest ++ rest) (frontRest.length + extra) count]
      exact natListSliceAt_appendSkipPrefix rest extra count frontRest

/-! ## The drop-shift reduction -/

/-- Reading past a dropped prefix: a slice at `removeCount + extra` of the original equals a slice at `extra` of
the list with its first `removeCount` wires removed. -/
theorem natListSliceAt_dropShift (extra count : Nat) :
    (wires : List Nat) → (removeCount : Nat) →
    natListSliceAt wires (removeCount + extra) count
      = natListSliceAt (natListRemoveManyAt wires 0 removeCount) extra count
  | wires, 0 => by
      rw [removeManyAt_zero wires 0]
      show natListSliceAt wires (0 + extra) count = natListSliceAt wires extra count
      rw [Nat.zero_add]
  | [], removeCount + 1 => by
      show natListSliceAt [] (removeCount + 1 + extra) count = natListSliceAt [] extra count
      rw [sliceAt_nil (removeCount + 1 + extra) count, sliceAt_nil extra count]
  | headWire :: tailWires, removeCount + 1 => by
      rw [removeManyAt_zero_cons headWire tailWires removeCount,
        Nat.add_right_comm removeCount 1 extra,
        sliceAt_cons_succ headWire tailWires (removeCount + extra) count]
      exact natListSliceAt_dropShift extra count tailWires removeCount

/-! ## Fact A — a left slice is invariant under a disjoint right splice -/

/-- ★ **Fact A: a slice at `position` is invariant under a splice at a disjoint RIGHT position.**  When the splice
position `splicePos` is at or beyond the end of the slice window (`position + count ≤ splicePos`) and within the
list (`splicePos ≤ wires.length`), replacing the `removeCount`-block at `splicePos` with `block` does not touch
what the window reads.  Structural on the wire list; the range bound rules out the empty-list past-end
degeneracy. -/
theorem natListSliceAt_spliceRight (removeCount : Nat) (block : List Nat) :
    (wires : List Nat) → (count position splicePos : Nat) →
    position + count ≤ splicePos → splicePos ≤ wires.length →
    natListSliceAt (natListInsertAt (natListRemoveManyAt wires splicePos removeCount) splicePos block)
        position count
      = natListSliceAt wires position count
  | wires, 0, position, _, _, _ => by
      rw [sliceAt_count_zero (natListInsertAt (natListRemoveManyAt wires _ removeCount) _ block) position,
        sliceAt_count_zero wires position]
  | [], count + 1, position, splicePos, windowLe, rangeLe =>
      absurd (Nat.le_trans windowLe rangeLe) (Nat.not_succ_le_zero (position + count))
  | headWire :: tailWires, count + 1, 0, splicePos, windowLe, rangeLe => by
      have windowLe' : count + 1 ≤ splicePos := by rw [Nat.zero_add] at windowLe; exact windowLe
      obtain ⟨splicePred, splicePosEq⟩ :=
        Nat.exists_eq_succ_of_ne_zero (fun isZero => Nat.not_succ_le_zero count (isZero ▸ windowLe'))
      subst splicePosEq
      rw [splice_succ_cons removeCount block headWire tailWires splicePred,
        sliceAt_cons_zero_succ headWire
          (natListInsertAt (natListRemoveManyAt tailWires splicePred removeCount) splicePred block) count,
        sliceAt_cons_zero_succ headWire tailWires count,
        natListSliceAt_spliceRight removeCount block tailWires count 0 splicePred
          (by rw [Nat.zero_add]; exact Nat.le_of_succ_le_succ windowLe') (Nat.le_of_succ_le_succ rangeLe)]
  | headWire :: tailWires, count + 1, position + 1, splicePos, windowLe, rangeLe => by
      obtain ⟨splicePred, splicePosEq⟩ :=
        Nat.exists_eq_succ_of_ne_zero (fun isZero =>
          Nat.not_succ_le_zero (position + 1 + count) (isZero ▸ windowLe))
      subst splicePosEq
      have windowRec : position + (count + 1) ≤ splicePred := by
        have shifted : position + 1 + (count + 1) ≤ splicePred + 1 := windowLe
        rw [Nat.add_right_comm position 1 (count + 1)] at shifted
        exact Nat.le_of_succ_le_succ shifted
      rw [splice_succ_cons removeCount block headWire tailWires splicePred,
        sliceAt_cons_succ headWire
          (natListInsertAt (natListRemoveManyAt tailWires splicePred removeCount) splicePred block)
          position (count + 1),
        sliceAt_cons_succ headWire tailWires position (count + 1),
        natListSliceAt_spliceRight removeCount block tailWires (count + 1) position splicePred
          windowRec (Nat.le_of_succ_le_succ rangeLe)]

/-! ## Fact B — a right slice reads the same at its shifted position after a left splice -/

/-- ★ **Fact B: a slice at the shifted position after a disjoint LEFT splice reads the original window.**  A
splice at `position` replaces `removeCount` wires with `block` (width `block.length`), moving everything past it;
so the window originally at `position + removeCount + extra` sits at `position + block.length + extra` in the
spliced list, and reads the same wires.  Restated with `extra` so the truncated subtraction never appears; the
range bound rules out the degenerate past-end case.  Structural on the wire list. -/
theorem natListSliceAt_spliceLeftShift (removeCount : Nat) (block : List Nat) :
    (wires : List Nat) → (count position extra : Nat) →
    position + removeCount + extra + count ≤ wires.length →
    natListSliceAt (natListInsertAt (natListRemoveManyAt wires position removeCount) position block)
        (position + block.length + extra) count
      = natListSliceAt wires (position + removeCount + extra) count
  | wires, count, 0, extra, _ => by
      rw [insertAt_zero (natListRemoveManyAt wires 0 removeCount) block, Nat.zero_add block.length,
        Nat.zero_add removeCount,
        natListSliceAt_appendSkipPrefix (natListRemoveManyAt wires 0 removeCount) extra count block,
        natListSliceAt_dropShift extra count wires removeCount]
  | [], count, position + 1, extra, rangeLe => by
      have collapsed : (position + removeCount + extra + count) + 1 ≤ 0 := by
        rw [Nat.add_right_comm position 1 removeCount, Nat.add_right_comm (position + removeCount) 1 extra,
          Nat.add_right_comm (position + removeCount + extra) 1 count] at rangeLe
        exact rangeLe
      exact absurd collapsed (Nat.not_succ_le_zero (position + removeCount + extra + count))
  | headWire :: tailWires, count, position + 1, extra, rangeLe => by
      rw [splice_succ_cons removeCount block headWire tailWires position,
        Nat.add_right_comm position 1 block.length, Nat.add_right_comm (position + block.length) 1 extra,
        sliceAt_cons_succ headWire
          (natListInsertAt (natListRemoveManyAt tailWires position removeCount) position block)
          (position + block.length + extra) count,
        Nat.add_right_comm position 1 removeCount, Nat.add_right_comm (position + removeCount) 1 extra,
        sliceAt_cons_succ headWire tailWires (position + removeCount + extra) count,
        natListSliceAt_spliceLeftShift removeCount block tailWires count position extra
          (Nat.le_of_succ_le_succ (by
            rw [Nat.add_right_comm position 1 removeCount, Nat.add_right_comm (position + removeCount) 1 extra,
              Nat.add_right_comm (position + removeCount + extra) 1 count] at rangeLe
            exact rangeLe))]

/-! ## Honesty marker -/

/-- **Honesty marker — the window-locality geometry is SHIPPED.**  Fact A (`natListSliceAt_spliceRight`: a left
slice is invariant under a disjoint right splice) and Fact B (`natListSliceAt_spliceLeftShift`: a right slice
reads the same window at its shifted position after a disjoint left splice) — the INPUT-node correspondences the
cross-order witness needs, each a structural induction over the wire list under a window-in-range discipline (the
degenerate past-end case genuinely breaks slice-invariance, which is why the residual is range-conditioned).
`= true`. -/
def fxBrauer_hasWiringDescWindowLocality : Bool := true

end FX1Poly.Polygraph
