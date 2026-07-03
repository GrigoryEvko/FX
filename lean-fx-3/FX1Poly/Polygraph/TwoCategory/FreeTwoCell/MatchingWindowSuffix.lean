import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowLocality

/-! # mode-3 keystone — wire-window locality of the matching fold (the suffix shift, atom layer)

The block-swap witness's `openMap` needs BOTH halves of the wire-window locality: the prefix half
(`MatchingWindowLocality` — reads below the window survive) and this SUFFIX half — reads at or beyond an
atom's consumed window survive, SHIFTED by the atom's arity delta.  A cup (`0 ⇒ 2`) splices two wires at
the firing position, so suffix reads shift up by two; a cap (`2 ⇒ 0`) removes the pair, so suffix reads
shift down by two.  Uniformly: reading at `position + offset + |generatorCod|` AFTER equals reading at
`position + offset + |generatorDom|` BEFORE.

The invariant is CONDITIONED on the cup/cap arity discipline (`AtomHasCupOrCapArity`): the generic box arm
drops `|generatorDom|` PAIRS (two wires each), so its wire bookkeeping is dimensionally opaque — the
walking-adjunction seed (unit = cup, counit = cap) is exactly the conditioned fragment.

Index expressions keep the structural summand SECOND (`position + offset + width`, never
`width + position + offset`) so `Nat.add`'s second-argument recursion makes every literal-width step
definitional; the remaining rearrangements are `Nat.add_right_comm` / `Nat.zero_add` (propext-clean).

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Tier0

/-! ## Append primitives (the position-0 splice arm) -/

/-- Reading an appended list past the prefix block reads the tail (block length kept SECOND in the index
so every cons step is definitional). -/
theorem natListGetAt_append_pastBlock :
    (block : List Nat) → (wires : List Nat) → (offset : Nat) →
    natListGetAt (block ++ wires) (offset + block.length) = natListGetAt wires offset
  | [], _, _ => rfl
  | _ :: blockRest, wires, offset => natListGetAt_append_pastBlock blockRest wires offset

/-! ## Splice suffix primitives -/

/-- A splice at an in-range `position` shifts every read at or beyond the position up by the block's
length: reading at `position + offset + block.length` after equals reading at `position + offset`
before.  (The position-0 arm is split by list shape — `natListInsertAt`'s matcher cases the list first,
so a variable list is stuck.  The length fact is the banked `natListInsertAt_length`.) -/
theorem natListGetAt_natListInsertAt_pastBlock :
    (wires : List Nat) → (position : Nat) → (block : List Nat) → (offset : Nat) →
    position ≤ wires.length →
    natListGetAt (natListInsertAt wires position block) (position + offset + block.length)
      = natListGetAt wires (position + offset)
  | [], 0, block, offset, _ => by
      rw [Nat.zero_add]
      exact natListGetAt_append_pastBlock block [] offset
  | head :: rest, 0, block, offset, _ => by
      rw [Nat.zero_add]
      exact natListGetAt_append_pastBlock block (head :: rest) offset
  | [], _ + 1, _, _, le => absurd le (Nat.not_succ_le_zero _)
  | head :: rest, position + 1, block, offset, le => by
      show natListGetAt (head :: natListInsertAt rest position block)
            (position + 1 + offset + block.length)
          = natListGetAt (head :: rest) (position + 1 + offset)
      rw [Nat.add_right_comm position 1 offset,
        Nat.add_right_comm (position + offset) 1 block.length]
      exact natListGetAt_natListInsertAt_pastBlock rest position block offset
        (Nat.le_of_succ_le_succ le)

/-! ## Pair-removal suffix primitives -/

/-- A pair removal at `position` (with the pair in range) shifts every read at or beyond the position down
by two: reading at `position + offset` after equals reading at `position + offset + 2` before.  (The list
is split two-deep because `natListRemoveTwoAt`'s singleton arm makes its matcher case the tail.) -/
theorem natListGetAt_natListRemoveTwoAt_pastPair :
    (wires : List Nat) → (position : Nat) → (offset : Nat) →
    position + 2 ≤ wires.length →
    natListGetAt (natListRemoveTwoAt wires position) (position + offset)
      = natListGetAt wires (position + offset + 2)
  | [], _, _, le => absurd le (Nat.not_succ_le_zero _)
  | [_], 0, _, le => absurd (Nat.le_of_succ_le_succ le) (Nat.not_succ_le_zero 0)
  | [_], _ + 1, _, le => absurd (Nat.le_of_succ_le_succ le) (Nat.not_succ_le_zero _)
  | first :: second :: rest, 0, offset, _ => by
      show natListGetAt rest (0 + offset)
          = natListGetAt (first :: second :: rest) (0 + offset + 2)
      rw [Nat.zero_add]
      rfl
  | first :: second :: rest, position + 1, offset, le => by
      show natListGetAt (first :: natListRemoveTwoAt (second :: rest) position)
            (position + 1 + offset)
          = natListGetAt (first :: second :: rest) (position + 1 + offset + 2)
      rw [Nat.add_right_comm position 1 offset]
      exact natListGetAt_natListRemoveTwoAt_pastPair (second :: rest) position offset
        (Nat.le_of_succ_le_succ le)

/-- An in-range pair removal drops exactly two (additive form — no subtraction). -/
theorem natListRemoveTwoAt_length :
    (wires : List Nat) → (position : Nat) →
    position + 2 ≤ wires.length →
    (natListRemoveTwoAt wires position).length + 2 = wires.length
  | [], _, le => absurd le (Nat.not_succ_le_zero _)
  | [_], 0, le => absurd (Nat.le_of_succ_le_succ le) (Nat.not_succ_le_zero 0)
  | [_], _ + 1, le => absurd (Nat.le_of_succ_le_succ le) (Nat.not_succ_le_zero _)
  | _ :: _ :: _, 0, _ => rfl
  | _ :: second :: rest, position + 1, le =>
      congrArg Nat.succ (natListRemoveTwoAt_length (second :: rest) position
        (Nat.le_of_succ_le_succ le))

/-! ## The per-atom suffix invariant (cup/cap arity discipline) -/

/-- The cup/cap arity discipline: the atom's generator is a `0 ⇒ 2` cup or a `2 ⇒ 0` cap.  The whole
walking-adjunction signature satisfies this (unit = cup, counit = cap); the generic box arm is
dimensionally opaque (it drops pairs) and is excluded. -/
def AtomHasCupOrCapArity {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode) : Prop :=
  (atom.generatorDom.length = 0 ∧ atom.generatorCod.length = 2)
    ∨ (atom.generatorDom.length = 2 ∧ atom.generatorCod.length = 0)

/-- ★ **One cup/cap atom shifts the wire suffix by exactly its arity delta.**  Reading at
`position + offset + |generatorCod|` after the atom equals reading at `position + offset + |generatorDom|`
before it, and the open-wire count changes by the same delta (additive form) — provided the atom's consumed
window is in range. -/
theorem stepAtom_openWiresSuffix_invariant {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : WireState) (atom : SpineAtom signature sourceMode targetMode) (offset : Nat)
    (arity : AtomHasCupOrCapArity atom)
    (windowInRange : atom.leftContext.length + atom.generatorDom.length
      ≤ state.openWires.length) :
    natListGetAt (stepAtom state atom).openWires
        (atom.leftContext.length + offset + atom.generatorCod.length)
      = natListGetAt state.openWires
        (atom.leftContext.length + offset + atom.generatorDom.length)
    ∧ (stepAtom state atom).openWires.length + atom.generatorDom.length
        = state.openWires.length + atom.generatorCod.length := by
  cases arity with
  | inl cupArity =>
      have windowBase : atom.leftContext.length ≤ state.openWires.length := by
        rw [cupArity.1] at windowInRange
        exact windowInRange
      rw [stepAtom_ofCupArity state atom cupArity.1 cupArity.2, stepCup_openWires,
        cupArity.1, cupArity.2]
      exact ⟨natListGetAt_natListInsertAt_pastBlock state.openWires atom.leftContext.length
          [state.nextFresh, state.nextFresh + 1] offset windowBase,
        natListInsertAt_length state.openWires atom.leftContext.length
          [state.nextFresh, state.nextFresh + 1]⟩
  | inr capArity =>
      have windowPair : atom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [capArity.1] at windowInRange
        exact windowInRange
      rw [stepAtom_ofCapArity state atom capArity.1 capArity.2, stepCap_openWires,
        capArity.1, capArity.2]
      exact ⟨natListGetAt_natListRemoveTwoAt_pastPair state.openWires atom.leftContext.length
          offset windowPair,
        natListRemoveTwoAt_length state.openWires atom.leftContext.length windowPair⟩

/-! ## Honesty marker -/

/-- **Honesty marker — the ATOM LAYER of the suffix shift is PROVED.**  Under the cup/cap arity discipline
(`AtomHasCupOrCapArity` — the whole walking-adjunction signature), one atom shifts every read at or beyond
its consumed window by exactly its arity delta, in value and in count
(`stepAtom_openWiresSuffix_invariant`); per-primitive lemmas cover the splice (`pastBlock`) and the pair
removal (`pastPair`), in the definitional `position + offset + width` index orientation.  NOT yet proved:
the whole-BLOCK composition (fold the per-atom shift over `spineDiff` — the cell-level suffix
correspondence, needing the boundary-length bookkeeping of the cell induction) and the fresh-id
`blockRotate` relation between the two run orders; see `fxMode_hasMatchingComponentCoreSwapWitness`.
`= true`. -/
def fxMode_hasMatchingAtomSuffixShift : Bool := true

end FX1Poly.Tier0
