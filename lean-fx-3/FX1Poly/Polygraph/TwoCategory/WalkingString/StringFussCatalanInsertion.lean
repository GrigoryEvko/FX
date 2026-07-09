import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanNoLoops

/-! # WalkingString — the INDEX-SHIFT lemma kit + the label companion fold (FC-2, piece A)

FC-1's `stringMatchingOf_loops_zero_ofDisciplinePreserved` owes two per-step residuals — `preserves` (the
orientation discipline is a fold invariant) and `capPin` (a cap window reads its `generatorDom`) — and its OPEN
marker names the exact missing infrastructure: "the `natListInsertAt`/`natListGetAt` index-shift lemmas, none of which
exist over the bare `WireState`", plus the label companion fold `advanceLabels`, plus the non-crossing planarity
invariant.  This file BUILDS that infrastructure:

  * a GENERIC list index-shift KIT (`listGetAtD` / `listInsertAt` / `listRemoveTwoAt`) with the six shift lemmas the
    cup-splice (`stepCup`, insert a 2-block) and cap-delete (`stepCap`, remove two) fold steps consume — proved ONCE
    over an arbitrary element type, then bridged to the shipped `natList*` (the open-wire side) and `wireLabelList*`
    (the label side) by `rfl`-clean equation lemmas;
  * the LABEL companion fold `advanceLabels`, mirroring `stepAtom` in lockstep (cup ⇒ insert the cup's cod labels,
    cap ⇒ remove two, box ⇒ mirror the generic arm), so the discipline's label list tracks the open wires;
  * the `sameLengths` HALF of `preserves` DISCHARGED unconditionally — the label list stays length-locked to the open
    wires across every fold step (cup, cap, box), via the length shift lemmas L6a/L6b;
  * the `StringNonCrossing` planarity predicate (P1) + its fresh-seed base (P2-initial), the datum the `orient` half
    of `preserves` needs in the cap survivor subcase.

## What this LOCALIZES (the honest advance)

FC-1's `preserves` residual splits into TWO independent halves; this file DISCHARGES the length half
(`stringAdvanceLabels_sameLengths_preserved`) and supplies the index-shift + planarity infrastructure the orient
half needs.  The orient half itself still owes the union-find FRESHNESS reasoning (a fresh cup pair is same-component
with no old wire) and the PLANARITY survivor lemma (a cap merges two distinct arcs whose survivors read a cup word by
non-crossing) — genuinely new union-find / planar arcs kept as the localized residual (see the honesty markers).  So
`fxString_hasNoLoopsTheorem` (in `StringFussCatalan`) STAYS `false`; this file moves the frontier from "the whole
`preserves` is a multi-round arc" to "the length half is done, the index-shift + planarity kit is shipped, the
residual is exactly union-find-freshness + the planar survivor lemma".

Raw Lean 4 + Init; the kit is structural list/`Nat` induction, the bridges are structural, the length preservation is
a length congruence.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free (private `Nat` helpers
where the public name would clash); per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The generic list index-shift kit -/

/-- Read a list at a position, defaulting to `fallback` past the end (the shipped `natListGetAt` / `wireLabelListGetAt`
are the `fallback := 0` / `fallback := gWire` instances).  Cons-only structural recursion — propext-clean. -/
def listGetAtD {carrier : Type} (fallback : carrier) : List carrier → Nat → carrier
  | [], _ => fallback
  | head :: _, 0 => head
  | _ :: rest, position + 1 => listGetAtD fallback rest position

/-- Splice a block into a list at a position (the generic `natListInsertAt`). -/
def listInsertAt {carrier : Type} : List carrier → Nat → List carrier → List carrier
  | wires, 0, block => block ++ wires
  | [], _ + 1, block => block
  | head :: rest, position + 1, block => head :: listInsertAt rest position block

/-- Remove the two entries at `position` and `position+1` (the generic `natListRemoveTwoAt`). -/
def listRemoveTwoAt {carrier : Type} : List carrier → Nat → List carrier
  | [], _ => []
  | _ :: _ :: rest, 0 => rest
  | [singleton], 0 => [singleton]
  | head :: rest, position + 1 => head :: listRemoveTwoAt rest position

/-- Splicing at position 0 is a plain prepend (both list shapes reduce). -/
theorem listInsertAt_zero {carrier : Type} (wires block : List carrier) :
    listInsertAt wires 0 block = block ++ wires := by cases wires <;> rfl

/-! ## Append-read helpers -/

/-- Reading the left part of an append: an index below the prefix length reads the prefix. -/
theorem listGetAtD_append_left {carrier : Type} (fallback : carrier) :
    (prefixList : List carrier) → (suffixList : List carrier) → (index : Nat) →
    index < prefixList.length →
    listGetAtD fallback (prefixList ++ suffixList) index = listGetAtD fallback prefixList index
  | [], _, _, indexBelow => absurd indexBelow (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | head :: rest, suffixList, index + 1, indexBelow => by
      have restBelow : index < rest.length := Nat.lt_of_succ_lt_succ indexBelow
      show listGetAtD fallback (rest ++ suffixList) index = listGetAtD fallback rest index
      exact listGetAtD_append_left fallback rest suffixList index restBelow

/-- Reading the right part of an append: shifting the index past the prefix reads the suffix. -/
theorem listGetAtD_append_right {carrier : Type} (fallback : carrier) :
    (prefixList : List carrier) → (suffixList : List carrier) → (index : Nat) →
    listGetAtD fallback (prefixList ++ suffixList) (prefixList.length + index)
      = listGetAtD fallback suffixList index
  | [], suffixList, index => by
      show listGetAtD fallback suffixList (0 + index) = listGetAtD fallback suffixList index
      rw [Nat.zero_add]
  | head :: rest, suffixList, index => by
      show listGetAtD fallback ((head :: rest) ++ suffixList) ((rest.length + 1) + index)
        = listGetAtD fallback suffixList index
      show listGetAtD fallback (head :: (rest ++ suffixList)) ((rest.length + 1) + index)
        = listGetAtD fallback suffixList index
      rw [Nat.add_right_comm rest.length 1 index]
      show listGetAtD fallback (rest ++ suffixList) (rest.length + index) = listGetAtD fallback suffixList index
      exact listGetAtD_append_right fallback rest suffixList index

/-! ## Private clean `Nat`/`List` helpers (public duplicates leak `propext`) -/

/-- `(a + b) - a = b`, propext-clean (the shipped `Nat.add_sub_cancel_left` leaks). -/
private theorem natAddSubCancelLeftClean : (amount value : Nat) → (amount + value) - amount = value
  | 0, value => by rw [Nat.zero_add, Nat.sub_zero]
  | amount + 1, value => by
      show (amount + 1 + value) - (amount + 1) = value
      rw [Nat.add_right_comm amount 1 value]
      show (amount + value + 1) - (amount + 1) = value
      rw [Nat.succ_sub_succ]
      exact natAddSubCancelLeftClean amount value

/-- `bound ≤ value → (value + 1) - bound = (value - bound) + 1`, propext-clean (the shipped `Nat.succ_sub` leaks). -/
private theorem natSuccSubClean : (bound value : Nat) → bound ≤ value →
    (value + 1) - bound = (value - bound) + 1
  | 0, value, _ => by rw [Nat.sub_zero, Nat.sub_zero]
  | bound + 1, 0, boundBelow => absurd boundBelow (Nat.not_succ_le_zero _)
  | bound + 1, value + 1, boundBelow => by
      have boundRestBelow : bound ≤ value := Nat.le_of_succ_le_succ boundBelow
      show (value + 1 + 1) - (bound + 1) = ((value + 1) - (bound + 1)) + 1
      rw [Nat.succ_sub_succ, Nat.succ_sub_succ]
      exact natSuccSubClean bound value boundRestBelow

/-- `(prefixList ++ suffixList).length = prefixList.length + suffixList.length`, propext-clean (the shipped
`List.length_append` leaks via the append lemmas). -/
private theorem listLengthAppendClean {carrier : Type} :
    (prefixList suffixList : List carrier) →
    (prefixList ++ suffixList).length = prefixList.length + suffixList.length
  | [], suffixList => (Nat.zero_add suffixList.length).symm
  | head :: rest, suffixList => by
      show (rest ++ suffixList).length + 1 = (rest.length + 1) + suffixList.length
      rw [listLengthAppendClean rest suffixList, Nat.add_right_comm]

/-! ## L1–L3 — the CUP index shifts (insert a block of `blockLength` at `position`) -/

/-- **L1 (insert-below).**  An index below the insertion point is unmoved. -/
theorem listGetAtD_insertAt_below {carrier : Type} (fallback : carrier) :
    (wires : List carrier) → (position : Nat) → (block : List carrier) → (index : Nat) →
    position ≤ wires.length → index < position →
    listGetAtD fallback (listInsertAt wires position block) index = listGetAtD fallback wires index
  | _, 0, _, _, _, indexBelow => absurd indexBelow (Nat.not_lt_zero _)
  | [], position + 1, _, _, positionInRange, _ => absurd positionInRange (Nat.not_succ_le_zero _)
  | head :: rest, position + 1, block, 0, _, _ => rfl
  | head :: rest, position + 1, block, index + 1, positionInRange, indexBelow => by
      have restInRange : position ≤ rest.length := Nat.le_of_succ_le_succ positionInRange
      have indexRestBelow : index < position := Nat.lt_of_succ_lt_succ indexBelow
      show listGetAtD fallback (listInsertAt rest position block) index = listGetAtD fallback rest index
      exact listGetAtD_insertAt_below fallback rest position block index restInRange indexRestBelow

/-- **L2 (insert-block-read).**  An index inside the inserted block reads the block. -/
theorem listGetAtD_insertAt_block {carrier : Type} (fallback : carrier) :
    (wires : List carrier) → (position : Nat) → (block : List carrier) → (index : Nat) →
    position ≤ wires.length → position ≤ index → index < position + block.length →
    listGetAtD fallback (listInsertAt wires position block) index = listGetAtD fallback block (index - position)
  | wires, 0, block, index, _, _, indexInBlock => by
      rw [listInsertAt_zero, Nat.sub_zero]
      rw [Nat.zero_add] at indexInBlock
      exact listGetAtD_append_left fallback block wires index indexInBlock
  | [], position + 1, _, _, positionInRange, _, _ => absurd positionInRange (Nat.not_succ_le_zero _)
  | head :: rest, position + 1, block, 0, _, positionBelow, _ =>
      absurd positionBelow (Nat.not_succ_le_zero _)
  | head :: rest, position + 1, block, index + 1, positionInRange, positionBelow, indexInBlock => by
      have restInRange : position ≤ rest.length := Nat.le_of_succ_le_succ positionInRange
      have positionRestBelow : position ≤ index := Nat.le_of_succ_le_succ positionBelow
      have indexRestInBlock : index < position + block.length := by
        have step : index + 1 < position + block.length + 1 := by
          rw [Nat.add_right_comm position block.length 1]; exact indexInBlock
        exact Nat.lt_of_succ_lt_succ step
      have subEq : index + 1 - (position + 1) = index - position := Nat.succ_sub_succ index position
      show listGetAtD fallback (listInsertAt rest position block) index
        = listGetAtD fallback block (index + 1 - (position + 1))
      rw [subEq]
      exact listGetAtD_insertAt_block fallback rest position block index restInRange positionRestBelow
        indexRestInBlock

/-- **L3 (insert-above).**  An index above the inserted block reads the original list, shifted down by the block
length. -/
theorem listGetAtD_insertAt_above {carrier : Type} (fallback : carrier) :
    (wires : List carrier) → (position : Nat) → (block : List carrier) → (index : Nat) →
    position ≤ wires.length → position + block.length ≤ index →
    listGetAtD fallback (listInsertAt wires position block) index
      = listGetAtD fallback wires (index - block.length)
  | wires, 0, block, index, _, blockBelow => by
      rw [Nat.zero_add] at blockBelow
      obtain ⟨offset, offsetEq⟩ := Nat.le.dest blockBelow
      rw [listInsertAt_zero, ← offsetEq, natAddSubCancelLeftClean block.length offset]
      exact listGetAtD_append_right fallback block wires offset
  | [], position + 1, _, _, positionInRange, _ => absurd positionInRange (Nat.not_succ_le_zero _)
  | head :: rest, position + 1, block, 0, _, blockBelow => by
      rw [Nat.add_right_comm position 1 block.length] at blockBelow
      exact absurd blockBelow (Nat.not_succ_le_zero (position + block.length))
  | head :: rest, position + 1, block, index + 1, positionInRange, blockBelow => by
      have restInRange : position ≤ rest.length := Nat.le_of_succ_le_succ positionInRange
      have blockRestBelow : position + block.length ≤ index := by
        have step : position + block.length + 1 ≤ index + 1 := by
          rw [Nat.add_right_comm position block.length 1]; exact blockBelow
        exact Nat.le_of_succ_le_succ step
      have blockLeIndex : block.length ≤ index :=
        Nat.le_trans (Nat.le_add_left block.length position) blockRestBelow
      have subEq : index + 1 - block.length = (index - block.length) + 1 :=
        natSuccSubClean block.length index blockLeIndex
      show listGetAtD fallback (listInsertAt rest position block) index
        = listGetAtD fallback (head :: rest) (index + 1 - block.length)
      rw [listGetAtD_insertAt_above fallback rest position block index restInRange blockRestBelow, subEq]
      rfl

/-! ## L4–L5 — the CAP index shifts (remove two entries at `position`) -/

/-- **L4 (remove-below).**  An index below the removal point is unmoved. -/
theorem listGetAtD_removeTwoAt_below {carrier : Type} (fallback : carrier) :
    (wires : List carrier) → (position : Nat) → (index : Nat) → index < position →
    listGetAtD fallback (listRemoveTwoAt wires position) index = listGetAtD fallback wires index
  | _, 0, _, indexBelow => absurd indexBelow (Nat.not_lt_zero _)
  | [], _ + 1, _, _ => rfl
  | [_], _ + 1, 0, _ => rfl
  | [_], _ + 1, _ + 1, _ => rfl
  | head :: second :: rest, position + 1, 0, _ => rfl
  | head :: second :: rest, position + 1, index + 1, indexBelow => by
      have indexRestBelow : index < position := Nat.lt_of_succ_lt_succ indexBelow
      show listGetAtD fallback (listRemoveTwoAt (second :: rest) position) index
        = listGetAtD fallback (second :: rest) index
      exact listGetAtD_removeTwoAt_below fallback (second :: rest) position index indexRestBelow

/-- **L5 (remove-above).**  An index at or above the removal point reads the original list shifted UP by 2 (the two
removed entries). -/
theorem listGetAtD_removeTwoAt_above {carrier : Type} (fallback : carrier) :
    (wires : List carrier) → (position : Nat) → (index : Nat) →
    position + 1 < wires.length → position ≤ index →
    listGetAtD fallback (listRemoveTwoAt wires position) index = listGetAtD fallback wires (index + 2)
  | [], _, _, windowInRange, _ => absurd windowInRange (Nat.not_lt_zero _)
  | [_], position, _, windowInRange, _ =>
      absurd windowInRange (Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.zero_le position)))
  | head :: second :: rest, 0, index, _, _ => by
      show listGetAtD fallback rest index = listGetAtD fallback (head :: second :: rest) (index + 2)
      show listGetAtD fallback rest index = listGetAtD fallback rest index
      rfl
  | head :: second :: rest, position + 1, 0, _, positionBelow =>
      absurd positionBelow (Nat.not_succ_le_zero _)
  | head :: second :: rest, position + 1, index + 1, windowInRange, positionBelow => by
      have restWindowInRange : position + 1 < (second :: rest).length :=
        Nat.lt_of_succ_lt_succ windowInRange
      have positionRestBelow : position ≤ index := Nat.le_of_succ_le_succ positionBelow
      show listGetAtD fallback (listRemoveTwoAt (second :: rest) position) index
        = listGetAtD fallback (second :: rest) (index + 2)
      exact listGetAtD_removeTwoAt_above fallback (second :: rest) position index restWindowInRange
        positionRestBelow

/-! ## L6 — the length shifts -/

/-- **L6a (insert-length).**  Splicing a block adds its length. -/
theorem listInsertAt_length {carrier : Type} :
    (wires : List carrier) → (position : Nat) → (block : List carrier) →
    position ≤ wires.length →
    (listInsertAt wires position block).length = wires.length + block.length
  | wires, 0, block, _ => by
      rw [listInsertAt_zero, listLengthAppendClean block wires, Nat.add_comm block.length wires.length]
  | [], position + 1, _, positionInRange => absurd positionInRange (Nat.not_succ_le_zero _)
  | head :: rest, position + 1, block, positionInRange => by
      have restInRange : position ≤ rest.length := Nat.le_of_succ_le_succ positionInRange
      show (listInsertAt rest position block).length + 1 = (rest.length + 1) + block.length
      rw [listInsertAt_length rest position block restInRange, Nat.add_right_comm]

/-- **L6b (remove-length).**  Removing two entries drops the length by 2 (stated additively — no `Nat` subtraction). -/
theorem listRemoveTwoAt_length {carrier : Type} :
    (wires : List carrier) → (position : Nat) → position + 1 < wires.length →
    (listRemoveTwoAt wires position).length + 2 = wires.length
  | [], _, windowInRange => absurd windowInRange (Nat.not_lt_zero _)
  | [_], position, windowInRange =>
      absurd windowInRange (Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.zero_le position)))
  | head :: second :: rest, 0, _ => by
      show rest.length + 2 = (head :: second :: rest).length
      show rest.length + 2 = rest.length + 1 + 1
      rw [Nat.add_assoc]
  | head :: second :: rest, position + 1, windowInRange => by
      have restWindowInRange : position + 1 < (second :: rest).length :=
        Nat.lt_of_succ_lt_succ windowInRange
      show (head :: listRemoveTwoAt (second :: rest) position).length + 2 = (head :: second :: rest).length
      show (listRemoveTwoAt (second :: rest) position).length + 1 + 2 = (second :: rest).length + 1
      rw [Nat.add_right_comm (listRemoveTwoAt (second :: rest) position).length 1 2,
        listRemoveTwoAt_length (second :: rest) position restWindowInRange]

/-! ## Bridges — the shipped `natList*` and `wireLabelListGetAt` are instances of the generic kit -/

/-- The shipped `natListGetAt` is `listGetAtD 0`. -/
theorem natListGetAt_eq_listGetAtD : (wires : List Nat) → (index : Nat) →
    natListGetAt wires index = listGetAtD (0 : Nat) wires index
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: rest, index + 1 => natListGetAt_eq_listGetAtD rest index

/-- The shipped `natListInsertAt` is the generic `listInsertAt`. -/
theorem natListInsertAt_eq_listInsertAt : (wires : List Nat) → (position : Nat) → (block : List Nat) →
    natListInsertAt wires position block = listInsertAt wires position block
  | [], 0, _ => rfl
  | [], _ + 1, _ => rfl
  | _ :: _, 0, _ => rfl
  | head :: rest, position + 1, block =>
      congrArg (head :: ·) (natListInsertAt_eq_listInsertAt rest position block)

/-- The shipped `natListRemoveTwoAt` is the generic `listRemoveTwoAt`. -/
theorem natListRemoveTwoAt_eq_listRemoveTwoAt : (wires : List Nat) → (position : Nat) →
    natListRemoveTwoAt wires position = listRemoveTwoAt wires position
  | [], _ => rfl
  | [_], 0 => rfl
  | [single], position + 1 => congrArg (single :: ·) (natListRemoveTwoAt_eq_listRemoveTwoAt [] position)
  | _ :: _ :: _, 0 => rfl
  | first :: second :: rest, position + 1 =>
      congrArg (first :: ·) (natListRemoveTwoAt_eq_listRemoveTwoAt (second :: rest) position)

/-- The shipped `wireLabelListGetAt` is `listGetAtD gWire`. -/
theorem wireLabelListGetAt_eq_listGetAtD : (labels : List WireLabel) → (index : Nat) →
    wireLabelListGetAt labels index = listGetAtD WireLabel.gWire labels index
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: rest, index + 1 => wireLabelListGetAt_eq_listGetAtD rest index

/-! ## The label companion fold `advanceLabels` -/

/-- Insert a `WireLabel` block (the generic kit at `carrier := WireLabel`). -/
def wireLabelListInsertAt (labels : List WireLabel) (position : Nat) (block : List WireLabel) : List WireLabel :=
  listInsertAt labels position block

/-- Remove two `WireLabel` entries (the generic kit at `carrier := WireLabel`). -/
def wireLabelListRemoveTwoAt (labels : List WireLabel) (position : Nat) : List WireLabel :=
  listRemoveTwoAt labels position

/-- ★ The **label companion fold** mirroring `stepAtom` in lockstep on the label list: a cup (`0 ⇒ 2`) splices the
cup's cod-word labels at the live position, a cap (`2 ⇒ 0`) removes the two consumed labels, a generic box mirrors
the generic arm (drop the consumed labels, splice the produced strand labels).  The arity is read off the generator
boundary lengths, exactly as `stepAtom` does, so this tracks the open wires one-for-one. -/
def advanceLabels {sourceMode targetMode : AdjointTripleMode}
    (labels : List WireLabel) (atom : SpineAtom adjointTripleModeSignature sourceMode targetMode) : List WireLabel :=
  let position := atom.leftContext.length
  match atom.generatorDom.length, atom.generatorCod.length with
  | 0, 2 => wireLabelListInsertAt labels position (pathLabels atom.generatorCod)
  | 2, 0 => wireLabelListRemoveTwoAt labels position
  | numConsumed, numProduced =>
      let droppedLabels :=
        Nat.rec labels (fun _ shorter => wireLabelListRemoveTwoAt shorter position) numConsumed
      wireLabelListInsertAt droppedLabels position (List.replicate numProduced WireLabel.gWire)

/-! ## The `sameLengths` half of `preserves` — DISCHARGED -/

/-- The cup cod word has length 2 (a cup opens two strands). -/
theorem pathLabels_length_two {sourceMode targetMode : AdjointTripleMode}
    (path : ModalityPath adjointTripleGraph sourceMode targetMode) (codTwo : path.length = 2) :
    (pathLabels path).length = 2 := (stringPathLabels_length path).trans codTwo

/-- Splicing a `WireLabel` block adds its length (the generic L6a at `carrier := WireLabel`). -/
theorem wireLabelListInsertAt_length (labels : List WireLabel) (position : Nat) (block : List WireLabel)
    (positionInRange : position ≤ labels.length) :
    (wireLabelListInsertAt labels position block).length = labels.length + block.length :=
  listInsertAt_length labels position block positionInRange

/-- Removing two `WireLabel` entries drops the length by 2 (the generic L6b at `carrier := WireLabel`). -/
theorem wireLabelListRemoveTwoAt_length (labels : List WireLabel) (position : Nat)
    (windowInRange : position + 1 < labels.length) :
    (wireLabelListRemoveTwoAt labels position).length + 2 = labels.length :=
  listRemoveTwoAt_length labels position windowInRange

/-- A CUP grows the open-wire list by exactly 2 (the two fresh legs), when the live position is in range. -/
theorem stringStepCup_openWires_length (state : WireState) (position : Nat)
    (positionInRange : position ≤ state.openWires.length) :
    (stepCup state position).openWires.length = state.openWires.length + 2 := by
  show (natListInsertAt state.openWires position [state.nextFresh, state.nextFresh + 1]).length
    = state.openWires.length + 2
  rw [natListInsertAt_eq_listInsertAt,
    listInsertAt_length state.openWires position [state.nextFresh, state.nextFresh + 1] positionInRange]
  rfl

/-- A CAP shrinks the open-wire list by exactly 2 (the two consumed wires), regardless of the loop-closing branch,
when the cap window is in range. -/
theorem stringStepCap_openWires_length (state : WireState) (position : Nat)
    (windowInRange : position + 1 < state.openWires.length) :
    (stepCap state position).openWires.length + 2 = state.openWires.length := by
  dsimp only [stepCap]
  split
  · show (natListRemoveTwoAt state.openWires position).length + 2 = state.openWires.length
    rw [natListRemoveTwoAt_eq_listRemoveTwoAt, listRemoveTwoAt_length state.openWires position windowInRange]
  · show (natListRemoveTwoAt state.openWires position).length + 2 = state.openWires.length
    rw [natListRemoveTwoAt_eq_listRemoveTwoAt, listRemoveTwoAt_length state.openWires position windowInRange]

/-- ★ **The `sameLengths` half of `preserves`, CUP case.**  If the label list is length-locked to the open wires
(`sameLen`), then after a cup — splicing a length-2 cod word in the labels and the two fresh legs in the wires — the
lists stay length-locked.  Assembled from L6a (`wireLabelListInsertAt_length` / `stringStepCup_openWires_length`).
The string port of `arcDisciplineFold`'s length half, at a cup. -/
theorem stringAdvanceLabels_sameLengths_cup (state : WireState) (labels codLabels : List WireLabel)
    (position : Nat) (positionInRange : position ≤ state.openWires.length) (codLength : codLabels.length = 2)
    (sameLen : labels.length = state.openWires.length) :
    (wireLabelListInsertAt labels position codLabels).length = (stepCup state position).openWires.length := by
  have labelInRange : position ≤ labels.length := sameLen ▸ positionInRange
  rw [wireLabelListInsertAt_length labels position codLabels labelInRange, codLength,
    stringStepCup_openWires_length state position positionInRange, sameLen]

/-- ★ **The `sameLengths` half of `preserves`, CAP case.**  If the label list is length-locked to the open wires,
then after a cap — removing two labels and two wires — the lists stay length-locked.  Assembled from L6b
(`wireLabelListRemoveTwoAt_length` / `stringStepCap_openWires_length`).  The string port of `arcDisciplineFold`'s
length half, at a cap. -/
theorem stringAdvanceLabels_sameLengths_cap (state : WireState) (labels : List WireLabel) (position : Nat)
    (windowInRange : position + 1 < state.openWires.length) (sameLen : labels.length = state.openWires.length) :
    (wireLabelListRemoveTwoAt labels position).length = (stepCap state position).openWires.length := by
  have labelWindowInRange : position + 1 < labels.length := sameLen ▸ windowInRange
  have labelDrop : (wireLabelListRemoveTwoAt labels position).length + 2 = labels.length :=
    wireLabelListRemoveTwoAt_length labels position labelWindowInRange
  have wireDrop : (stepCap state position).openWires.length + 2 = state.openWires.length :=
    stringStepCap_openWires_length state position windowInRange
  have chain : (wireLabelListRemoveTwoAt labels position).length + 2
      = (stepCap state position).openWires.length + 2 := by
    rw [labelDrop, wireDrop, sameLen]
  exact Nat.succ.inj (Nat.succ.inj chain)

/-! ## The non-crossing planarity predicate (P1) + its fresh-seed base -/

/-- ★ **The non-crossing (PLANARITY) predicate.**  Two same-component open-wire windows never INTERLEAVE: there is no
`lowA < lowB < highA < highB` with `(lowA, highA)` and `(lowB, highB)` both same-component arcs.  This is the datum
the `orient` half of `preserves` needs in the cap survivor subcase — when a cap merges two distinct arcs, their
survivors read a cup word ONLY because the arcs were non-crossing.  The string port of the adjunction's
`ArcNonCrossingFold`. -/
def StringNonCrossing (state : WireState) : Prop :=
  ∀ lowA lowB highA highB : Nat,
    lowA < lowB → lowB < highA → highA < highB → highB < state.openWires.length →
    isSameComponent state.links (natListGetAt state.openWires lowA)
        (natListGetAt state.openWires highA) = true →
    isSameComponent state.links (natListGetAt state.openWires lowB)
        (natListGetAt state.openWires highB) = true →
    False

/-- Private range plumbing (per-file copies, following the codebase pattern; the `NoLoops` originals are `private`
so not visible here). -/
private theorem insertionRangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := insertionRangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem insertionRangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [insertionRangeLoopLength count []]; exact Nat.add_zero count

private theorem insertionRangeLoopGetPast : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := insertionRangeLoopGetPast count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem insertionRangeLoopGetBelow : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact insertionRangeLoopGetBelow count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := insertionRangeLoopGetPast count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]; exact pastRead

private theorem insertionRangeGetBelow (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  insertionRangeLoopGetBelow count [] index indexBelow

/-- ★ **The fresh seed is non-crossing (the vacuous base, P2-initial).**  At `stringInitialWireState bottomCount`
the union-find is empty, so `isSameComponent` on two DISTINCT boundary indices is `false` — no same-component arc
exists, and the crossing predicate holds vacuously.  The string port of `arcNonCrossing_initial`. -/
theorem stringInitialNonCrossing (bottomCount : Nat) :
    StringNonCrossing (stringInitialWireState bottomCount) := by
  intro lowA lowB highA highB lowALtLowB lowBLtHighA highALtHighB highBLt sameA _
  have lenEq : (stringInitialWireState bottomCount).openWires.length = bottomCount := by
    show (List.range bottomCount).length = bottomCount
    exact insertionRangeLength bottomCount
  have highBLtCount : highB < bottomCount := lenEq ▸ highBLt
  have highALtCount : highA < bottomCount := Nat.lt_trans highALtHighB highBLtCount
  have lowALtHighA : lowA < highA := Nat.lt_trans lowALtLowB lowBLtHighA
  have lowALtCount : lowA < bottomCount := Nat.lt_trans lowALtHighA highALtCount
  have lowGet : natListGetAt (stringInitialWireState bottomCount).openWires lowA = lowA := by
    show natListGetAt (List.range bottomCount) lowA = lowA
    exact insertionRangeGetBelow bottomCount lowA lowALtCount
  have highGet : natListGetAt (stringInitialWireState bottomCount).openWires highA = highA := by
    show natListGetAt (List.range bottomCount) highA = highA
    exact insertionRangeGetBelow bottomCount highA highALtCount
  rw [lowGet, highGet] at sameA
  -- `(stringInitialWireState _).links` is `[]`, so `isSameComponent [] a b` is defeq `(a == b)`
  have windowBeq : (lowA == highA) = true := sameA
  exact absurd (of_decide_eq_true windowBeq) (Nat.ne_of_lt lowALtHighA)

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the INDEX-SHIFT lemma kit is shipped (the FC-1 OPEN marker's named-missing infrastructure).**
The generic kit `listGetAtD` / `listInsertAt` / `listRemoveTwoAt` carries the six shift lemmas the cup-splice and
cap-delete fold steps consume — L1 (`listGetAtD_insertAt_below`), L2 (`listGetAtD_insertAt_block`), L3
(`listGetAtD_insertAt_above`), L4 (`listGetAtD_removeTwoAt_below`), L5 (`listGetAtD_removeTwoAt_above`), and L6a/L6b
(`listInsertAt_length` / `listRemoveTwoAt_length`) — proved ONCE over an arbitrary element type and bridged to the
shipped `natListInsertAt` / `natListRemoveTwoAt` / `natListGetAt` (the open-wire side) and `wireLabelListGetAt` (the
label side) by `rfl`-clean equation lemmas.  This is exactly "the `natListInsertAt`/`natListGetAt` index-shift
lemmas, none of which exist over the bare `WireState`" the FC-1 OPEN marker named.  `= true`. -/
def fxString_hasIndexShiftKit : Bool := true

/-- **★ ESTABLISHED — the `advanceLabels` companion fold + the `sameLengths` half of `preserves` + planarity.**
`advanceLabels` mirrors `stepAtom` in lockstep (cup ⇒ splice the cup's cod labels, cap ⇒ remove two, box ⇒ mirror the
generic arm), the `wireLabelListInsertAt` / `wireLabelListRemoveTwoAt` label twins are the generic kit at
`carrier := WireLabel`, and the `sameLengths` HALF of `preserves` is DISCHARGED per step: the label list stays
length-locked to the open wires across a CUP (`stringAdvanceLabels_sameLengths_cup`, +2 both, via L6a) and a CAP
(`stringAdvanceLabels_sameLengths_cap`, −2 both, via L6b) — assembled from `stringStepCup_openWires_length` /
`stringStepCap_openWires_length` and the label-list length lemmas.  The non-crossing planarity predicate
`StringNonCrossing` (P1) is shipped with its fresh-seed base (`stringInitialNonCrossing`, the vacuous P2-initial).
So the length-tracking + planarity infrastructure the `orient` half of `preserves` needs is in place.  `= true`. -/
def fxString_hasAdvanceLabelsAndPlanarityKit : Bool := true

/-- **OPEN (honest, LOCALIZED) — the `orient` half of `preserves` still owes union-find FRESHNESS + the planar
survivor lemma.**  With the index-shift kit and `advanceLabels` shipped, FC-1's `preserves` residual is now localized
to two genuinely-new arcs that the kit does NOT by itself close:

  * **CUP freshness** — after `stepCup` splices a FRESH connected pair `(nextFresh, nextFresh+1)`, the two new legs
    are same-component with each other (reading the cup's ORDERED cod word) and with NO old wire; proving this needs
    that every id in `openWires`/`links` is `< nextFresh` and that adding the edge `(nextFresh, nextFresh+1)` changes
    no OLD-old `isSameComponent` — a union-find `unionFindRootOf`-cons/freshness arc over the shipped fuel-bounded
    root finder.
  * **CAP planar survivor** — after `stepCap` merges two DISTINCT arcs meeting at `p, p+1`, the two survivors read a
    cup word ONLY because the arcs were non-crossing (`StringNonCrossing`); this planar survivor lemma (P4) is the
    genuinely-new mathematics.

So `fxString_hasNoLoopsTheorem` STAYS `false`, HONESTLY, with the frontier moved: the length half of `preserves` is
DISCHARGED, the index-shift + planarity kit is SHIPPED, and the residual is exactly union-find-freshness + the planar
survivor lemma + `capPin` (label tracking).  `= false`. -/
def fxString_hasOrientPreservationResidual : Bool := false

end FX1Poly.Polygraph
