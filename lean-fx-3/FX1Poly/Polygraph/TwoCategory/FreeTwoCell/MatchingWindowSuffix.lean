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

namespace FX1Poly.Polygraph

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

/-! ## Nat cancellation helpers (hand-rolled; core `Nat.add_right_cancel` leaks propext) -/

private theorem natAddRightCancel : (cancelled : Nat) → {leftSum rightSum : Nat} →
    leftSum + cancelled = rightSum + cancelled → leftSum = rightSum
  | 0, _, _, sumsEq => sumsEq
  | cancelled + 1, _, _, sumsEq => natAddRightCancel cancelled (Nat.succ.inj sumsEq)

private theorem natAddLeCancelRight : (cancelled : Nat) → {leftSum rightSum : Nat} →
    leftSum + cancelled ≤ rightSum + cancelled → leftSum ≤ rightSum
  | 0, _, _, sumsLe => sumsLe
  | cancelled + 1, _, _, sumsLe => natAddLeCancelRight cancelled (Nat.le_of_succ_le_succ sumsLe)

private theorem natAddLeMonoRight : (added : Nat) → {leftSide rightSide : Nat} →
    leftSide ≤ rightSide → leftSide + added ≤ rightSide + added
  | 0, _, _, sidesLe => sidesLe
  | added + 1, _, _, sidesLe => Nat.succ_le_succ (natAddLeMonoRight added sidesLe)

/-! ## The block layer: composing the atom shift over a whole cell -/

/-- Path composition adds word lengths (the additive strengthening of `composePath_length_left_le`). -/
theorem composePath_length {graph : ModeGraph} {sourceMode middleMode targetMode : graph.Mode} :
    (first : ModalityPath graph sourceMode middleMode) →
    (second : ModalityPath graph middleMode targetMode) →
    (composePath first second).length = first.length + second.length
  | .nil _, second => (Nat.zero_add second.length).symm
  | .cons _ rest, second => by
      show (composePath rest second).length + 1 = rest.length + 1 + second.length
      rw [Nat.add_right_comm rest.length 1 second.length]
      exact congrArg Nat.succ (composePath_length rest second)

/-- A vertical composite's fold runs the first factor and then the second (the block-level reading of
`processSpine_spineDiff`). -/
theorem runMatchingCell_vcomp {signature : ModeSignature}
    {overallSource overallTarget localSource localTarget : signature.graph.Mode}
    (state : WireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph localSource localTarget}
    (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
    (cellBeta : RawTwoCellExpr signature oneCellG oneCellH) :
    runMatchingCell state leftAcc rightAcc (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      = runMatchingCell (runMatchingCell state leftAcc rightAcc cellAlpha) leftAcc rightAcc
          cellBeta :=
  processSpine_spineDiff leftAcc rightAcc cellAlpha state (cellBeta.spineDiff leftAcc rightAcc [])

/-- The cup/cap generator discipline for a whole cell: every generator it contains is a `0 ⇒ 2` cup or a
`2 ⇒ 0` cap.  Every walking-adjunction cell satisfies this (unit = cup, counit = cap). -/
def CellHasCupCapGenerators {signature : ModeSignature} :
    {localSource localTarget : signature.graph.Mode} →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    RawTwoCellExpr signature localDom localCod → Prop
  | _, _, localDom, localCod, .gen _ =>
      (localDom.length = 0 ∧ localCod.length = 2) ∨ (localDom.length = 2 ∧ localCod.length = 0)
  | _, _, _, _, .id _ => True
  | _, _, _, _, .vcomp cellAlpha cellBeta =>
      CellHasCupCapGenerators cellAlpha ∧ CellHasCupCapGenerators cellBeta
  | _, _, _, _, .whiskerLeft _ body => CellHasCupCapGenerators body
  | _, _, _, _, .whiskerRight _ body => CellHasCupCapGenerators body

/-- ★ **A whole block's fold shifts the wire suffix by exactly its boundary delta.**  Under the cup/cap
generator discipline, reading at `window + offset + |localCod|` after `runMatchingCell` equals reading at
`window + offset + |localDom|` before it (window = the block's left-accumulator length), and the open-wire
count changes by the same delta — provided the block's source window is in range.  Structural cell
induction: a generator is the atom invariant, an identity is untouched, a vertical composite chains the two
factor invariants through `runMatchingCell_vcomp` (the middle boundary's range comes from the first
factor's count equation), and the two whiskerings re-anchor the window (`whiskerLeft` widens the
accumulator, `whiskerRight` widens the offset). -/
theorem runMatchingCell_openWiresSuffix_invariant {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAcc : ModalityPath signature.graph overallSource localSource) →
    (rightAcc : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (state : WireState) →
    CellHasCupCapGenerators cell →
    leftAcc.length + localDom.length ≤ state.openWires.length →
    (∀ offset : Nat,
      natListGetAt (runMatchingCell state leftAcc rightAcc cell).openWires
          (leftAcc.length + offset + localCod.length)
        = natListGetAt state.openWires (leftAcc.length + offset + localDom.length))
    ∧ (runMatchingCell state leftAcc rightAcc cell).openWires.length + localDom.length
        = state.openWires.length + localCod.length
  | _, _, leftAcc, rightAcc, _, _, .gen generator, state, cupCap, windowInRange =>
      ⟨fun offset => (stepAtom_openWiresSuffix_invariant state
          ⟨_, _, leftAcc, _, _, generator, rightAcc⟩ offset cupCap windowInRange).1,
        (stepAtom_openWiresSuffix_invariant state
          ⟨_, _, leftAcc, _, _, generator, rightAcc⟩ 0 cupCap windowInRange).2⟩
  | _, _, _, _, _, _, .id _, _, _, _ => ⟨fun _ => rfl, rfl⟩
  | _, _, leftAcc, rightAcc, _, _,
      @RawTwoCellExpr.vcomp _ _ _ oneCellF oneCellG oneCellH cellAlpha cellBeta,
      state, cupCap, windowInRange => by
      have alphaInvariant := runMatchingCell_openWiresSuffix_invariant leftAcc rightAcc cellAlpha
        state cupCap.1 windowInRange
      have paddedRange : leftAcc.length + oneCellG.length + oneCellF.length
          ≤ (runMatchingCell state leftAcc rightAcc cellAlpha).openWires.length
            + oneCellF.length := by
        rw [Nat.add_right_comm leftAcc.length oneCellG.length oneCellF.length,
          alphaInvariant.2]
        exact natAddLeMonoRight oneCellG.length windowInRange
      have betaInvariant := runMatchingCell_openWiresSuffix_invariant leftAcc rightAcc cellBeta
        (runMatchingCell state leftAcc rightAcc cellAlpha) cupCap.2
        (natAddLeCancelRight oneCellF.length paddedRange)
      rw [runMatchingCell_vcomp state leftAcc rightAcc cellAlpha cellBeta]
      exact ⟨fun offset => (betaInvariant.1 offset).trans (alphaInvariant.1 offset),
        natAddRightCancel oneCellG.length
          ((Nat.add_right_comm _ oneCellF.length oneCellG.length).trans
            ((congrArg (fun total => total + oneCellF.length) betaInvariant.2).trans
              ((Nat.add_right_comm _ oneCellH.length oneCellF.length).trans
                ((congrArg (fun total => total + oneCellH.length) alphaInvariant.2).trans
                  (Nat.add_right_comm _ oneCellG.length oneCellH.length)))))⟩
  | _, _, leftAcc, rightAcc, _, _,
      @RawTwoCellExpr.whiskerLeft _ _ _ _ oneCell oneCellG oneCellH body,
      state, cupCap, windowInRange => by
      have shiftedRange : (composePath leftAcc oneCell).length + oneCellG.length
          ≤ state.openWires.length := by
        rw [composePath_length leftAcc oneCell,
          Nat.add_assoc leftAcc.length oneCell.length oneCellG.length,
          ← composePath_length oneCell oneCellG]
        exact windowInRange
      have bodyInvariant := runMatchingCell_openWiresSuffix_invariant
        (composePath leftAcc oneCell) rightAcc body state cupCap shiftedRange
      constructor
      · intro offset
        have indexEq := bodyInvariant.1 offset
        rw [composePath_length leftAcc oneCell,
          Nat.add_right_comm leftAcc.length oneCell.length offset,
          Nat.add_assoc (leftAcc.length + offset) oneCell.length oneCellH.length,
          Nat.add_assoc (leftAcc.length + offset) oneCell.length oneCellG.length,
          ← composePath_length oneCell oneCellH,
          ← composePath_length oneCell oneCellG] at indexEq
        exact indexEq
      · show (runMatchingCell state (composePath leftAcc oneCell) rightAcc body).openWires.length
            + (composePath oneCell oneCellG).length
          = state.openWires.length + (composePath oneCell oneCellH).length
        rw [composePath_length oneCell oneCellG, composePath_length oneCell oneCellH,
          Nat.add_comm oneCell.length oneCellG.length,
          Nat.add_comm oneCell.length oneCellH.length,
          ← Nat.add_assoc, ← Nat.add_assoc, bodyInvariant.2]
  | _, _, leftAcc, rightAcc, _, _,
      @RawTwoCellExpr.whiskerRight _ _ _ _ oneCellF oneCellG oneCell body,
      state, cupCap, windowInRange => by
      have baseRange : leftAcc.length + oneCellF.length ≤ state.openWires.length := by
        rw [composePath_length oneCellF oneCell, ← Nat.add_assoc] at windowInRange
        exact Nat.le_trans
          (Nat.le_add_right (leftAcc.length + oneCellF.length) oneCell.length) windowInRange
      have bodyInvariant := runMatchingCell_openWiresSuffix_invariant
        leftAcc (composePath oneCell rightAcc) body state cupCap baseRange
      constructor
      · intro offset
        have indexEq := bodyInvariant.1 (offset + oneCell.length)
        rw [← Nat.add_assoc leftAcc.length offset oneCell.length,
          Nat.add_right_comm (leftAcc.length + offset) oneCell.length oneCellG.length,
          Nat.add_right_comm (leftAcc.length + offset) oneCell.length oneCellF.length,
          Nat.add_assoc (leftAcc.length + offset) oneCellG.length oneCell.length,
          Nat.add_assoc (leftAcc.length + offset) oneCellF.length oneCell.length,
          ← composePath_length oneCellG oneCell,
          ← composePath_length oneCellF oneCell] at indexEq
        exact indexEq
      · show (runMatchingCell state leftAcc (composePath oneCell rightAcc) body).openWires.length
            + (composePath oneCellF oneCell).length
          = state.openWires.length + (composePath oneCellG oneCell).length
        rw [composePath_length oneCellF oneCell, composePath_length oneCellG oneCell,
          ← Nat.add_assoc, ← Nat.add_assoc, bodyInvariant.2]

/-! ## Honesty markers -/

/-- **Honesty marker — the ATOM LAYER of the suffix shift is PROVED.**  Under the cup/cap arity discipline
(`AtomHasCupOrCapArity` — the whole walking-adjunction signature), one atom shifts every read at or beyond
its consumed window by exactly its arity delta, in value and in count
(`stepAtom_openWiresSuffix_invariant`); per-primitive lemmas cover the splice (`pastBlock`) and the pair
removal (`pastPair`), in the definitional `position + offset + width` index orientation.  The whole-block
composition is `fxMode_hasMatchingBlockSuffixShift` below.  `= true`. -/
def fxMode_hasMatchingAtomSuffixShift : Bool := true

/-- **Honesty marker — the BLOCK LAYER of the suffix shift is PROVED.**  Under the cup/cap generator
discipline (`CellHasCupCapGenerators`), a whole block's fold shifts every read at or beyond its window by
the block's net boundary delta, in value and in count (`runMatchingCell_openWiresSuffix_invariant`), by
structural cell induction over `runMatchingCell_vcomp` and the whisker re-anchorings.  Together with the
prefix half (`fxMode_hasMatchingWindowPrefixLocality`) this closes the VALUE bookkeeping of the block-swap
`openMap` obligation.  NOT yet proved: the FRESH-ID correspondence — the suffix values the two transposed
run orders read are equal only up to the `blockRotate` renaming of the two blocks' fresh ranges, so the σ
assembly (`fxMode_hasMatchingComponentCoreSwapWitness`) must thread the rotation through these invariants.
`= true`. -/
def fxMode_hasMatchingBlockSuffixShift : Bool := true

end FX1Poly.Polygraph
