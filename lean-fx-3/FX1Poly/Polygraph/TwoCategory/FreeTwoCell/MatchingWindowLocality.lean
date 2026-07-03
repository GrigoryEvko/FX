import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFoldCongruence

/-! # mode-3 keystone — wire-window locality of the matching fold (the prefix half)

The block-swap witness runs two blocks in transposed orders; its `openMap` field needs the fold's wire
bookkeeping to be LOCAL to each block's window.  This file ships the PREFIX half: every atom fires at its
live position `leftContext.length`, and all three wire updates (`natListInsertAt`, `natListRemoveTwoAt`,
the box arm's iterated drop-then-insert) leave positions strictly below the firing position untouched — so
a spine whose atoms all fire at or beyond a window start (`SpineFiresAtOrBeyond`) preserves every
`natListGetAt` read below that window, and keeps the read in range.

The in-range half (`index < wires.length`) is carried through the invariant because a cap SHRINKS the list:
prefix reads survive a removal at a higher position, but composing across the fold needs the survival of
the range bound too.

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Primitive prefix lemmas -/

/-- A splice at `position` leaves reads strictly below untouched (in-range reads — an out-of-range splice
lands early, which is why the range bound is a hypothesis). -/
theorem natListGetAt_natListInsertAt_below :
    (wires : List Nat) → (position : Nat) → (block : List Nat) → (index : Nat) →
    index < position → index < wires.length →
    natListGetAt (natListInsertAt wires position block) index = natListGetAt wires index
  | _, 0, _, index, belowPosition, _ => absurd belowPosition (Nat.not_lt_zero index)
  | [], _ + 1, _, index, _, belowLength => absurd belowLength (Nat.not_lt_zero index)
  | _ :: _, _ + 1, _, 0, _, _ => rfl
  | _ :: rest, position + 1, block, index + 1, belowPosition, belowLength =>
      natListGetAt_natListInsertAt_below rest position block index
        (Nat.lt_of_succ_lt_succ belowPosition) (Nat.lt_of_succ_lt_succ belowLength)

/-- A splice never loses an in-range read strictly below the splice position. -/
theorem natListInsertAt_length_above :
    (wires : List Nat) → (position : Nat) → (block : List Nat) → (index : Nat) →
    index < position → index < wires.length →
    index < (natListInsertAt wires position block).length
  | _, 0, _, index, belowPosition, _ => absurd belowPosition (Nat.not_lt_zero index)
  | [], _ + 1, _, index, _, belowLength => absurd belowLength (Nat.not_lt_zero index)
  | _ :: _, _ + 1, _, 0, _, _ => Nat.succ_le_succ (Nat.zero_le _)
  | _ :: rest, position + 1, block, index + 1, belowPosition, belowLength =>
      Nat.succ_lt_succ (natListInsertAt_length_above rest position block index
        (Nat.lt_of_succ_lt_succ belowPosition) (Nat.lt_of_succ_lt_succ belowLength))

/-- A pair removal at `position` leaves reads strictly below untouched.  (The list is split two-deep
because `natListRemoveTwoAt`'s singleton arm makes its matcher case the tail — a variable tail is stuck.) -/
theorem natListGetAt_natListRemoveTwoAt_below :
    (wires : List Nat) → (position : Nat) → (index : Nat) → index < position →
    natListGetAt (natListRemoveTwoAt wires position) index = natListGetAt wires index
  | _, 0, index, belowPosition => absurd belowPosition (Nat.not_lt_zero index)
  | [], _ + 1, _, _ => rfl
  | _ :: [], _ + 1, _, _ => rfl
  | _ :: _ :: _, _ + 1, 0, _ => rfl
  | _ :: second :: rest, position + 1, index + 1, belowPosition =>
      natListGetAt_natListRemoveTwoAt_below (second :: rest) position index
        (Nat.lt_of_succ_lt_succ belowPosition)

/-- A pair removal at `position` never loses an in-range read strictly below it. -/
theorem natListRemoveTwoAt_length_above :
    (wires : List Nat) → (position : Nat) → (index : Nat) →
    index < position → index < wires.length →
    index < (natListRemoveTwoAt wires position).length
  | _, 0, index, belowPosition, _ => absurd belowPosition (Nat.not_lt_zero index)
  | [], _ + 1, index, _, belowLength => absurd belowLength (Nat.not_lt_zero index)
  | _ :: [], _ + 1, 0, _, _ => Nat.succ_le_succ (Nat.zero_le _)
  | _ :: [], _ + 1, index + 1, _, belowLength =>
      absurd (Nat.lt_of_succ_lt_succ belowLength) (Nat.not_lt_zero index)
  | _ :: _ :: _, _ + 1, 0, _, _ => Nat.succ_le_succ (Nat.zero_le _)
  | _ :: second :: rest, position + 1, index + 1, belowPosition, belowLength =>
      Nat.succ_lt_succ (natListRemoveTwoAt_length_above (second :: rest) position index
        (Nat.lt_of_succ_lt_succ belowPosition) (Nat.lt_of_succ_lt_succ belowLength))

/-! ## The box arm's iterated drop-then-insert -/

/-- The generic box arm's iterated pair removal preserves prefix reads and their range (composition of
`natListGetAt_natListRemoveTwoAt_below` / `natListRemoveTwoAt_length_above` along the `Nat.rec` iterate,
stated about the raw `Nat.rec` so it unifies with `stepAtom`'s arm definitionally). -/
private theorem iteratedRemovePrefixInvariant (position index : Nat)
    (belowPosition : index < position) :
    (repetitions : Nat) → (wires : List Nat) → index < wires.length →
    natListGetAt (Nat.rec (motive := fun _ => List Nat) wires
        (fun _ shorter => natListRemoveTwoAt shorter position) repetitions) index
        = natListGetAt wires index
      ∧ index < (Nat.rec (motive := fun _ => List Nat) wires
          (fun _ shorter => natListRemoveTwoAt shorter position) repetitions).length
  | 0, _, belowLength => ⟨rfl, belowLength⟩
  | repetitions + 1, wires, belowLength =>
      have tailInvariant := iteratedRemovePrefixInvariant position index belowPosition
        repetitions wires belowLength
      ⟨(natListGetAt_natListRemoveTwoAt_below _ position index belowPosition).trans
          tailInvariant.1,
        natListRemoveTwoAt_length_above _ position index belowPosition tailInvariant.2⟩

/-- The whole box arm (drop `numConsumed` pairs, splice the fresh block) preserves prefix reads and their
range below the firing position. -/
private theorem boxArmPrefixInvariant (wires : List Nat) (position : Nat) (freshBlock : List Nat)
    (numConsumed index : Nat)
    (belowPosition : index < position) (belowLength : index < wires.length) :
    natListGetAt (natListInsertAt (Nat.rec (motive := fun _ => List Nat) wires
        (fun _ shorter => natListRemoveTwoAt shorter position) numConsumed) position freshBlock)
        index
        = natListGetAt wires index
      ∧ index < (natListInsertAt (Nat.rec (motive := fun _ => List Nat) wires
          (fun _ shorter => natListRemoveTwoAt shorter position) numConsumed) position
          freshBlock).length :=
  have droppedInvariant := iteratedRemovePrefixInvariant position index belowPosition
    numConsumed wires belowLength
  ⟨(natListGetAt_natListInsertAt_below _ position freshBlock index belowPosition
      droppedInvariant.2).trans droppedInvariant.1,
    natListInsertAt_length_above _ position freshBlock index belowPosition droppedInvariant.2⟩

/-! ## The per-atom prefix invariant -/

/-- ★ **One atom leaves the wire prefix below its firing position untouched, and in range.**  Cup splices
at the position, cap removes at the position, the box arm drops-then-splices at the position — all three
are invisible strictly below it.  Literal-arity case tree (the `stepAtom` matcher reduces on
literal-headed arities). -/
theorem stepAtom_openWiresPrefix_invariant {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : WireState) (atom : SpineAtom signature sourceMode targetMode) (index : Nat)
    (belowPosition : index < atom.leftContext.length)
    (belowLength : index < state.openWires.length) :
    natListGetAt (stepAtom state atom).openWires index = natListGetAt state.openWires index
      ∧ index < (stepAtom state atom).openWires.length := by
  cases hdom : atom.generatorDom.length with
  | zero =>
      cases hcod : atom.generatorCod.length with
      | zero =>
          unfold stepAtom; rw [hdom, hcod]
          exact boxArmPrefixInvariant state.openWires atom.leftContext.length
            ((List.range 0).map (· + state.nextFresh)) 0 index belowPosition belowLength
      | succ codPred =>
          cases codPred with
          | zero =>
              unfold stepAtom; rw [hdom, hcod]
              exact boxArmPrefixInvariant state.openWires atom.leftContext.length
                ((List.range 1).map (· + state.nextFresh)) 0 index belowPosition belowLength
          | succ codPredPred =>
              cases codPredPred with
              | zero =>
                  rw [stepAtom_ofCupArity state atom hdom hcod]
                  exact ⟨natListGetAt_natListInsertAt_below state.openWires
                      atom.leftContext.length [state.nextFresh, state.nextFresh + 1] index
                      belowPosition belowLength,
                    natListInsertAt_length_above state.openWires atom.leftContext.length
                      [state.nextFresh, state.nextFresh + 1] index belowPosition belowLength⟩
              | succ codRest =>
                  unfold stepAtom; rw [hdom, hcod]
                  exact boxArmPrefixInvariant state.openWires atom.leftContext.length
                    ((List.range (codRest + 1 + 1 + 1)).map (· + state.nextFresh)) 0 index
                    belowPosition belowLength
  | succ domPred =>
      cases domPred with
      | zero =>
          unfold stepAtom; rw [hdom]
          exact boxArmPrefixInvariant state.openWires atom.leftContext.length
            ((List.range atom.generatorCod.length).map (· + state.nextFresh)) 1 index
            belowPosition belowLength
      | succ domPredPred =>
          cases domPredPred with
          | zero =>
              cases hcod : atom.generatorCod.length with
              | zero =>
                  rw [stepAtom_ofCapArity state atom hdom hcod, stepCap_openWires]
                  exact ⟨natListGetAt_natListRemoveTwoAt_below state.openWires
                      atom.leftContext.length index belowPosition,
                    natListRemoveTwoAt_length_above state.openWires atom.leftContext.length
                      index belowPosition belowLength⟩
              | succ codPred =>
                  unfold stepAtom; rw [hdom, hcod]
                  exact boxArmPrefixInvariant state.openWires atom.leftContext.length
                    ((List.range (codPred + 1)).map (· + state.nextFresh)) 2 index
                    belowPosition belowLength
          | succ domRest =>
              unfold stepAtom; rw [hdom]
              exact boxArmPrefixInvariant state.openWires atom.leftContext.length
                ((List.range atom.generatorCod.length).map (· + state.nextFresh))
                (domRest + 1 + 1 + 1) index belowPosition belowLength

/-! ## The spine-level window predicate + fold -/

/-- Every atom of the spine fires at or beyond the window start (its live position
`leftContext.length` is at least `windowStart`). -/
def SpineFiresAtOrBeyond {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (windowStart : Nat) : List (SpineAtom signature sourceMode targetMode) → Prop
  | [] => True
  | atom :: rest => windowStart ≤ atom.leftContext.length ∧ SpineFiresAtOrBeyond windowStart rest

/-- ★ **The wire prefix below the window survives a whole spine** — every read strictly below the window
start is unchanged by `processSpine`, and stays in range, when all atoms fire at or beyond the window.
This is the prefix half of the block-swap witness's `openMap` locality. -/
theorem processSpine_openWiresPrefix_invariant {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (windowStart index : Nat)
    (belowWindow : index < windowStart) :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : WireState) →
    SpineFiresAtOrBeyond windowStart atoms → index < state.openWires.length →
    natListGetAt (processSpine state atoms).openWires index = natListGetAt state.openWires index
      ∧ index < (processSpine state atoms).openWires.length
  | [], _, _, belowLength => ⟨rfl, belowLength⟩
  | atom :: rest, state, fires, belowLength => by
      show natListGetAt (processSpine (stepAtom state atom) rest).openWires index
            = natListGetAt state.openWires index
          ∧ index < (processSpine (stepAtom state atom) rest).openWires.length
      obtain ⟨stepEq, stepLength⟩ := stepAtom_openWiresPrefix_invariant state atom index
        (Nat.lt_of_lt_of_le belowWindow fires.1) belowLength
      obtain ⟨restEq, restLength⟩ := processSpine_openWiresPrefix_invariant windowStart index
        belowWindow rest (stepAtom state atom) fires.2 stepLength
      exact ⟨restEq.trans stepEq, restLength⟩

/-! ## The spineDiff window lower bound -/

/-- The left factor of a path composite is no longer than the composite (`composePath` recurses on the
first path, so the word length only grows to the right). -/
theorem composePath_length_left_le {graph : ModeGraph}
    {sourceMode middleMode targetMode : graph.Mode} :
    (first : ModalityPath graph sourceMode middleMode) →
    (second : ModalityPath graph middleMode targetMode) →
    first.length ≤ (composePath first second).length
  | .nil _, second => Nat.zero_le second.length
  | .cons _ rest, second => Nat.succ_le_succ (composePath_length_left_le rest second)

/-- ★ **Every atom of a `spineDiff` block fires at or beyond the block's left-accumulator window.**  The
flattening only ever EXTENDS the left accumulator (`gen` records it verbatim as the atom's live position,
`whiskerLeft` composes onto it), so a window start at or below the accumulator length bounds every firing
position — provided the tail already fires at or beyond it. -/
theorem spineDiff_firesAtOrBeyond {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} (windowStart : Nat) :
    {localSource localTarget : signature.graph.Mode} →
    (leftAccumulator : ModalityPath signature.graph overallSource localSource) →
    (rightAccumulator : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (rest : List (SpineAtom signature overallSource overallTarget)) →
    windowStart ≤ leftAccumulator.length → SpineFiresAtOrBeyond windowStart rest →
    SpineFiresAtOrBeyond windowStart (cell.spineDiff leftAccumulator rightAccumulator rest)
  | _, _, _, _, _, _, .gen _, _, windowLe, restFires => ⟨windowLe, restFires⟩
  | _, _, _, _, _, _, .id _, _, _, restFires => restFires
  | _, _, leftAccumulator, rightAccumulator, _, _, .vcomp cellAlpha cellBeta, rest, windowLe,
      restFires =>
      spineDiff_firesAtOrBeyond windowStart leftAccumulator rightAccumulator cellAlpha
        (cellBeta.spineDiff leftAccumulator rightAccumulator rest) windowLe
        (spineDiff_firesAtOrBeyond windowStart leftAccumulator rightAccumulator cellBeta rest
          windowLe restFires)
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerLeft oneCell body, rest, windowLe,
      restFires =>
      spineDiff_firesAtOrBeyond windowStart (composePath leftAccumulator oneCell) rightAccumulator
        body rest (Nat.le_trans windowLe (composePath_length_left_le leftAccumulator oneCell))
        restFires
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerRight oneCell body, rest, windowLe,
      restFires =>
      spineDiff_firesAtOrBeyond windowStart leftAccumulator (composePath oneCell rightAccumulator)
        body rest windowLe restFires

/-- A whole cell's spine block fires at or beyond its own left accumulator's length — the block's own
window (empty tail, reflexive bound). -/
theorem spineDiff_firesAtOrBeyond_ownWindow {signature : ModeSignature}
    {overallSource overallTarget localSource localTarget : signature.graph.Mode}
    (leftAccumulator : ModalityPath signature.graph overallSource localSource)
    (rightAccumulator : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod) :
    SpineFiresAtOrBeyond leftAccumulator.length
      (cell.spineDiff leftAccumulator rightAccumulator []) :=
  spineDiff_firesAtOrBeyond leftAccumulator.length leftAccumulator rightAccumulator cell []
    (Nat.le_refl leftAccumulator.length) True.intro

/-- ★ **A block's fold cannot see the wire prefix below its own window** — `runMatchingCell` leaves every
read strictly below the left accumulator's length untouched, in value AND in range.  The prefix half of
the block-swap witness's `openMap` obligation, at block granularity. -/
theorem runMatchingCell_openWiresPrefix_invariant {signature : ModeSignature}
    {overallSource overallTarget localSource localTarget : signature.graph.Mode}
    (state : WireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod) (index : Nat)
    (belowWindow : index < leftAcc.length) (belowLength : index < state.openWires.length) :
    natListGetAt (runMatchingCell state leftAcc rightAcc cell).openWires index
        = natListGetAt state.openWires index
      ∧ index < (runMatchingCell state leftAcc rightAcc cell).openWires.length :=
  processSpine_openWiresPrefix_invariant leftAcc.length index belowWindow
    (cell.spineDiff leftAcc rightAcc []) state
    (spineDiff_firesAtOrBeyond_ownWindow leftAcc rightAcc cell) belowLength

/-! ## Honesty marker -/

/-- **Honesty marker — the PREFIX half of the wire-window locality is PROVED, at block granularity.**
Reads strictly below a window start survive any spine whose atoms fire at or beyond it
(`SpineFiresAtOrBeyond` + `processSpine_openWiresPrefix_invariant`), in value AND in range;
per-primitive lemmas cover the cup splice, the cap removal, and the generic box arm's iterated
drop-then-splice.  The spineDiff position lower bound is PROVED (`spineDiff_firesAtOrBeyond`: the
flattening only extends the left accumulator, so every atom of a block fires at or beyond the block's
window), giving the block-level corollary `runMatchingCell_openWiresPrefix_invariant`.  NOT yet proved
(the remaining geometric half of the block-swap witness): the SUFFIX correspondence — positions at or
beyond the window shift by the block's net width, with fresh ids related by `blockRotate`; see
`fxMode_hasMatchingComponentCoreSwapWitness`.  `= true`. -/
def fxMode_hasMatchingWindowPrefixLocality : Bool := true

end FX1Poly.Polygraph
