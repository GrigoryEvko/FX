import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix

/-! # mode-3 keystone — fresh-shift equivariance of the matching fold's wire view

The block-swap witness `sigma = blockRotate nf wA wB` must relate the open wires of the two transposed
Godement run orders: order-1 runs the upper-alpha block at counter `nf` and the beta block at `nf + wA`;
order-2 runs beta at `nf` and upper-alpha at `nf + wB`.  The SAME cell run from the SAME window contents at
a counter shifted by `delta` produces the SAME wire list up to `freshShiftAbove threshold delta` — old ids
(below the threshold) survive untouched, fresh ids come out exactly `delta` higher.  This file proves that
equivariance for the WIRE VIEW (`openWires` + `nextFresh`): per cup/cap atom, then for a whole block by the
same structural cell induction as `runMatchingCell_openWiresSuffix_invariant`.

Honest scope: conditioned on the cup/cap discipline (`AtomHasCupOrCapArity` / `CellHasCupCapGenerators` —
the whole walking-adjunction signature); the box arm's fresh block `(range n).map (· + nextFresh)` would
need the `listMapCongr` route and is not needed at the seed.  Only the wire view is covered — the `links` /
`loops` correspondence of the sigma witness is carried separately by the component machinery
(`componentComm` via the join kit, `loopsEq` via the exchange argument).

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The fresh shift -/

/-- Shift every identifier at or above `threshold` up by `delta`; fix every identifier below it.  The
renaming that relates a fold run at counter `threshold` to the same fold run at counter
`threshold + delta`. -/
def freshShiftAbove (threshold delta identifier : Nat) : Nat :=
  if threshold ≤ identifier then identifier + delta else identifier

/-- `freshShiftAbove` moves an at-or-above-threshold identifier up by exactly `delta`. -/
theorem freshShiftAbove_ofLe (threshold delta identifier : Nat)
    (isAtOrAboveThreshold : threshold ≤ identifier) :
    freshShiftAbove threshold delta identifier = identifier + delta :=
  if_pos isAtOrAboveThreshold

/-- `freshShiftAbove` fixes a below-threshold identifier. -/
theorem freshShiftAbove_ofNotLe (threshold delta identifier : Nat)
    (isBelowThreshold : ¬ threshold ≤ identifier) :
    freshShiftAbove threshold delta identifier = identifier :=
  if_neg isBelowThreshold

/-! ## The per-atom equivariance (cup/cap arity discipline) -/

/-- ★ **One cup/cap atom is equivariant under the fresh shift.**  If the shifted state's wires are the
shift-image of the base state's wires and its counter runs exactly `delta` ahead (with the shift threshold
at or below the base counter), the same holds after the atom: a cup splices `[nfT, nfT+1] =
[shift nfS, shift (nfS+1)]` (the splice commutes with the map, the two fresh legs are at-or-above the
threshold), a cap removes the same window pair on both sides (the removal commutes with the map, the
counter is untouched). -/
theorem stepAtom_wireView_freshShift {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (threshold delta : Nat) (stateS stateT : WireState)
    (atom : SpineAtom signature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom)
    (wiresMap : stateT.openWires = stateS.openWires.map (freshShiftAbove threshold delta))
    (freshShifted : stateT.nextFresh = stateS.nextFresh + delta)
    (thresholdLe : threshold ≤ stateS.nextFresh) :
    (stepAtom stateT atom).openWires
        = (stepAtom stateS atom).openWires.map (freshShiftAbove threshold delta)
      ∧ (stepAtom stateT atom).nextFresh = (stepAtom stateS atom).nextFresh + delta := by
  cases arity with
  | inl cupArity =>
      rw [stepAtom_ofCupArity stateT atom cupArity.1 cupArity.2,
        stepAtom_ofCupArity stateS atom cupArity.1 cupArity.2]
      constructor
      · rw [stepCup_openWires, stepCup_openWires,
          natListInsertAt_map (freshShiftAbove threshold delta) stateS.openWires
            atom.leftContext.length [stateS.nextFresh, stateS.nextFresh + 1],
          wiresMap, freshShifted]
        show natListInsertAt (stateS.openWires.map (freshShiftAbove threshold delta))
              atom.leftContext.length
              [stateS.nextFresh + delta, stateS.nextFresh + delta + 1]
            = natListInsertAt (stateS.openWires.map (freshShiftAbove threshold delta))
              atom.leftContext.length
              [freshShiftAbove threshold delta stateS.nextFresh,
                freshShiftAbove threshold delta (stateS.nextFresh + 1)]
        rw [freshShiftAbove_ofLe threshold delta stateS.nextFresh thresholdLe,
          freshShiftAbove_ofLe threshold delta (stateS.nextFresh + 1)
            (Nat.le_succ_of_le thresholdLe),
          Nat.add_right_comm stateS.nextFresh 1 delta]
      · rw [stepCup_nextFresh, stepCup_nextFresh, freshShifted,
          Nat.add_right_comm stateS.nextFresh delta 2]
  | inr capArity =>
      rw [stepAtom_ofCapArity stateT atom capArity.1 capArity.2,
        stepAtom_ofCapArity stateS atom capArity.1 capArity.2]
      constructor
      · rw [stepCap_openWires, stepCap_openWires, wiresMap,
          natListRemoveTwoAt_map (freshShiftAbove threshold delta) stateS.openWires
            atom.leftContext.length]
      · rw [stepCap_nextFresh, stepCap_nextFresh, freshShifted]

/-! ## The block layer: equivariance of a whole cell's fold -/

/-- ★ **A whole block's fold is equivariant under the fresh shift.**  Under the cup/cap generator
discipline, running the SAME cell from a shift-related state pair yields a shift-related pair: structural
cell induction mirroring `runMatchingCell_openWiresSuffix_invariant` — a generator is the atom lemma, an
identity is untouched, a vertical composite chains the two factor equivariances through
`runMatchingCell_vcomp` (the threshold bound transported along `runMatchingCell_nextFresh_le`), and the two
whiskerings only re-anchor the accumulators. -/
theorem runMatchingCell_wireView_freshShift {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} (threshold delta : Nat) :
    {localSource localTarget : signature.graph.Mode} →
    (leftAcc : ModalityPath signature.graph overallSource localSource) →
    (rightAcc : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (stateS stateT : WireState) →
    CellHasCupCapGenerators cell →
    stateT.openWires = stateS.openWires.map (freshShiftAbove threshold delta) →
    stateT.nextFresh = stateS.nextFresh + delta →
    threshold ≤ stateS.nextFresh →
    (runMatchingCell stateT leftAcc rightAcc cell).openWires
        = (runMatchingCell stateS leftAcc rightAcc cell).openWires.map
            (freshShiftAbove threshold delta)
      ∧ (runMatchingCell stateT leftAcc rightAcc cell).nextFresh
          = (runMatchingCell stateS leftAcc rightAcc cell).nextFresh + delta
  | _, _, leftAcc, rightAcc, _, _, .gen generator, stateS, stateT, cupCap, wiresMap,
      freshShifted, thresholdLe =>
      stepAtom_wireView_freshShift threshold delta stateS stateT
        ⟨_, _, leftAcc, _, _, generator, rightAcc⟩ cupCap wiresMap freshShifted thresholdLe
  | _, _, _, _, _, _, .id _, _, _, _, wiresMap, freshShifted, _ =>
      ⟨wiresMap, freshShifted⟩
  | _, _, leftAcc, rightAcc, _, _, .vcomp cellAlpha cellBeta, stateS, stateT, cupCap,
      wiresMap, freshShifted, thresholdLe => by
      have alphaShift := runMatchingCell_wireView_freshShift threshold delta leftAcc rightAcc
        cellAlpha stateS stateT cupCap.1 wiresMap freshShifted thresholdLe
      have betaShift := runMatchingCell_wireView_freshShift threshold delta leftAcc rightAcc
        cellBeta (runMatchingCell stateS leftAcc rightAcc cellAlpha)
        (runMatchingCell stateT leftAcc rightAcc cellAlpha) cupCap.2 alphaShift.1 alphaShift.2
        (Nat.le_trans thresholdLe
          (runMatchingCell_nextFresh_le stateS leftAcc rightAcc cellAlpha))
      rw [runMatchingCell_vcomp stateT leftAcc rightAcc cellAlpha cellBeta,
        runMatchingCell_vcomp stateS leftAcc rightAcc cellAlpha cellBeta]
      exact betaShift
  | _, _, leftAcc, rightAcc, _, _, .whiskerLeft oneCell body, stateS, stateT, cupCap,
      wiresMap, freshShifted, thresholdLe =>
      runMatchingCell_wireView_freshShift threshold delta (composePath leftAcc oneCell)
        rightAcc body stateS stateT cupCap wiresMap freshShifted thresholdLe
  | _, _, leftAcc, rightAcc, _, _, .whiskerRight oneCell body, stateS, stateT, cupCap,
      wiresMap, freshShifted, thresholdLe =>
      runMatchingCell_wireView_freshShift threshold delta leftAcc
        (composePath oneCell rightAcc) body stateS stateT cupCap wiresMap freshShifted
        thresholdLe

/-! ## The pointwise read kit (sigma-assembly substrate)

The witness's `openMap` is a LIST-map equality, while the window invariants are pointwise reads.  The
bridge: prove the map equality index-by-index (zones: below / inside / past the window) and assemble via
`natListEqOfPointwiseGetAt`.  The in-range getAt/map commutation drops `natListGetAt_map`'s
`sigma 0 = 0` sentinel condition — the key to the empty-boundary degeneracy, where the rotation MUST
move `0`. -/

/-- Reading a mapped list in range commutes with the map — NO fixed-sentinel condition (contrast the
banked `natListGetAt_map`, whose out-of-range arm needs `sigma 0 = 0`). -/
theorem natListGetAt_map_inRange (mapped : Nat → Nat) :
    (wires : List Nat) → (index : Nat) → index < wires.length →
    natListGetAt (wires.map mapped) index = mapped (natListGetAt wires index)
  | [], _, indexInRange => absurd indexInRange (Nat.not_succ_le_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: rest, index + 1, indexInRange =>
      natListGetAt_map_inRange mapped rest index (Nat.le_of_succ_le_succ indexInRange)

/-- Two lists of equal length with equal reads at every in-range index are EQUAL — the pointwise-to-list
bridge (structural double recursion on an `Eq` of `List Nat`; no function extensionality anywhere). -/
theorem natListEqOfPointwiseGetAt :
    (first : List Nat) → (second : List Nat) → first.length = second.length →
    (∀ index, index < first.length → natListGetAt first index = natListGetAt second index) →
    first = second
  | [], [], _, _ => rfl
  | [], _ :: _, lengthsEq, _ => Nat.noConfusion lengthsEq
  | _ :: _, [], lengthsEq, _ => Nat.noConfusion lengthsEq
  | firstHead :: firstRest, secondHead :: secondRest, lengthsEq, pointwiseEq => by
      rw [show firstHead = secondHead from
          pointwiseEq 0 (Nat.succ_le_succ (Nat.zero_le firstRest.length)),
        natListEqOfPointwiseGetAt firstRest secondRest (Nat.succ.inj lengthsEq)
          (fun index indexInRange => pointwiseEq (index + 1) (Nat.succ_le_succ indexInRange))]

/-- A renaming that fixes every id below a threshold fixes a whole list of below-threshold ids — the
mirror of the banked `mapFixedAbove` (prefix/suffix zones hold only pre-swap ids, which both
`freshShiftAbove threshold delta` and `blockRotate threshold w1 w2` fix). -/
theorem mapFixedBelow (sigma : Nat → Nat) (threshold : Nat)
    (fixesBelow : ∀ identifier, identifier < threshold → sigma identifier = identifier) :
    (wires : List Nat) → (∀ wire ∈ wires, wire < threshold) → wires.map sigma = wires
  | [], _ => rfl
  | head :: tail, allBelowThreshold => by
      show sigma head :: tail.map sigma = head :: tail
      rw [fixesBelow head (allBelowThreshold head (List.Mem.head _)),
        mapFixedBelow sigma threshold fixesBelow tail
          (fun wire wireInTail => allBelowThreshold wire (List.Mem.tail _ wireInTail))]

/-- Reading an appended list inside the prefix block reads the block (the mirror of the banked
`natListGetAt_append_pastBlock`). -/
theorem natListGetAt_append_inside :
    (block : List Nat) → (wires : List Nat) → (offset : Nat) → offset < block.length →
    natListGetAt (block ++ wires) offset = natListGetAt block offset
  | [], _, _, offsetInRange => absurd offsetInRange (Nat.not_succ_le_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: blockRest, wires, offset + 1, offsetInRange =>
      natListGetAt_append_inside blockRest wires offset (Nat.le_of_succ_le_succ offsetInRange)

/-- ★ Reading a spliced list INSIDE the spliced window reads the block itself — the third window zone,
completing the trio (below = `natListGetAt_natListInsertAt_below`, past = `…_pastBlock`, inside =
this).  Position-0 arms split by list shape (the splice matcher cases the list first). -/
theorem natListGetAt_natListInsertAt_inside :
    (wires : List Nat) → (position : Nat) → (block : List Nat) → (innerOffset : Nat) →
    innerOffset < block.length → position ≤ wires.length →
    natListGetAt (natListInsertAt wires position block) (position + innerOffset)
      = natListGetAt block innerOffset
  | [], 0, block, innerOffset, offsetInRange, _ => by
      rw [Nat.zero_add]
      exact natListGetAt_append_inside block [] innerOffset offsetInRange
  | head :: rest, 0, block, innerOffset, offsetInRange, _ => by
      rw [Nat.zero_add]
      exact natListGetAt_append_inside block (head :: rest) innerOffset offsetInRange
  | [], _ + 1, _, _, _, positionInRange => absurd positionInRange (Nat.not_succ_le_zero _)
  | head :: rest, position + 1, block, innerOffset, offsetInRange, positionInRange => by
      show natListGetAt (head :: natListInsertAt rest position block)
            (position + 1 + innerOffset)
          = natListGetAt block innerOffset
      rw [Nat.add_right_comm position 1 innerOffset]
      exact natListGetAt_natListInsertAt_inside rest position block innerOffset offsetInRange
        (Nat.le_of_succ_le_succ positionInRange)

/-! ## Nat monotonicity/cancellation helpers (hand-rolled; core `Nat.add_right_cancel` leaks propext) -/

private theorem natAddLeMonoRight : (added : Nat) → {leftSide rightSide : Nat} →
    leftSide ≤ rightSide → leftSide + added ≤ rightSide + added
  | 0, _, _, sidesLe => sidesLe
  | added + 1, _, _, sidesLe => Nat.succ_le_succ (natAddLeMonoRight added sidesLe)

private theorem natAddLeCancelRight : (cancelled : Nat) → {leftSum rightSum : Nat} →
    leftSum + cancelled ≤ rightSum + cancelled → leftSum ≤ rightSum
  | 0, _, _, sumsLe => sumsLe
  | cancelled + 1, _, _, sumsLe => natAddLeCancelRight cancelled (Nat.le_of_succ_le_succ sumsLe)

private theorem natAddLeMonoLeft (added : Nat) {leftSide rightSide : Nat}
    (sidesLe : leftSide ≤ rightSide) : added + leftSide ≤ added + rightSide := by
  rw [Nat.add_comm added leftSide, Nat.add_comm added rightSide]
  exact natAddLeMonoRight added sidesLe

private theorem natAddLtMonoLeft (added : Nat) {leftSide rightSide : Nat}
    (sidesLt : leftSide < rightSide) : added + leftSide < added + rightSide := by
  show added + leftSide + 1 ≤ added + rightSide
  rw [Nat.add_assoc added leftSide 1]
  exact natAddLeMonoLeft added sidesLt

private theorem natAddLtCancelLeft (cancelled : Nat) {leftSide rightSide : Nat}
    (sumsLt : cancelled + leftSide < cancelled + rightSide) : leftSide < rightSide := by
  show leftSide + 1 ≤ rightSide
  have shifted : cancelled + (leftSide + 1) ≤ cancelled + rightSide := by
    rw [← Nat.add_assoc cancelled leftSide 1]
    exact sumsLt
  have commuted : leftSide + 1 + cancelled ≤ rightSide + cancelled := by
    rw [Nat.add_comm (leftSide + 1) cancelled, Nat.add_comm rightSide cancelled]
    exact shifted
  exact natAddLeCancelRight cancelled commuted

/-! ## The window-localized fresh-shift congruence

The whole-list equivariance above needs the ENTIRE wire lists map-related — but in the transposed
block-swap orders the second block runs on a state whose OTHER-window contents already diverged (the first
block's fresh output).  What actually holds is the window-localized version: a cup/cap block's wire output
WINDOW depends only on its input WINDOW and its counter — everything outside the window (content, and even
length beyond the window) is invisible to the block, and the two right accumulators may differ outright
(the fold's wire bookkeeping never reads them).  Pointwise window reads related by `freshShiftAbove`
propagate through the block. -/

/-- ★ **One cup/cap atom's output window is fresh-shift-related from counter data alone.**  Two atoms with
the same firing position and the same generator arities (the block-swap instances share the generator and
the left context, differing only in the right context) step two counter-shifted states to
counter-shifted output windows: a cup's output window is exactly its two fresh legs (the input window is
empty), a cap's output window is empty.  The input WINDOW hypothesis is not even needed at the atom layer —
it enters at the block layer through the identity cell and the whisker pass-through zones. -/
theorem stepAtomPair_windowWireView_freshShift {signature : ModeSignature}
    {sourceModeS targetModeS sourceModeT targetModeT : signature.graph.Mode}
    (threshold delta : Nat) (stateS stateT : WireState)
    (atomS : SpineAtom signature sourceModeS targetModeS)
    (atomT : SpineAtom signature sourceModeT targetModeT)
    (positionEq : atomT.leftContext.length = atomS.leftContext.length)
    (domEq : atomT.generatorDom.length = atomS.generatorDom.length)
    (codEq : atomT.generatorCod.length = atomS.generatorCod.length)
    (arity : AtomHasCupOrCapArity atomS)
    (freshShifted : stateT.nextFresh = stateS.nextFresh + delta)
    (thresholdLe : threshold ≤ stateS.nextFresh)
    (windowInRangeS : atomS.leftContext.length + atomS.generatorDom.length
      ≤ stateS.openWires.length)
    (windowInRangeT : atomS.leftContext.length + atomS.generatorDom.length
      ≤ stateT.openWires.length) :
    (∀ innerOffset, innerOffset < atomS.generatorCod.length →
      natListGetAt (stepAtom stateT atomT).openWires (atomS.leftContext.length + innerOffset)
        = freshShiftAbove threshold delta
            (natListGetAt (stepAtom stateS atomS).openWires
              (atomS.leftContext.length + innerOffset)))
    ∧ (stepAtom stateT atomT).nextFresh = (stepAtom stateS atomS).nextFresh + delta := by
  cases arity with
  | inl cupArity =>
      rw [cupArity.1] at windowInRangeS windowInRangeT
      rw [stepAtom_ofCupArity stateT atomT (domEq.trans cupArity.1) (codEq.trans cupArity.2),
        stepAtom_ofCupArity stateS atomS cupArity.1 cupArity.2, positionEq]
      constructor
      · intro innerOffset offsetInRange
        rw [cupArity.2] at offsetInRange
        rw [stepCup_openWires, stepCup_openWires,
          natListGetAt_natListInsertAt_inside stateT.openWires atomS.leftContext.length
            [stateT.nextFresh, stateT.nextFresh + 1] innerOffset offsetInRange windowInRangeT,
          natListGetAt_natListInsertAt_inside stateS.openWires atomS.leftContext.length
            [stateS.nextFresh, stateS.nextFresh + 1] innerOffset offsetInRange windowInRangeS]
        cases innerOffset with
        | zero =>
            show stateT.nextFresh = freshShiftAbove threshold delta stateS.nextFresh
            rw [freshShiftAbove_ofLe threshold delta stateS.nextFresh thresholdLe, freshShifted]
        | succ offsetPred =>
            cases offsetPred with
            | zero =>
                show stateT.nextFresh + 1
                    = freshShiftAbove threshold delta (stateS.nextFresh + 1)
                rw [freshShiftAbove_ofLe threshold delta (stateS.nextFresh + 1)
                    (Nat.le_succ_of_le thresholdLe),
                  freshShifted, Nat.add_right_comm stateS.nextFresh 1 delta]
            | succ offsetRest =>
                exact absurd
                  (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ offsetInRange))
                  (Nat.not_lt_zero offsetRest)
      · rw [stepCup_nextFresh, stepCup_nextFresh, freshShifted,
          Nat.add_right_comm stateS.nextFresh delta 2]
  | inr capArity =>
      rw [stepAtom_ofCapArity stateT atomT (domEq.trans capArity.1) (codEq.trans capArity.2),
        stepAtom_ofCapArity stateS atomS capArity.1 capArity.2, positionEq]
      constructor
      · intro innerOffset offsetInRange
        rw [capArity.2] at offsetInRange
        exact absurd offsetInRange (Nat.not_lt_zero innerOffset)
      · rw [stepCap_nextFresh, stepCap_nextFresh, freshShifted]

/-- ★ **A whole block's fold reads only its window and its counter (fresh-shift form).**  Under the cup/cap
generator discipline, two runs of the SAME cell at the SAME left accumulator — but from states whose
WINDOW reads are `freshShiftAbove`-related and whose counters run `delta` apart, with ARBITRARY (even
different) right accumulators and arbitrary out-of-window content — produce fresh-shift-related output
windows and counters.  This is the missing localization the block-swap `openMap` assembly needs: the
whole-list equivariance cannot relate the transposed orders directly (the other block's window already
diverged), but each block's window evolution is local.  Structural cell induction: a generator is the
atom-pair lemma, an identity passes the window hypothesis through, a vertical composite chains the factor
congruences through `runMatchingCell_vcomp` (middle window ranges from the banked suffix count equation),
`whiskerLeft` splits the window into the passed-through prefix zone (both runs leave it untouched — the
prefix invariant) and the re-anchored body window, and `whiskerRight` splits into the body window and the
passed-through suffix zone (both runs shift it by the body's boundary delta — the suffix invariant). -/
theorem runMatchingCell_windowWireView_freshShift {signature : ModeSignature}
    {overallSource overallTargetS overallTargetT : signature.graph.Mode}
    (threshold delta : Nat) :
    {localSource localTarget : signature.graph.Mode} →
    (leftAcc : ModalityPath signature.graph overallSource localSource) →
    (rightAccS : ModalityPath signature.graph localTarget overallTargetS) →
    (rightAccT : ModalityPath signature.graph localTarget overallTargetT) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (stateS stateT : WireState) →
    CellHasCupCapGenerators cell →
    (∀ innerOffset, innerOffset < localDom.length →
      natListGetAt stateT.openWires (leftAcc.length + innerOffset)
        = freshShiftAbove threshold delta
            (natListGetAt stateS.openWires (leftAcc.length + innerOffset))) →
    stateT.nextFresh = stateS.nextFresh + delta →
    threshold ≤ stateS.nextFresh →
    leftAcc.length + localDom.length ≤ stateS.openWires.length →
    leftAcc.length + localDom.length ≤ stateT.openWires.length →
    (∀ innerOffset, innerOffset < localCod.length →
      natListGetAt (runMatchingCell stateT leftAcc rightAccT cell).openWires
          (leftAcc.length + innerOffset)
        = freshShiftAbove threshold delta
            (natListGetAt (runMatchingCell stateS leftAcc rightAccS cell).openWires
              (leftAcc.length + innerOffset)))
    ∧ (runMatchingCell stateT leftAcc rightAccT cell).nextFresh
        = (runMatchingCell stateS leftAcc rightAccS cell).nextFresh + delta
  | _, _, leftAcc, rightAccS, rightAccT, _, _, .gen generator, stateS, stateT, cupCap,
      _windowMap, freshShifted, thresholdLe, windowInRangeS, windowInRangeT =>
      stepAtomPair_windowWireView_freshShift threshold delta stateS stateT
        ⟨_, _, leftAcc, _, _, generator, rightAccS⟩
        ⟨_, _, leftAcc, _, _, generator, rightAccT⟩
        rfl rfl rfl cupCap freshShifted thresholdLe windowInRangeS windowInRangeT
  | _, _, _, _, _, _, _, .id _, _, _, _, windowMap, freshShifted, _, _, _ =>
      ⟨windowMap, freshShifted⟩
  | _, _, leftAcc, rightAccS, rightAccT, _, _,
      @RawTwoCellExpr.vcomp _ _ _ oneCellF oneCellG oneCellH cellAlpha cellBeta,
      stateS, stateT, cupCap, windowMap, freshShifted, thresholdLe,
      windowInRangeS, windowInRangeT => by
      have alphaCongruence := runMatchingCell_windowWireView_freshShift threshold delta leftAcc
        rightAccS rightAccT cellAlpha stateS stateT cupCap.1 windowMap freshShifted thresholdLe
        windowInRangeS windowInRangeT
      have alphaCountS := (runMatchingCell_openWiresSuffix_invariant leftAcc rightAccS cellAlpha
        stateS cupCap.1 windowInRangeS).2
      have alphaCountT := (runMatchingCell_openWiresSuffix_invariant leftAcc rightAccT cellAlpha
        stateT cupCap.1 windowInRangeT).2
      have middleRangeS : leftAcc.length + oneCellG.length
          ≤ (runMatchingCell stateS leftAcc rightAccS cellAlpha).openWires.length := by
        have padded : leftAcc.length + oneCellG.length + oneCellF.length
            ≤ (runMatchingCell stateS leftAcc rightAccS cellAlpha).openWires.length
              + oneCellF.length := by
          rw [Nat.add_right_comm leftAcc.length oneCellG.length oneCellF.length, alphaCountS]
          exact natAddLeMonoRight oneCellG.length windowInRangeS
        exact natAddLeCancelRight oneCellF.length padded
      have middleRangeT : leftAcc.length + oneCellG.length
          ≤ (runMatchingCell stateT leftAcc rightAccT cellAlpha).openWires.length := by
        have padded : leftAcc.length + oneCellG.length + oneCellF.length
            ≤ (runMatchingCell stateT leftAcc rightAccT cellAlpha).openWires.length
              + oneCellF.length := by
          rw [Nat.add_right_comm leftAcc.length oneCellG.length oneCellF.length, alphaCountT]
          exact natAddLeMonoRight oneCellG.length windowInRangeT
        exact natAddLeCancelRight oneCellF.length padded
      have betaCongruence := runMatchingCell_windowWireView_freshShift threshold delta leftAcc
        rightAccS rightAccT cellBeta (runMatchingCell stateS leftAcc rightAccS cellAlpha)
        (runMatchingCell stateT leftAcc rightAccT cellAlpha) cupCap.2 alphaCongruence.1
        alphaCongruence.2
        (Nat.le_trans thresholdLe
          (runMatchingCell_nextFresh_le stateS leftAcc rightAccS cellAlpha))
        middleRangeS middleRangeT
      rw [runMatchingCell_vcomp stateT leftAcc rightAccT cellAlpha cellBeta,
        runMatchingCell_vcomp stateS leftAcc rightAccS cellAlpha cellBeta]
      exact betaCongruence
  | _, _, leftAcc, rightAccS, rightAccT, _, _,
      @RawTwoCellExpr.whiskerLeft _ _ _ _ oneCell oneCellG oneCellH body,
      stateS, stateT, cupCap, windowMap, freshShifted, thresholdLe,
      windowInRangeS, windowInRangeT => by
      rw [composePath_length oneCell oneCellG] at windowInRangeS windowInRangeT
      have bodyWindowMap : ∀ innerOffset, innerOffset < oneCellG.length →
          natListGetAt stateT.openWires ((composePath leftAcc oneCell).length + innerOffset)
            = freshShiftAbove threshold delta
                (natListGetAt stateS.openWires
                  ((composePath leftAcc oneCell).length + innerOffset)) := by
        intro innerOffset offsetInRange
        have outerRead := windowMap (oneCell.length + innerOffset) (by
          rw [composePath_length oneCell oneCellG]
          exact natAddLtMonoLeft oneCell.length offsetInRange)
        rw [← Nat.add_assoc leftAcc.length oneCell.length innerOffset,
          ← composePath_length leftAcc oneCell] at outerRead
        exact outerRead
      have bodyRangeS : (composePath leftAcc oneCell).length + oneCellG.length
          ≤ stateS.openWires.length := by
        rw [composePath_length leftAcc oneCell,
          Nat.add_assoc leftAcc.length oneCell.length oneCellG.length]
        exact windowInRangeS
      have bodyRangeT : (composePath leftAcc oneCell).length + oneCellG.length
          ≤ stateT.openWires.length := by
        rw [composePath_length leftAcc oneCell,
          Nat.add_assoc leftAcc.length oneCell.length oneCellG.length]
        exact windowInRangeT
      have bodyCongruence := runMatchingCell_windowWireView_freshShift threshold delta
        (composePath leftAcc oneCell) rightAccS rightAccT body stateS stateT cupCap
        bodyWindowMap freshShifted thresholdLe bodyRangeS bodyRangeT
      constructor
      · intro innerOffset offsetInRange
        rw [composePath_length oneCell oneCellH] at offsetInRange
        show natListGetAt (runMatchingCell stateT (composePath leftAcc oneCell) rightAccT
              body).openWires (leftAcc.length + innerOffset)
            = freshShiftAbove threshold delta
                (natListGetAt (runMatchingCell stateS (composePath leftAcc oneCell) rightAccS
                  body).openWires (leftAcc.length + innerOffset))
        cases Nat.lt_or_ge innerOffset oneCell.length with
        | inl belowWhisker =>
            have belowWindow : leftAcc.length + innerOffset
                < (composePath leftAcc oneCell).length := by
              rw [composePath_length leftAcc oneCell]
              exact natAddLtMonoLeft leftAcc.length belowWhisker
            have belowDomWidth : innerOffset < oneCell.length + oneCellG.length :=
              Nat.lt_of_lt_of_le belowWhisker (Nat.le_add_right oneCell.length oneCellG.length)
            have prefixT := runMatchingCell_openWiresPrefix_invariant stateT
              (composePath leftAcc oneCell) rightAccT body (leftAcc.length + innerOffset)
              belowWindow
              (Nat.lt_of_lt_of_le (natAddLtMonoLeft leftAcc.length belowDomWidth)
                windowInRangeT)
            have prefixS := runMatchingCell_openWiresPrefix_invariant stateS
              (composePath leftAcc oneCell) rightAccS body (leftAcc.length + innerOffset)
              belowWindow
              (Nat.lt_of_lt_of_le (natAddLtMonoLeft leftAcc.length belowDomWidth)
                windowInRangeS)
            rw [prefixT.1, prefixS.1]
            exact windowMap innerOffset (by
              rw [composePath_length oneCell oneCellG]
              exact belowDomWidth)
        | inr atOrPastWhisker =>
            obtain ⟨bodyOffset, bodyOffsetEq⟩ := Nat.le.dest atOrPastWhisker
            have bodyOffsetLt : bodyOffset < oneCellH.length := by
              rw [← bodyOffsetEq] at offsetInRange
              exact natAddLtCancelLeft oneCell.length offsetInRange
            have bodyRead := bodyCongruence.1 bodyOffset bodyOffsetLt
            rw [composePath_length leftAcc oneCell,
              Nat.add_assoc leftAcc.length oneCell.length bodyOffset, bodyOffsetEq] at bodyRead
            exact bodyRead
      · exact bodyCongruence.2
  | _, _, leftAcc, rightAccS, rightAccT, _, _,
      @RawTwoCellExpr.whiskerRight _ _ _ _ oneCellF oneCellG oneCell body,
      stateS, stateT, cupCap, windowMap, freshShifted, thresholdLe,
      windowInRangeS, windowInRangeT => by
      rw [composePath_length oneCellF oneCell] at windowInRangeS windowInRangeT
      have bodyRangeS : leftAcc.length + oneCellF.length ≤ stateS.openWires.length := by
        rw [← Nat.add_assoc leftAcc.length oneCellF.length oneCell.length] at windowInRangeS
        exact Nat.le_trans
          (Nat.le_add_right (leftAcc.length + oneCellF.length) oneCell.length) windowInRangeS
      have bodyRangeT : leftAcc.length + oneCellF.length ≤ stateT.openWires.length := by
        rw [← Nat.add_assoc leftAcc.length oneCellF.length oneCell.length] at windowInRangeT
        exact Nat.le_trans
          (Nat.le_add_right (leftAcc.length + oneCellF.length) oneCell.length) windowInRangeT
      have bodyWindowMap : ∀ innerOffset, innerOffset < oneCellF.length →
          natListGetAt stateT.openWires (leftAcc.length + innerOffset)
            = freshShiftAbove threshold delta
                (natListGetAt stateS.openWires (leftAcc.length + innerOffset)) :=
        fun innerOffset offsetInRange =>
          windowMap innerOffset (by
            rw [composePath_length oneCellF oneCell]
            exact Nat.lt_of_lt_of_le offsetInRange
              (Nat.le_add_right oneCellF.length oneCell.length))
      have bodyCongruence := runMatchingCell_windowWireView_freshShift threshold delta leftAcc
        (composePath oneCell rightAccS) (composePath oneCell rightAccT) body stateS stateT
        cupCap bodyWindowMap freshShifted thresholdLe bodyRangeS bodyRangeT
      have suffixS := runMatchingCell_openWiresSuffix_invariant leftAcc
        (composePath oneCell rightAccS) body stateS cupCap bodyRangeS
      have suffixT := runMatchingCell_openWiresSuffix_invariant leftAcc
        (composePath oneCell rightAccT) body stateT cupCap bodyRangeT
      constructor
      · intro innerOffset offsetInRange
        rw [composePath_length oneCellG oneCell] at offsetInRange
        show natListGetAt (runMatchingCell stateT leftAcc (composePath oneCell rightAccT)
              body).openWires (leftAcc.length + innerOffset)
            = freshShiftAbove threshold delta
                (natListGetAt (runMatchingCell stateS leftAcc (composePath oneCell rightAccS)
                  body).openWires (leftAcc.length + innerOffset))
        cases Nat.lt_or_ge innerOffset oneCellG.length with
        | inl insideBodyCod => exact bodyCongruence.1 innerOffset insideBodyCod
        | inr atOrPastBodyCod =>
            obtain ⟨suffixOffset, suffixOffsetEq⟩ := Nat.le.dest atOrPastBodyCod
            have suffixOffsetLt : suffixOffset < oneCell.length := by
              rw [← suffixOffsetEq] at offsetInRange
              exact natAddLtCancelLeft oneCellG.length offsetInRange
            have readT := suffixT.1 suffixOffset
            have readS := suffixS.1 suffixOffset
            rw [Nat.add_assoc leftAcc.length suffixOffset oneCellG.length,
              Nat.add_comm suffixOffset oneCellG.length, suffixOffsetEq,
              Nat.add_assoc leftAcc.length suffixOffset oneCellF.length,
              Nat.add_comm suffixOffset oneCellF.length] at readT readS
            rw [readT, readS]
            exact windowMap (oneCellF.length + suffixOffset) (by
              rw [composePath_length oneCellF oneCell]
              exact natAddLtMonoLeft oneCellF.length suffixOffsetLt)
      · exact bodyCongruence.2

/-! ## Honesty marker -/

/-- **Honesty marker — the fresh-shift equivariance of the WIRE VIEW is PROVED.**  Under the cup/cap
discipline, the same cell run from a `freshShiftAbove`-related state pair (wires the shift-image, counter
`delta` ahead, threshold at or below the base counter) stays shift-related in `openWires` and `nextFresh`
(`stepAtom_wireView_freshShift`, `runMatchingCell_wireView_freshShift`).  This is the fresh-id half of the
`blockRotate` witness's `openMap`: the two transposed Godement run orders run the SAME two blocks at
counters offset by the OTHER block's fresh count, so their wire lists differ exactly by the per-block
shifts the rotation composes.  NOT covered here: the `links` / `loops` correspondence (the witness reads
those through `componentComm` / `loopsEq`, via the component-algebra kit), and the box arm (excluded by the
discipline; its fresh block would need the `listMapCongr` route).  `= true`. -/
def fxMode_hasMatchingFreshShiftEquivariance : Bool := true

/-- **Honesty marker — the WINDOW-LOCALIZED fresh-shift congruence is PROVED.**  Under the cup/cap
discipline, a block's wire-window evolution depends ONLY on its input window reads and its counter
(`stepAtomPair_windowWireView_freshShift`, `runMatchingCell_windowWireView_freshShift`): two runs of the
same cell at the same left accumulator — with arbitrary, even DIFFERENT right accumulators and arbitrary
out-of-window content — carry `freshShiftAbove`-related window reads and `delta`-shifted counters to
`freshShiftAbove`-related output windows.  This is the localization the block-swap `openMap` assembly
needs: the two transposed Godement orders run each block from states whose OTHER-window contents already
diverged, so the whole-list equivariance never applies — but per window, order-2's block run is exactly
order-1's at a counter shifted by the other block's fresh count.  NOT covered: the `links` / `loops`
correspondence (componentComm / loopsEq, via the component-algebra kit), and the zone-wise assembly of the
full `openWires` map equality itself (prefix via `mapFixedBelow` + the prefix invariants, windows via THIS
congruence, suffix via the suffix invariants — the next brick).  `= true`. -/
def fxMode_hasMatchingWindowFreshShiftCongruence : Bool := true

end FX1Poly.Polygraph
