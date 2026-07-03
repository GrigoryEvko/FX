import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentGodement

/-! # mode-3 keystone — the wire/partition SPLIT of the matching fold

The A2c block-swap witness (`sigma = blockRotate`) must compare TWO DIFFERENT atom orders — the redex runs
`cellAlphaUpper` then `cellBeta`, the reduct the transpose — so the step-simulation machinery (same atom, both
sides) does not apply; the comparison has to factor through what each projection of the fold ACTUALLY depends
on.  This file proves that factorization — the split of the matching fold into its wire-plumbing and partition
halves:

  ★ `stepAtom_wireView_congr` / `processSpine_wireView_congr` — the `openWires` / `nextFresh` outputs depend
    ONLY on the input `openWires` / `nextFresh`: `links` and `loops` are INVISIBLE to the wire plumbing.  So
    the open-wire evolution of both run orders can be computed symbolically, links-free — the substrate for
    the witness's `openMap` field and for defining the symbolic wire trace by dummy-state projection.
  ★ `stepAtom_partitionView_congr` / `processSpine_partitionView_congr` — the `links` output depends only on
    (`openWires`, `nextFresh`, `links`), and `loops` is a PURE ACCUMULATOR: it is never read, and its
    contribution obeys the swap law `outOne.loops + stateTwo.loops = outTwo.loops + stateOne.loops`.  So loop
    counts of the two run orders can be compared with arbitrary accumulator offsets — the substrate for the
    witness's `loopsEq` field (the exchange argument).
  ★ `stepAtom_ofCupArity` / `stepAtom_ofCapArity` — the arity characterizations reducing `stepAtom` to
    `stepCup` / `stepCap` under literal boundary lengths (the leaf-case workhorses).

Raw Lean 4 + Init; the congruences are literal-arity case trees (every leaf reduces both `stepAtom` matchers
definitionally), the spine level is structural recursion.  No `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Step-level projections and arity characterizations -/

/-- A cup splices the two fresh legs into the open wires. -/
theorem stepCup_openWires (state : WireState) (position : Nat) :
    (stepCup state position).openWires
      = natListInsertAt state.openWires position [state.nextFresh, state.nextFresh + 1] := rfl

/-- A cup allocates exactly two fresh ids. -/
theorem stepCup_nextFresh (state : WireState) (position : Nat) :
    (stepCup state position).nextFresh = state.nextFresh + 2 := rfl

/-- A cup joins exactly its two fresh legs. -/
theorem stepCup_links (state : WireState) (position : Nat) :
    (stepCup state position).links
      = unionFindJoin state.links state.nextFresh (state.nextFresh + 1) := rfl

/-- A cup never closes a loop. -/
theorem stepCup_loops (state : WireState) (position : Nat) :
    (stepCup state position).loops = state.loops := rfl

/-- A `0 ⇒ 2` generator steps as a CUP at its live position. -/
theorem stepAtom_ofCupArity {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : WireState) (atom : SpineAtom signature sourceMode targetMode)
    (hdom : atom.generatorDom.length = 0) (hcod : atom.generatorCod.length = 2) :
    stepAtom state atom = stepCup state atom.leftContext.length := by
  unfold stepAtom
  rw [hdom, hcod]

/-- A `2 ⇒ 0` generator steps as a CAP at its live position. -/
theorem stepAtom_ofCapArity {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : WireState) (atom : SpineAtom signature sourceMode targetMode)
    (hdom : atom.generatorDom.length = 2) (hcod : atom.generatorCod.length = 0) :
    stepAtom state atom = stepCap state atom.leftContext.length := by
  unfold stepAtom
  rw [hdom, hcod]

/-! ## The wire half: `openWires` / `nextFresh` never read `links` / `loops` -/

/-- ★ **The wire half of the split, per atom.**  `stepAtom`'s `openWires` and `nextFresh` outputs depend ONLY
on the input's `openWires` and `nextFresh` — the `links` and `loops` fields are invisible to the wire
plumbing (the cap's branch test reads `links`, but BOTH branches drop the same two wires).  Literal-arity
case tree; each leaf reduces both matchers definitionally. -/
theorem stepAtom_wireView_congr {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (stateOne stateTwo : WireState) (atom : SpineAtom signature sourceMode targetMode)
    (openEq : stateOne.openWires = stateTwo.openWires)
    (freshEq : stateOne.nextFresh = stateTwo.nextFresh) :
    (stepAtom stateOne atom).openWires = (stepAtom stateTwo atom).openWires
      ∧ (stepAtom stateOne atom).nextFresh = (stepAtom stateTwo atom).nextFresh := by
  cases hdom : atom.generatorDom.length with
  | zero =>
      cases hcod : atom.generatorCod.length with
      | zero =>
          exact ⟨by unfold stepAtom; rw [hdom, hcod, openEq, freshEq],
            by unfold stepAtom; rw [hdom, hcod, freshEq]⟩
      | succ codPred =>
          cases codPred with
          | zero =>
              exact ⟨by unfold stepAtom; rw [hdom, hcod, openEq, freshEq],
                by unfold stepAtom; rw [hdom, hcod, freshEq]⟩
          | succ codPredPred =>
              cases codPredPred with
              | zero =>
                  rw [stepAtom_ofCupArity stateOne atom hdom hcod,
                    stepAtom_ofCupArity stateTwo atom hdom hcod]
                  exact ⟨by rw [stepCup_openWires, stepCup_openWires, openEq, freshEq],
                    by rw [stepCup_nextFresh, stepCup_nextFresh, freshEq]⟩
              | succ _ =>
                  exact ⟨by unfold stepAtom; rw [hdom, hcod, openEq, freshEq]; rfl,
                    by unfold stepAtom; rw [hdom, hcod, freshEq]; rfl⟩
  | succ domPred =>
      cases domPred with
      | zero =>
          exact ⟨by unfold stepAtom; rw [hdom, openEq, freshEq],
            by unfold stepAtom; rw [hdom, freshEq]⟩
      | succ domPredPred =>
          cases domPredPred with
          | zero =>
              cases hcod : atom.generatorCod.length with
              | zero =>
                  rw [stepAtom_ofCapArity stateOne atom hdom hcod,
                    stepAtom_ofCapArity stateTwo atom hdom hcod]
                  exact ⟨by rw [stepCap_openWires, stepCap_openWires, openEq],
                    by rw [stepCap_nextFresh, stepCap_nextFresh, freshEq]⟩
              | succ _ =>
                  exact ⟨by unfold stepAtom; rw [hdom, hcod, openEq, freshEq]; rfl,
                    by unfold stepAtom; rw [hdom, hcod, freshEq]; rfl⟩
          | succ _ =>
              exact ⟨by unfold stepAtom; rw [hdom, openEq, freshEq]; rfl,
                by unfold stepAtom; rw [hdom, freshEq]; rfl⟩

/-- ★ **The wire half folds over a whole spine.** -/
theorem processSpine_wireView_congr {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (stateOne stateTwo : WireState) →
    stateOne.openWires = stateTwo.openWires → stateOne.nextFresh = stateTwo.nextFresh →
    (processSpine stateOne atoms).openWires = (processSpine stateTwo atoms).openWires
      ∧ (processSpine stateOne atoms).nextFresh = (processSpine stateTwo atoms).nextFresh
  | [], _, _, openEq, freshEq => ⟨openEq, freshEq⟩
  | atom :: rest, stateOne, stateTwo, openEq, freshEq => by
      show (processSpine (stepAtom stateOne atom) rest).openWires
            = (processSpine (stepAtom stateTwo atom) rest).openWires
          ∧ (processSpine (stepAtom stateOne atom) rest).nextFresh
            = (processSpine (stepAtom stateTwo atom) rest).nextFresh
      obtain ⟨stepOpen, stepFresh⟩ := stepAtom_wireView_congr stateOne stateTwo atom openEq freshEq
      exact processSpine_wireView_congr rest (stepAtom stateOne atom) (stepAtom stateTwo atom)
        stepOpen stepFresh

/-- ★ **The wire half survives running one cell.** -/
theorem runMatchingCell_wireView_congr {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (stateOne stateTwo : WireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod)
    (openEq : stateOne.openWires = stateTwo.openWires)
    (freshEq : stateOne.nextFresh = stateTwo.nextFresh) :
    (runMatchingCell stateOne leftAcc rightAcc cell).openWires
        = (runMatchingCell stateTwo leftAcc rightAcc cell).openWires
      ∧ (runMatchingCell stateOne leftAcc rightAcc cell).nextFresh
        = (runMatchingCell stateTwo leftAcc rightAcc cell).nextFresh :=
  processSpine_wireView_congr (cell.spineDiff leftAcc rightAcc []) stateOne stateTwo openEq freshEq

/-! ## The partition half: `links` never reads `loops`; `loops` is a pure accumulator -/

/-- Right-cancellation of `Nat` addition, structurally (`Nat.add_right_cancel`'s core proof leaks
`propext`; this recursion on the cancelled summand is axiom-free — `Nat.add` recurses on its second
argument, so each step is `Nat.succ.inj`). -/
private theorem natAddRightCancel : (middle leftSum rightSum : Nat) →
    leftSum + middle = rightSum + middle → leftSum = rightSum
  | 0, _, _, sumsEq => sumsEq
  | middle + 1, leftSum, rightSum, sumsEq =>
      natAddRightCancel middle leftSum rightSum (Nat.succ.inj sumsEq)

/-- Composing two loop-count swap laws through a shared middle pair — the transitivity of the
accumulator-swap relation, by cancelling the middle contributions. -/
private theorem loopsSwap_compose (outFirst outSecond stepFirst stepSecond accFirst accSecond : Nat)
    (outerSwap : outFirst + stepSecond = outSecond + stepFirst)
    (stepSwap : stepFirst + accSecond = stepSecond + accFirst) :
    outFirst + accSecond = outSecond + accFirst := by
  apply natAddRightCancel (stepFirst + stepSecond)
  calc outFirst + accSecond + (stepFirst + stepSecond)
      = outFirst + stepSecond + (stepFirst + accSecond) := by
        rw [Nat.add_assoc, Nat.add_assoc,
          Nat.add_left_comm accSecond stepFirst stepSecond,
          Nat.add_left_comm stepSecond stepFirst accSecond,
          Nat.add_comm accSecond stepSecond]
    _ = outSecond + stepFirst + (stepFirst + accSecond) := by rw [outerSwap]
    _ = outSecond + stepFirst + (stepSecond + accFirst) := by rw [stepSwap]
    _ = outSecond + accFirst + (stepFirst + stepSecond) := by
        rw [Nat.add_assoc, Nat.add_assoc,
          Nat.add_left_comm accFirst stepFirst stepSecond,
          Nat.add_comm stepSecond accFirst]

/-- ★ **The partition half of the split, per atom.**  With equal wire views AND equal links, the `links`
outputs agree, and the `loops` outputs obey the accumulator-SWAP law — `loops` is never READ by the fold
(the cap's increment test reads `links`, not `loops`), so the two accumulators just ride along. -/
theorem stepAtom_partitionView_congr {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (stateOne stateTwo : WireState) (atom : SpineAtom signature sourceMode targetMode)
    (openEq : stateOne.openWires = stateTwo.openWires)
    (freshEq : stateOne.nextFresh = stateTwo.nextFresh)
    (linksEq : stateOne.links = stateTwo.links) :
    (stepAtom stateOne atom).links = (stepAtom stateTwo atom).links
      ∧ (stepAtom stateOne atom).loops + stateTwo.loops
        = (stepAtom stateTwo atom).loops + stateOne.loops := by
  cases hdom : atom.generatorDom.length with
  | zero =>
      cases hcod : atom.generatorCod.length with
      | zero =>
          exact ⟨by unfold stepAtom; rw [hdom, hcod, linksEq],
            by unfold stepAtom; rw [hdom, hcod]; exact Nat.add_comm stateOne.loops stateTwo.loops⟩
      | succ codPred =>
          cases codPred with
          | zero =>
              exact ⟨by unfold stepAtom; rw [hdom, hcod, linksEq],
                by unfold stepAtom; rw [hdom, hcod]; exact Nat.add_comm stateOne.loops stateTwo.loops⟩
          | succ codPredPred =>
              cases codPredPred with
              | zero =>
                  rw [stepAtom_ofCupArity stateOne atom hdom hcod,
                    stepAtom_ofCupArity stateTwo atom hdom hcod]
                  exact ⟨by rw [stepCup_links, stepCup_links, linksEq, freshEq],
                    by rw [stepCup_loops, stepCup_loops]
                       exact Nat.add_comm stateOne.loops stateTwo.loops⟩
              | succ _ =>
                  exact ⟨by unfold stepAtom; rw [hdom, hcod, linksEq]; rfl,
                    by unfold stepAtom; rw [hdom, hcod]
                       exact Nat.add_comm stateOne.loops stateTwo.loops⟩
  | succ domPred =>
      cases domPred with
      | zero =>
          exact ⟨by unfold stepAtom; rw [hdom, linksEq],
            by unfold stepAtom; rw [hdom]; exact Nat.add_comm stateOne.loops stateTwo.loops⟩
      | succ domPredPred =>
          cases domPredPred with
          | zero =>
              cases hcod : atom.generatorCod.length with
              | zero =>
                  rw [stepAtom_ofCapArity stateOne atom hdom hcod,
                    stepAtom_ofCapArity stateTwo atom hdom hcod]
                  refine ⟨by rw [stepCap_links, stepCap_links, openEq, linksEq], ?_⟩
                  rw [stepCap_loops, stepCap_loops, openEq, linksEq]
                  split
                  · rw [Nat.add_right_comm stateOne.loops 1 stateTwo.loops,
                      Nat.add_right_comm stateTwo.loops 1 stateOne.loops,
                      Nat.add_comm stateOne.loops stateTwo.loops]
                  · exact Nat.add_comm stateOne.loops stateTwo.loops
              | succ _ =>
                  exact ⟨by unfold stepAtom; rw [hdom, hcod, linksEq]; rfl,
                    by unfold stepAtom; rw [hdom, hcod]
                       exact Nat.add_comm stateOne.loops stateTwo.loops⟩
          | succ _ =>
              exact ⟨by unfold stepAtom; rw [hdom, linksEq]; rfl,
                by unfold stepAtom; rw [hdom]; exact Nat.add_comm stateOne.loops stateTwo.loops⟩

/-- ★ **The partition half folds over a whole spine** — the wire half threads the wire equalities, the
accumulator-swap laws compose by `loopsSwap_compose`. -/
theorem processSpine_partitionView_congr {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (stateOne stateTwo : WireState) →
    stateOne.openWires = stateTwo.openWires → stateOne.nextFresh = stateTwo.nextFresh →
    stateOne.links = stateTwo.links →
    (processSpine stateOne atoms).links = (processSpine stateTwo atoms).links
      ∧ (processSpine stateOne atoms).loops + stateTwo.loops
        = (processSpine stateTwo atoms).loops + stateOne.loops
  | [], stateOne, stateTwo, _, _, linksEq => ⟨linksEq, Nat.add_comm stateOne.loops stateTwo.loops⟩
  | atom :: rest, stateOne, stateTwo, openEq, freshEq, linksEq => by
      show (processSpine (stepAtom stateOne atom) rest).links
            = (processSpine (stepAtom stateTwo atom) rest).links
          ∧ (processSpine (stepAtom stateOne atom) rest).loops + stateTwo.loops
            = (processSpine (stepAtom stateTwo atom) rest).loops + stateOne.loops
      obtain ⟨stepOpen, stepFresh⟩ := stepAtom_wireView_congr stateOne stateTwo atom openEq freshEq
      obtain ⟨stepLinks, stepLoops⟩ :=
        stepAtom_partitionView_congr stateOne stateTwo atom openEq freshEq linksEq
      obtain ⟨restLinks, restLoops⟩ := processSpine_partitionView_congr rest (stepAtom stateOne atom)
        (stepAtom stateTwo atom) stepOpen stepFresh stepLinks
      exact ⟨restLinks, loopsSwap_compose _ _ _ _ _ _ restLoops stepLoops⟩

/-- ★ **The partition half survives running one cell.** -/
theorem runMatchingCell_partitionView_congr {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (stateOne stateTwo : WireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod)
    (openEq : stateOne.openWires = stateTwo.openWires)
    (freshEq : stateOne.nextFresh = stateTwo.nextFresh)
    (linksEq : stateOne.links = stateTwo.links) :
    (runMatchingCell stateOne leftAcc rightAcc cell).links
        = (runMatchingCell stateTwo leftAcc rightAcc cell).links
      ∧ (runMatchingCell stateOne leftAcc rightAcc cell).loops + stateTwo.loops
        = (runMatchingCell stateTwo leftAcc rightAcc cell).loops + stateOne.loops :=
  processSpine_partitionView_congr (cell.spineDiff leftAcc rightAcc []) stateOne stateTwo openEq
    freshEq linksEq

/-! ## Honesty marker -/

/-- **Honesty marker — the wire/partition SPLIT of the matching fold is PROVED.**  The fold's `openWires` /
`nextFresh` projections are congruent in the wire view alone (`links` / `loops` invisible), the `links`
projection is congruent in (wires + links), and `loops` is a pure accumulator obeying the swap law — per
atom, per spine, per cell.  This is the factorization the block-swap witness comparison rides on: the two
Godement run orders can now be compared projection-by-projection with mismatched `links` / `loops` riding
along, and the symbolic wire / event trace (the next brick) is definable by dummy-state projection with
faithfulness BY these congruences.  What remains of the witness: the window-locality of the wire view under
disjoint blocks (`openMap`), the partition join-order independence (`componentComm`), and the loop-count
exchange (`loopsEq`) — see `fxMode_hasMatchingComponentCoreSwapWitness`.  `= true`. -/
def fxMode_hasMatchingFoldWirePartitionSplit : Bool := true

end FX1Poly.Polygraph
