import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPairSeatedDescent
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPairUntouched

/-! # WalkingString/StringConsecutiveUntouchedSeat — the FORWARD adjacency invariant of the toucher's
consecutive legs (FC-3 r25, B1)

The r24 exclusion `stringArcPairSeated_beforeCapStep_ofDistinctSeat` (`StringDistinctSeatCapExclusion`) descends a
seated pair BACKWARD through a cap, but it takes the pair's PRE-cap adjacency (`seatedBeforeInState`) as a
hypothesis.  Re-founding the descent master on that exclusion (r25, B2) therefore needs the pair adjacent at EVERY
front state along the prefix — established FORWARD, since a pure-cap prefix never inserts between the pair (only
cups do, and the located spine is pure-cap).  This file ships the forward substrate:

  * ★ `stringArcPairSeated_stepCapArc_ofDisjointReads` — **the forward adjacency-preservation step**.  A cap whose
    two consumed reads MISS both pair nodes never separates a seated pair: the removal window is positionally
    disjoint from the seat window (equal positions read equal values, so a missing read forces distinct
    positions), and two length-two windows of consecutive integers that are disjoint as SETS lie one strictly
    below the other — so the seat reads survive (below the window at the same seat, or past it two lower).  The
    ONE genuinely new position-arithmetic lemma; parity NEVER mentioned, colour-free, no distinctness needed.

  * ★ `stringMemProcessArcSpine_belowFresh_imp` — **the below-fresh membership monotonicity**.  A node below the
    START `nextFresh` that is open at the END of an arc fold was open at the START: cups only splice ids at or
    above `nextFresh` (a below-fresh node is never one of them) and caps/boxes only remove, so a below-fresh id,
    once dropped, never reappears.  This is the reverse read-off the r24 recon flagged as unpackaged (its Risk
    R1); it discharges the descent's touching-cap contradiction (a prefix cap that consumed a pair node would
    leave that node gone at the toucher, contradicting the located seat).

  * `stringConsecutiveUntouchedSeatProbe_fires` — the 3-cap maximally-shifting prefix truth-probe (seed
    `range 8`, pair `(2,3)`, caps at windows `0`, then `2`, then `2`), fired once through the forward step and
    checked end-to-end on the raw arithmetic.

Raw Lean 4 + Init; structural recursion only; the forward step is one `Nat`-trichotomy interval split closing on
the removal read-offs.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The forward adjacency-preservation step -/

/-- ★ **A disjoint cap keeps a seated pair seated, at a forward-shifted seat.**  When the cap's two consumed
reads MISS both pair nodes, the removal window `{windowPosition, windowPosition + 1}` is positionally disjoint
from the seat window `{seatPosition, seatPosition + 1}` (equal positions read equal values, so a missing read
forces distinct positions), and two length-two consecutive windows disjoint as sets lie one strictly below the
other.  So the seat survives: below the window at the SAME seat, or past it at the seat two lower — in either
case the pair is still seated adjacent.  The forward companion of the backward
`stringArcPairSeated_beforeCapStep_ofDistinctSeat`; NO distinctness needed (the position-disjointness is read
straight off the four misses), parity NEVER mentioned. -/
theorem stringArcPairSeated_stepCapArc_ofDisjointReads (state : ArcWireState)
    (windowPosition : Nat) {leftNode rightNode seatPosition : Nat}
    (seated : ArcPairSeated leftNode rightNode seatPosition state)
    (windowFits : windowPosition + 2 ≤ state.openWires.length)
    (firstReadMissesLeft : natListGetAt state.openWires windowPosition ≠ leftNode)
    (secondReadMissesLeft : natListGetAt state.openWires (windowPosition + 1) ≠ leftNode)
    (firstReadMissesRight : natListGetAt state.openWires windowPosition ≠ rightNode)
    (_secondReadMissesRight : natListGetAt state.openWires (windowPosition + 1) ≠ rightNode) :
    ∃ nextSeat, ArcPairSeated leftNode rightNode nextSeat (stepCapArc state windowPosition) := by
  obtain ⟨readLeft, readRight, seatFits⟩ := seated
  -- The four misses turn into three positional inequalities (equal positions would read equal values).
  have windowNeSeat : windowPosition ≠ seatPosition :=
    fun collides => firstReadMissesLeft (by rw [collides]; exact readLeft)
  have windowNeSeatSucc : windowPosition ≠ seatPosition + 1 :=
    fun collides => firstReadMissesRight (by rw [collides]; exact readRight)
  have windowSuccNeSeat : windowPosition + 1 ≠ seatPosition :=
    fun collides => secondReadMissesLeft (by rw [collides]; exact readLeft)
  have removedLength : (natListRemoveTwoAt state.openWires windowPosition).length + 2
      = state.openWires.length :=
    natListRemoveTwoAt_length state.openWires windowPosition windowFits
  have windowLeRemoved : windowPosition ≤ (natListRemoveTwoAt state.openWires windowPosition).length := by
    have shifted : windowPosition + 2 ≤ (natListRemoveTwoAt state.openWires windowPosition).length + 2 := by
      rw [removedLength]; exact windowFits
    exact Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ shifted)
  cases Nat.lt_or_ge windowPosition seatPosition with
  | inl windowLtSeat =>
      -- window strictly below the pair: both pair positions shift down by two.
      have windowPlusTwoLeSeat : windowPosition + 2 ≤ seatPosition :=
        Nat.lt_of_le_of_ne (Nat.succ_le_of_lt windowLtSeat) windowSuccNeSeat
      obtain ⟨gap, gapEq⟩ := Nat.le.dest windowPlusTwoLeSeat
      have seatEq : windowPosition + gap + 2 = seatPosition := by
        rw [Nat.add_right_comm windowPosition gap 2]; exact gapEq
      have seatSuccEq : windowPosition + (gap + 1) + 2 = seatPosition + 1 := by
        rw [Nat.add_right_comm windowPosition (gap + 1) 2, ← Nat.add_assoc (windowPosition + 2) gap 1,
          gapEq]
      have seatLeRemoved : seatPosition ≤ (natListRemoveTwoAt state.openWires windowPosition).length := by
        have shifted : seatPosition + 2 ≤ (natListRemoveTwoAt state.openWires windowPosition).length + 2 := by
          rw [removedLength]; exact seatFits
        exact Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ shifted)
      refine ⟨windowPosition + gap, ?_, ?_, ?_⟩
      · exact (natListGetAt_natListRemoveTwoAt_pastPair state.openWires windowPosition gap windowFits).trans
          (by rw [seatEq]; exact readLeft)
      · exact (natListGetAt_natListRemoveTwoAt_pastPair state.openWires windowPosition (gap + 1)
          windowFits).trans (by rw [seatSuccEq]; exact readRight)
      · show windowPosition + gap + 2 ≤ (natListRemoveTwoAt state.openWires windowPosition).length
        rw [seatEq]; exact seatLeRemoved
  | inr seatLeWindow =>
      -- window at-or-above the pair; the two disjoint windows force it strictly above.
      have seatLtWindow : seatPosition < windowPosition :=
        Nat.lt_of_le_of_ne seatLeWindow (fun collides => windowNeSeat collides.symm)
      have seatPlusTwoLeWindow : seatPosition + 2 ≤ windowPosition :=
        Nat.lt_of_le_of_ne (Nat.succ_le_of_lt seatLtWindow)
          (fun collides => windowNeSeatSucc collides.symm)
      have seatLtWindowStrict : seatPosition < windowPosition :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self seatPosition)
          (Nat.le_trans (Nat.le_succ (seatPosition + 1)) seatPlusTwoLeWindow)
      have seatSuccLtWindow : seatPosition + 1 < windowPosition :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self (seatPosition + 1)) seatPlusTwoLeWindow
      refine ⟨seatPosition, ?_, ?_, ?_⟩
      · exact (natListGetAt_natListRemoveTwoAt_below state.openWires windowPosition seatPosition
          seatLtWindowStrict).trans readLeft
      · exact (natListGetAt_natListRemoveTwoAt_below state.openWires windowPosition (seatPosition + 1)
          seatSuccLtWindow).trans readRight
      · show seatPosition + 2 ≤ (natListRemoveTwoAt state.openWires windowPosition).length
        exact Nat.le_trans seatPlusTwoLeWindow windowLeRemoved

/-! ## The below-fresh membership monotonicity (the r24 Risk-R1 reverse read-off) -/

/-- A below-fresh node open after ONE fold step was open before it: a cup splices only ids at or above
`nextFresh` (never a below-fresh id), a cap removes, and the box arm removes-then-splices-fresh — so a
below-fresh id in the step result is a below-fresh id in the source. -/
theorem stringMemStepArcAtom_belowFresh_imp {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode) {node : Nat}
    (nodeBelowFresh : node < state.nextFresh)
    (memAfter : node ∈ (stepArcAtom state atom).openWires) :
    node ∈ state.openWires := by
  unfold stepArcAtom at memAfter
  split at memAfter
  · -- cup: splice [nextFresh, nextFresh + 1]; a below-fresh node is neither leg.
    show node ∈ state.openWires
    cases mem_natListInsertAt_imp state.openWires atom.leftContext.length
        [state.nextFresh, state.nextFresh + 1] memAfter with
    | inl inWires => exact inWires
    | inr inBlock =>
        cases inBlock with
        | head => exact absurd nodeBelowFresh (Nat.lt_irrefl state.nextFresh)
        | tail _ inTail =>
            cases inTail with
            | head =>
                exact absurd (Nat.lt_trans nodeBelowFresh (Nat.lt_succ_self state.nextFresh))
                  (Nat.lt_irrefl (state.nextFresh + 1))
            | tail _ inNil => nomatch inNil
  · -- cap: remove two; membership only shrinks.
    exact mem_natListRemoveTwoAt_imp state.openWires _ memAfter
  · -- box: iterate remove then splice a fresh block; a below-fresh node is not in the fresh block.
    cases mem_natListInsertAt_imp _ atom.leftContext.length
        ((List.range atom.generatorCod.length).map (· + state.nextFresh)) memAfter with
    | inl inRemoved =>
        exact mem_iterRemoveTwoAt atom.leftContext.length state.openWires atom.generatorDom.length
          inRemoved
    | inr inFreshBlock =>
        obtain ⟨source, _sourceMem, sourceEq⟩ :=
          mem_map_imp (· + state.nextFresh) (List.range atom.generatorCod.length) inFreshBlock
        exact absurd (sourceEq ▸ nodeBelowFresh)
          (Nat.not_lt.mpr (Nat.le_add_left state.nextFresh source))

/-- ★ **A below-fresh node open at the END of an arc fold was open at the START.**  Structural recursion on the
spine: each step preserves below-freshness (`stepArcAtom_nextFresh_le`) and reflects membership one step
(`stringMemStepArcAtom_belowFresh_imp`).  The reverse read-off the r24 recon flagged as unpackaged (Risk R1):
once a below-fresh id is dropped by a cap it never returns (cups mint fresh ids only), so surviving to the end
witnesses survival at the start. -/
theorem stringMemProcessArcSpine_belowFresh_imp {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : ArcWireState) →
    {node : Nat} → node < state.nextFresh →
    node ∈ (processArcSpine state atoms).openWires → node ∈ state.openWires
  | [], _, _, _, memAfter => memAfter
  | atom :: rest, state, node, nodeBelowFresh, memAfter => by
      have memStepped : node ∈ (stepArcAtom state atom).openWires :=
        stringMemProcessArcSpine_belowFresh_imp rest (stepArcAtom state atom)
          (Nat.lt_of_lt_of_le nodeBelowFresh (stepArcAtom_nextFresh_le state atom)) memAfter
      exact stringMemStepArcAtom_belowFresh_imp state atom nodeBelowFresh memStepped

/-! ## Concrete truth-probe — the forward step on a maximally-shifting 3-cap prefix -/

/-- The 6-plus-2-wire seed `[0,1,2,3,4,5,6,7]` (fresh counter at `8`), the anchor for the maximally-shifting
prefix probe: the tracked pair `(2, 3)` sits adjacent at position `2`. -/
def stringConsecutiveUntouchedSeatProbeState : ArcWireState :=
  ArcWireState.mk (List.range 8) [] 8 0 [] []

/-- ★ **The forward step fires on a genuine disjoint cap, and the 3-cap prefix keeps the pair adjacent.**  The
forward step carries the pair `(2, 3)` seated at position `2` through a cap at window `0` (reads `0, 1`, disjoint
from the pair), yielding some forward seat in the stepped state; and the raw arithmetic of the whole
maximally-shifting 3-cap prefix — caps at windows `0`, then `2`, then `2`, each disjoint from the pair — is
checked end-to-end to leave the pair adjacent at position `0`.  A machine-checked non-vacuity witness for the
forward adjacency step. -/
theorem stringConsecutiveUntouchedSeatProbe_fires :
    (∃ nextSeat, ArcPairSeated 2 3 nextSeat
        (stepCapArc stringConsecutiveUntouchedSeatProbeState 0))
      ∧ ArcPairSeated 2 3 0
          (stepCapArc (stepCapArc (stepCapArc stringConsecutiveUntouchedSeatProbeState 0) 2) 2) := by
  refine ⟨?_, ?_⟩
  · exact stringArcPairSeated_stepCapArc_ofDisjointReads stringConsecutiveUntouchedSeatProbeState 0
      (seatPosition := 2) ⟨by decide, by decide, by decide⟩ (by decide) (by decide) (by decide)
      (by decide) (by decide)
  · exact ⟨by decide, by decide, by decide⟩

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the FORWARD adjacency invariant substrate is machine-checked (FC-3 r25, B1).**  Two new
pieces re-founding the descent on B2's colour-free exclusion:
`stringArcPairSeated_stepCapArc_ofDisjointReads` pushes a seated pair FORWARD through any cap that misses it (the
position-disjointness read straight off the four misses, no parity, no distinctness), and
`stringMemProcessArcSpine_belowFresh_imp` reflects a below-fresh open node from the fold's end back to its start
(the reverse read-off the recon flagged as Risk R1, the touching-cap-contradiction supplier for B2).
`stringConsecutiveUntouchedSeatProbe_fires` runs the forward step end-to-end on a maximally-shifting 3-cap
prefix.  NOT yet shipped this brick: the re-founded descent master (B2) and the pin-prime assembly (B3).
`= true`. -/
def fxString_hasConsecutiveUntouchedSeatForward : Bool := true

end FX1Poly.Polygraph
