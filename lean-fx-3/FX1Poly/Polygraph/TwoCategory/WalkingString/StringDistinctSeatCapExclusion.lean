import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPairSeatedDescent
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcWireDistinct

/-! # WalkingString/StringDistinctSeatCapExclusion — the COLOUR-FREE cap-step gap-closing exclusion
(FC-3 r24, B2)

The r23 descent master (`StringWordPairSeatedDescent`) refutes the cap step's gap-closing case
(a passed cap at the seat's successor fusing a distance-three pre-pair to adjacency) via
`stringArcPairSeated_beforeCapStep_ofSameParities`, which needs the passed cap's window colour to MATCH the
seat's — supplied by the threaded `prefixSharesWindowMode` premise.  B1
(`StringCapWindowColourTruthProbe`) truth-probed that colour read and it came back **FALSE**: an
`AllCapArity` prefix can carry a cap of the OPPOSITE window colour, so `prefixSharesWindowMode` is not
derivable and the colour route to inhabiting `StringCapHeadExtractionWordPin` is dead.

This file lands the HONEST unblocking route the recon under-analyzed: the gap-closing exclusion is
POSITIONAL, not colour.  The seat pair, in the located pure-cap regime, is the toucher's two legs — an
adjacent pair that is untouched through the prefix — and the arc fold's open-wire list is positionally
DISTINCT (`WireListDistinct`, shipped in `ArcWireDistinct`: distinct positions read distinct values).  So:
if the pair is ALSO seated adjacent in the PRE-cap state, a gap-closing cap is IMPOSSIBLE, because
gap-closing would read the pair at positions `seatAfter` and `seatAfter + 3` (distance three), while
pre-adjacency pins them at consecutive positions — and distinctness makes equal wire VALUES pin equal
POSITIONS, forcing `seatAfter + 1 = seatAfter + 3`, absurd.

  * ★ `natListGetAt_inj_ofWireListDistinct` — the position-uniqueness read-off: distinct positions read
    distinct values, so equal in-range reads pin equal positions (the injective converse of
    `WireListDistinct`).
  * ★★ `stringArcPairSeated_beforeCapStep_ofDistinctSeat` — the COLOUR-FREE gap-closing exclusion.  Given
    positional distinctness of the pre-cap open wires and the pair seated adjacent in the pre-cap state, a
    seated pair descends through EVERY cap of the spine — with parity NEVER mentioned.  This is the drop-in
    replacement for `stringArcPairSeated_beforeCapStep_ofSameParities` that the descent-master re-founding
    threads INSTEAD of `prefixSharesWindowMode`.

## The named residual (what the FULL pin inhabitation still needs)

This keystone takes the pair's PRE-cap adjacency (`seatedBeforeInState`) as a hypothesis.  Threading it
through the whole prefix — establishing forward that the toucher's consecutive untouched legs stay adjacent
as each pure-cap prefix atom fires (they never separate, because a cap only removes, never inserts) — plus
re-founding `stringWordPairSeated_bubblesThroughPrefix` on this exclusion in place of
`prefixSharesWindowMode`, and then assembling the four `StringCapHeadExtractionWordPin` conjuncts on top, is
the standing r24 residual (a descent-master re-founding, several lemmas).  What this file settles: the
exclusion itself is COLOUR-FREE and machine-checked, so the wall the r23 plan hit (and the recon called
"blocked") is genuinely REFUTABLE — the block was the colour framing, not the mathematics.

Raw Lean 4 + Init; the exclusion is `arcPairSeated_beforeCapStep` fed a positional refutation of gap-closing.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Position-uniqueness from positional distinctness -/

/-- ★ **Positional distinctness makes `natListGetAt` injective on the in-range indices.**  If two in-range
positions of a `WireListDistinct` list read the SAME value, the positions coincide: were they distinct one
way or the other, `WireListDistinct` would separate their reads.  The injective converse of the
distinctness predicate, threaded by `Nat` trichotomy. -/
theorem natListGetAt_inj_ofWireListDistinct {wires : List Nat}
    (distinct : WireListDistinct wires) {indexOne indexTwo : Nat}
    (oneBelowLength : indexOne < wires.length) (twoBelowLength : indexTwo < wires.length)
    (readsEqual : natListGetAt wires indexOne = natListGetAt wires indexTwo) :
    indexOne = indexTwo := by
  cases Nat.lt_or_ge indexOne indexTwo with
  | inl oneLtTwo => exact absurd readsEqual (distinct indexOne indexTwo oneLtTwo twoBelowLength)
  | inr twoLeOne =>
      cases Nat.lt_or_ge indexTwo indexOne with
      | inl twoLtOne =>
          exact absurd readsEqual.symm (distinct indexTwo indexOne twoLtOne oneBelowLength)
      | inr oneLeTwo => exact Nat.le_antisymm oneLeTwo twoLeOne

/-! ## The colour-free gap-closing exclusion -/

/-- ★★ **Backward descent through a cap at the adjoint triple, colour-free.**  The gap-closing exclusion is
supplied from POSITION, not parity: when the pre-cap open wires are positionally DISTINCT and the tracked
pair is ALSO seated adjacent in the pre-cap state, a cap at the seat's successor is impossible — it would
read the pair at positions three apart, contradicting the consecutive-position pre-seating (distinctness
pins equal wire values to equal positions).  So a seated pair descends through EVERY cap.  This
GENERALIZES the descent's `stringArcPairSeated_beforeCapStep_ofSameParities` off colour entirely: parity is
never mentioned, so `counitUpper` (`base`) and `counitLower` (`tip`) are handled identically, dissolving the
wall B1 showed the colour route cannot cross.  The positional core `arcPairSeated_beforeCapStep` is reused
verbatim (it is colour-blind). -/
theorem stringArcPairSeated_beforeCapStep_ofDistinctSeat (state : ArcWireState)
    (windowPosition : Nat) {leftNode rightNode seatAfter seatBefore : Nat}
    (distinct : WireListDistinct state.openWires)
    (seatedBeforeInState : ArcPairSeated leftNode rightNode seatBefore state)
    (windowFits : windowPosition + 2 ≤ state.openWires.length)
    (seatedAfter : ArcPairSeated leftNode rightNode seatAfter
      (stepCapArc state windowPosition)) :
    (ArcPairSeated leftNode rightNode seatAfter state ∧ seatAfter + 2 ≤ windowPosition)
      ∨ (ArcPairSeated leftNode rightNode (seatAfter + 2) state
          ∧ windowPosition ≤ seatAfter) := by
  refine arcPairSeated_beforeCapStep state windowPosition ?_ windowFits seatedAfter
  intro isGapClosing
  subst isGapClosing
  -- The post-cap reads unfold onto the pre-cap open-wire list.
  have leftFromState : natListGetAt state.openWires seatAfter = leftNode :=
    (natListGetAt_natListRemoveTwoAt_below state.openWires (seatAfter + 1) seatAfter
      (Nat.lt_succ_self seatAfter)).symm.trans seatedAfter.1
  have pastRead := natListGetAt_natListRemoveTwoAt_pastPair state.openWires (seatAfter + 1) 0 windowFits
  rw [Nat.add_zero, Nat.add_zero] at pastRead
  have rightFromState : natListGetAt state.openWires (seatAfter + 1 + 2) = rightNode :=
    pastRead.symm.trans seatedAfter.2.1
  -- Length bounds: the post-cap seat bound forces the distance-three read to be in range.
  have removedLength := natListRemoveTwoAt_length state.openWires (seatAfter + 1) windowFits
  have seatAfterPlusFourLeLength : seatAfter + 2 + 2 ≤ state.openWires.length :=
    Nat.le_trans (Nat.add_le_add_right seatedAfter.2.2 2) (Nat.le_of_eq removedLength)
  have distThreeBelowLength : seatAfter + 1 + 2 < state.openWires.length :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (seatAfter + 1 + 2)) seatAfterPlusFourLeLength
  have seatAfterBelowLength : seatAfter < state.openWires.length :=
    Nat.lt_of_lt_of_le
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self seatAfter)
        (Nat.le_add_right (seatAfter + 1) 2))
      (Nat.le_of_lt distThreeBelowLength)
  have seatBeforeBelowLength : seatBefore < state.openWires.length :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self seatBefore) (Nat.le_succ (seatBefore + 1)))
      seatedBeforeInState.2.2
  -- Distinctness pins the pre-seating to the gap-closing read, collapsing the distance.
  have seatEq : seatBefore = seatAfter :=
    natListGetAt_inj_ofWireListDistinct distinct seatBeforeBelowLength seatAfterBelowLength
      (seatedBeforeInState.1.trans leftFromState.symm)
  have rightAtSuccessor : natListGetAt state.openWires (seatAfter + 1) = rightNode := by
    rw [← seatEq]
    exact seatedBeforeInState.2.1
  have valuesCollide :
      natListGetAt state.openWires (seatAfter + 1) = natListGetAt state.openWires (seatAfter + 1 + 2) :=
    rightAtSuccessor.trans rightFromState.symm
  exact absurd valuesCollide
    (distinct (seatAfter + 1) (seatAfter + 1 + 2)
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self (seatAfter + 1)) (Nat.le_add_right (seatAfter + 1 + 1) 1))
      distThreeBelowLength)

/-! ## Concrete truth-probe — the colour-free exclusion fires on a real cap step -/

/-- A concrete four-wire seed state `[0, 1, 2, 3]` (fresh counter at `4`), the anchor for the colour-free
exclusion probe. -/
def stringDistinctSeatProbeState : ArcWireState :=
  ArcWireState.mk (List.range 4) [] 4 0 [] []

/-- ★ **The colour-free exclusion fires on a genuine cap step.**  A pair `(0, 1)` seated adjacent at
position `0` — both in the pre-cap state (positionally distinct seed wires, `arcInitialState_wireListDistinct`)
and after a cap consumes the window `(2, 3)` (`stepCapArc … 2`) — descends to having been seated at position
`0` before the cap (the PAST-window branch), run end-to-end through
`stringArcPairSeated_beforeCapStep_ofDistinctSeat` on concrete `Nat` / `ArcWireState` data with NO parity
input.  A machine-checked non-vacuity witness that the distinctness exclusion applies to a real cap. -/
theorem stringDistinctSeatProbe_fires :
    (ArcPairSeated 0 1 0 stringDistinctSeatProbeState ∧ 0 + 2 ≤ 2)
      ∨ (ArcPairSeated 0 1 (0 + 2) stringDistinctSeatProbeState ∧ 2 ≤ 0) := by
  have seatedBefore : ArcPairSeated 0 1 0 stringDistinctSeatProbeState :=
    ⟨by decide, by decide, by decide⟩
  have seatedAfter : ArcPairSeated 0 1 0 (stepCapArc stringDistinctSeatProbeState 2) :=
    ⟨by decide, by decide, by decide⟩
  exact stringArcPairSeated_beforeCapStep_ofDistinctSeat stringDistinctSeatProbeState 2
    (arcInitialState_wireListDistinct 4) seatedBefore (by decide) seatedAfter

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the COLOUR-FREE cap-step gap-closing exclusion is machine-checked (FC-3 r24, B2).**
`stringArcPairSeated_beforeCapStep_ofDistinctSeat` refutes the descent's gap-closing case from POSITION,
not parity: positional distinctness of the pre-cap open wires (`WireListDistinct`, shipped) plus the pair's
pre-cap adjacency force a gap-closing cap to read the pair three positions apart while pre-seating pins them
consecutive — impossible, since distinctness makes equal wire VALUES pin equal POSITIONS
(`natListGetAt_inj_ofWireListDistinct`).  Parity is NEVER mentioned, so `counitUpper` (`base`) and
`counitLower` (`tip`) descend identically — dissolving the wall B1 proved the colour route cannot cross.
`stringDistinctSeatProbe_fires` runs it end-to-end on a concrete four-wire cap step.

  THE RESIDUAL (honest).  This exclusion is the drop-in replacement for
  `stringArcPairSeated_beforeCapStep_ofSameParities`; it takes the pair's pre-cap adjacency as a hypothesis.
  The FULL `StringCapHeadExtractionWordPin` inhabitation still needs: (i) the forward invariant threading the
  toucher's consecutive untouched legs' adjacency through the whole pure-cap prefix (they never separate — a
  cap only removes, never inserts); (ii) re-founding `stringWordPairSeated_bubblesThroughPrefix` on this
  exclusion in place of `prefixSharesWindowMode`; (iii) the four-conjunct assembly on top.  This round settles
  that the exclusion is genuinely colour-free — the r23 plan's block was the colour framing, not the
  mathematics.  `= true`. -/
def fxString_hasDistinctSeatCapExclusion : Bool := true

end FX1Poly.Polygraph
