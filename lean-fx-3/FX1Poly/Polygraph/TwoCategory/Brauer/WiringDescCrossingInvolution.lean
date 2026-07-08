import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescPortReconnection
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescWindowLocality

/-! # KEYSTONE12 ingredient — the R2 NET-IDENTITY port reconnection (two crossings restore each window strand)

The shipped single-crossing reconnection (`stepWiring_crossing_reconnects`, `Brauer/WiringDescPortReconnection.lean`)
proves ONE crossing reconnects its two fresh output ports to its two input window strands, TRANSPOSED.  The R2
relation is `crossing ∘ crossing = id ⊗ id`: two crossings fired at the same position compose the transposition with
itself, so the composite is the boundary IDENTITY on the two window strands.  This file ships that net-identity at the
links level: after two crossings at `position`, each fresh top output port of the DOUBLE crossing is in the SAME
union-find component as the ORIGINAL bottom input strand at the same window slot.

## The two ingredients this file ships (each zero-axiom, structural)

  * ★ **`natListSliceAt_spliceSame`** — the SAME-position splice surgery the window-locality file lacked (it ships
    only the DISJOINT-window facts A / B, `natListSliceAt_spliceRight` / `…_spliceLeftShift`).  Slicing at `position`
    the block just inserted at `position` (after removing `removeCount` there) reads back exactly that block, under
    the window-in-range discipline `position ≤ wires.length`.  Structural on the wire list, off the prefix-take
    helper `natListSliceAt_prefixAll`.  This is the positional half of the port-reconnection `bnodeCorr` residual —
    it identifies the SECOND crossing's input node list with the FIRST crossing's output node list.
  * ★ **`stepWiring_crossing_involution_reconnects`** — the R2 net-identity.  Chains the shipped single-crossing
    reconnection twice: the second crossing reconnects its inputs (= the first's fresh outputs, by
    `natListSliceAt_spliceSame`) to its own fresh outputs transposed, the first crossing's reconnections survive the
    second by connectivity monotonicity (`stepWiring_isSameComponent_ofBase`), and same-component transitivity closes
    each window slot back to its original strand.  Offset- and base-parametric; the window nodes stay abstract.

## Honest scope — this does NOT flip `fxBrauer_hasBrauerSoundness`

This delivers the R2-specific port reconnection composite — the `bnodeCorr` net-identity at the LINKS level.  A full
per-relation `relationAgrees` (the hypothesis the shipped `whisker` move consumes, `Brauer/WiringDescConv.lean`) still
needs (i) the boundary-INDEX surgery lifting this links-level reconnection to the `matchingBoundaryNodes` positional
read, and (ii) the `componentComm` freshness-threaded fold over ALL nodes (combining the shipped monotone half
`processBrauer_isSameComponent_ofBase` with the second-endpoint converse
`isSameComponent_unionFindJoin_eq_ofSecondDisconnected`) to build a `MatchingComponentRenameRel` witness.  For the
collapse trio (snake / snakeMirror / R2) those residuals are net-identity and buildable; for R1 (cap-slide) the
`componentComm` is the cross-order partition independence whose only known renaming route is REFUTED
(`fxBrauer_hasWiringDescBlockSwapWitness = false`).  So no relation's `relationAgrees` closes, and
`fxBrauer_hasBrauerSoundness` STAYS `false`.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The same-position splice surgery -/

/-- Slicing the leading `block.length` wires off `block ++ rest` reads back `block`.  Structural on `block`. -/
theorem natListSliceAt_prefixAll : (block rest : List Nat) →
    natListSliceAt (block ++ rest) 0 block.length = block
  | [], rest => sliceAt_count_zero rest 0
  | headWire :: tailBlock, rest => by
      show natListSliceAt (headWire :: (tailBlock ++ rest)) 0 (tailBlock.length + 1) = headWire :: tailBlock
      rw [sliceAt_cons_zero_succ headWire (tailBlock ++ rest) tailBlock.length,
        natListSliceAt_prefixAll tailBlock rest]

/-- ★ **The SAME-position splice reads back the inserted block.**  A slice at `position` (width `block.length`) of
the list obtained by removing `removeCount` wires at `position` and inserting `block` there reads back exactly
`block`, under the window-in-range discipline `position ≤ wires.length` (the past-end degeneracy is ruled out).
Structural on the wire list; at `position = 0` the insert prepends the block and `natListSliceAt_prefixAll` reads it,
at a successor position the splice-cons peel recurses. -/
theorem natListSliceAt_spliceSame (removeCount : Nat) (block : List Nat) :
    (wires : List Nat) → (position : Nat) →
    position ≤ wires.length →
    natListSliceAt (natListInsertAt (natListRemoveManyAt wires position removeCount) position block)
        position block.length
      = block
  | wires, 0, _ => by
      rw [insertAt_zero (natListRemoveManyAt wires 0 removeCount) block]
      exact natListSliceAt_prefixAll block (natListRemoveManyAt wires 0 removeCount)
  | [], position + 1, rangeLe => absurd rangeLe (Nat.not_succ_le_zero position)
  | headWire :: tailWires, position + 1, rangeLe => by
      rw [splice_succ_cons removeCount block headWire tailWires position,
        sliceAt_cons_succ headWire
          (natListInsertAt (natListRemoveManyAt tailWires position removeCount) position block)
          position block.length]
      exact natListSliceAt_spliceSame removeCount block tailWires position (Nat.le_of_succ_le_succ rangeLe)

/-! ## The second crossing reads the first crossing's output block -/

/-- ★ **The second crossing's input nodes ARE the first crossing's output nodes.**  Firing a crossing at `position`
replaces the two window strands with its two fresh outputs; a second crossing at the SAME position slices those two
freshly-inserted outputs back out as its own inputs.  Read off by `natListSliceAt_spliceSame` at the crossing's
`inputCount = outputCount = 2`, under the window-in-range discipline. -/
theorem stepWiring_crossing_secondInputs (state : WireState) (position : Nat)
    (rangeLe : position ≤ state.openWires.length) :
    stepWiringInputNodes (stepWiring state position crossingWiring) position crossingWiring
      = stepWiringOutputNodes state crossingWiring := by
  show natListSliceAt
      (natListInsertAt (natListRemoveManyAt state.openWires position crossingWiring.inputCount) position
        (stepWiringOutputNodes state crossingWiring))
      position crossingWiring.inputCount
    = stepWiringOutputNodes state crossingWiring
  exact natListSliceAt_spliceSame crossingWiring.inputCount (stepWiringOutputNodes state crossingWiring)
    state.openWires position rangeLe

/-! ## The R2 net-identity reconnection -/

/-- ★ **Two crossings restore each window strand — the R2 net-identity port reconnection.**  After firing the
crossing twice at `position`, each fresh top output port of the double crossing is in the SAME union-find component as
the ORIGINAL bottom input strand at the same window slot (output `0` reconnects to input `0`, output `1` to input
`1`).  This is the transposition composed with itself: the first crossing sends input `k` to the strand under output
`1-k`, the second sends that back, so the net boundary effect on the two window strands is the identity.  Chained
from the shipped single-crossing reconnection (`stepWiring_crossing_reconnects`) applied to both crossings — the
second's inputs identified with the first's outputs by `stepWiring_crossing_secondInputs`, the first's reconnections
carried across the second by connectivity monotonicity (`stepWiring_isSameComponent_ofBase`) — and closed by
same-component transitivity.  Offset- and base-parametric under the window-in-range discipline. -/
theorem stepWiring_crossing_involution_reconnects (state : WireState) (position : Nat)
    (forest : isUnionFindForest state.links)
    (rangeLe : position ≤ state.openWires.length) :
    isSameComponent (stepWiring (stepWiring state position crossingWiring) position crossingWiring).links
        (natListGetAt (stepWiringOutputNodes (stepWiring state position crossingWiring) crossingWiring) 0)
        (natListGetAt (stepWiringInputNodes state position crossingWiring) 0) = true
    ∧ isSameComponent (stepWiring (stepWiring state position crossingWiring) position crossingWiring).links
        (natListGetAt (stepWiringOutputNodes (stepWiring state position crossingWiring) crossingWiring) 1)
        (natListGetAt (stepWiringInputNodes state position crossingWiring) 1) = true := by
  have forest1 : isUnionFindForest (stepWiring state position crossingWiring).links :=
    stepWiring_links_isUnionFindForest state position crossingWiring forest
  obtain ⟨firstInZeroToMidOne, firstInOneToMidZero⟩ := stepWiring_crossing_reconnects state position forest
  obtain ⟨secondMidZeroToOutOne, secondMidOneToOutZero⟩ :=
    stepWiring_crossing_reconnects (stepWiring state position crossingWiring) position forest1
  rw [stepWiring_crossing_secondInputs state position rangeLe] at secondMidZeroToOutOne secondMidOneToOutZero
  have liftedInZeroToMidOne :
      isSameComponent (stepWiring (stepWiring state position crossingWiring) position crossingWiring).links
        (natListGetAt (stepWiringInputNodes state position crossingWiring) 0)
        (natListGetAt (stepWiringOutputNodes state crossingWiring) 1) = true :=
    stepWiring_isSameComponent_ofBase (stepWiring state position crossingWiring) position crossingWiring forest1
      _ _ firstInZeroToMidOne
  have liftedInOneToMidZero :
      isSameComponent (stepWiring (stepWiring state position crossingWiring) position crossingWiring).links
        (natListGetAt (stepWiringInputNodes state position crossingWiring) 1)
        (natListGetAt (stepWiringOutputNodes state crossingWiring) 0) = true :=
    stepWiring_isSameComponent_ofBase (stepWiring state position crossingWiring) position crossingWiring forest1
      _ _ firstInOneToMidZero
  refine ⟨?_, ?_⟩
  · exact isSameComponent_trans _ _ _ _
      (isSameComponent_flip _ _ _ secondMidOneToOutZero)
      (isSameComponent_flip _ _ _ liftedInZeroToMidOne)
  · exact isSameComponent_trans _ _ _ _
      (isSameComponent_flip _ _ _ secondMidZeroToOutOne)
      (isSameComponent_flip _ _ _ liftedInOneToMidZero)

/-! ## Honesty markers -/

/-- **Honesty marker — the SAME-position splice surgery is SHIPPED.**  `natListSliceAt_spliceSame` reads back the
block just spliced in at a position, the positional half of the port-reconnection `bnodeCorr` the window-locality
file lacked (it ships only the disjoint-window facts).  `= true`. -/
def fxBrauer_hasSamePositionSpliceSurgery : Bool := true

/-- ★ **Honesty marker — the R2 net-identity port reconnection is SHIPPED at the links level.**
`stepWiring_crossing_involution_reconnects` proves two crossings at the same position reconnect each fresh top output
port to its original bottom input strand (transposition composed with itself = boundary identity), offset- and
base-parametric, chaining the shipped single-crossing reconnection twice via the same-position splice surgery and
connectivity monotonicity.  This is the R2 half of the collapse trio's `bnodeCorr` net-identity.  The residual to a
full R2 `relationAgrees` is the boundary-INDEX surgery lifting this to the `matchingBoundaryNodes` read plus the
`componentComm` freshness-threaded fold over all nodes.  `= true`. -/
def fxBrauer_hasCrossingInvolutionReconnection : Bool := true

/-- **Honesty marker — this does NOT flip `fxBrauer_hasBrauerSoundness`; the honest count stays 0/5
`relationAgrees` closed.**  This ships the R2 net-identity reconnection composite (the `bnodeCorr` at links level),
not a `relationAgrees`.  Closing R2 (and the snakes) additionally needs the boundary-index surgery + the
`componentComm` freshness fold to a `MatchingComponentRenameRel` witness; R1 (cap-slide) is walled by the refuted
cross-order block-swap (`fxBrauer_hasWiringDescBlockSwapWitness = false`).  With R1 walled, the full congruence
closure cannot close this round regardless, so `fxBrauer_hasBrauerSoundness` STAYS `false`.  `= false`. -/
def fxBrauer_hasCrossingInvolutionReconnectionFlipsSoundness : Bool := false

end FX1Poly.Polygraph
