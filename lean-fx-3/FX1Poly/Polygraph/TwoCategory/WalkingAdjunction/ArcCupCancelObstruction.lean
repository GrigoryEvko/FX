import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineTraceDecision
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryChain
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionModeParity

/-! # ArcCupCancelObstruction — the unconditional cup-head cancellation is FALSE

The cap-head transport cancellation (`arcCapHeadFolded_extractArc_cancel`) inverts the
composite extract field by field, because a cap HEAD consumes two bottom ports the tail
never touches: every composite field is a splice of fresh-extract data.  A cup head is the
asymmetric case: it CREATES the two leg ports the tail then acts on, and the composite
merges the two legs into one strand (`stepCupArc` joins them), so the composite counts see
only the SUM of the two leg components' event data.  The fresh run keeps the legs separate,
so the fresh extract remembers WHICH leg each tail event attached to — information the
composite provably forgets.

This file pins that as a machine-checked refutation.  The witness pair, over the peeled cup
at window `0` on bottom boundary `2` (base parity, so mode-realizable):

  * LEFT tail  = [cup at window 0, cap at window 1] — its cup event lands on the strand of
    the head's LEFT leg;
  * RIGHT tail = [cup at window 2, cap at window 1] — the same two generators, but the cap
    connects the tail cup to the head's RIGHT leg.

Both tails are boundary-chained at `4`, both keep the head's legs fresh-separated, and the
two COMPOSITE extracts are EQUAL — yet the two FRESH tail extracts differ (internal cup
counts `[1,0,0,0,1,0,0,0]` vs `[0,1,0,0,0,1,0,0]`: the leg-split of the joined count).
So no theorem can recover the fresh extract from the composite extract alone.

The obligation `SpineArcHeadExtractionChained` SURVIVES this obstruction: on the witness
pair the tail cup has an EMPTY generator domain at window 0, so it is window-disjoint from
the head cup and swaps THROUGH it — the matched remainder must be CHOSEN inside the second
list's through-the-head trace orbit (re-selecting which cup realizes the head), not derived
from composite-extract equality.  That orbit choice is the corrected shape of the cup leg
of the head-cancellation assembly.

Raw Lean 4 + Init; the equalities/disequalities close by kernel `decide` on the computable
arc fold.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The witness cells -/

/-- The bottom boundary of the peeled composite: the length-2 path `L.R` at `base`. -/
def arcCupObstructionBottomPath : ModalityPath adjunctionGraph
    AdjunctionMode.base AdjunctionMode.base :=
  adjunctionLeftThenRight

/-- The left whisker of the connecting cap: the single modality `L` (`base -> tip`). -/
def arcCupObstructionCapLeftContext : ModalityPath adjunctionGraph
    AdjunctionMode.base AdjunctionMode.tip :=
  singletonModalityPath (graph := adjunctionGraph) AdjunctionModality.left

/-- The right whisker of the connecting cap: the length-3 path `R.L.R` (`tip -> base`). -/
def arcCupObstructionCapRightContext : ModalityPath adjunctionGraph
    AdjunctionMode.tip AdjunctionMode.base :=
  ModalityPath.cons AdjunctionModality.right
    (ModalityPath.cons AdjunctionModality.left
      (ModalityPath.cons AdjunctionModality.right
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)))

/-- The tail cup fired at window 0 over the length-4 boundary `LR.P`. -/
def arcCupObstructionCupAtWindowZero :=
  RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
    (composePath adjunctionLeftThenRight arcCupObstructionBottomPath) adjunctionUnitTwoCell

/-- The tail cup fired at window 2 over the length-4 boundary `LR.P`. -/
def arcCupObstructionCupAtWindowTwo :=
  RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
    adjunctionLeftThenRight
    (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
      arcCupObstructionBottomPath adjunctionUnitTwoCell)

/-- The connecting cap fired at window 1 over the length-6 boundary `LR.LR.P`. -/
def arcCupObstructionConnectingCap :=
  RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
    arcCupObstructionCapLeftContext
    (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
      arcCupObstructionCapRightContext adjunctionCounitTwoCell)

/-- The LEFT-attached tail: cup at 0 then cap at 1 — the tail cup event ends on the strand
of the head's LEFT leg. -/
def arcCupObstructionLeftTail :=
  RawTwoCellExpr.vcomp arcCupObstructionCupAtWindowZero arcCupObstructionConnectingCap

/-- The RIGHT-attached tail: cup at 2 then cap at 1 — the tail cup event ends on the strand
of the head's RIGHT leg. -/
def arcCupObstructionRightTail :=
  RawTwoCellExpr.vcomp arcCupObstructionCupAtWindowTwo arcCupObstructionConnectingCap

/-- The left-attached tail's spine atoms (chained at boundary 4). -/
def arcCupObstructionLeftTailAtoms :
    List (SpineAtom adjunctionModeSignature AdjunctionMode.base AdjunctionMode.base) :=
  arcCupObstructionLeftTail.spine

/-- The right-attached tail's spine atoms (chained at boundary 4). -/
def arcCupObstructionRightTailAtoms :
    List (SpineAtom adjunctionModeSignature AdjunctionMode.base AdjunctionMode.base) :=
  arcCupObstructionRightTail.spine

/-! ## The witness facts (kernel-decided on the computable arc fold) -/

/-- Both tails are boundary-chained at 4 (the peeled cup head's cod boundary). -/
theorem arcCupObstructionLeftTail_isChained :
    SpineBoundaryChained 4 arcCupObstructionLeftTailAtoms :=
  arcCupObstructionLeftTail.spineBoundaryChained_spine

/-- Both tails are boundary-chained at 4 (the peeled cup head's cod boundary). -/
theorem arcCupObstructionRightTail_isChained :
    SpineBoundaryChained 4 arcCupObstructionRightTailAtoms :=
  arcCupObstructionRightTail.spineBoundaryChained_spine

/-- The head's window sits at BASE parity — the witness is a mode-realizable cup window. -/
theorem arcCupObstruction_windowParityIsBase :
    adjunctionModeAtDistance AdjunctionMode.base 0 = AdjunctionMode.base := rfl

/-- The LEFT tail keeps the head's fresh legs (ports 0 and 1 at the fresh boundary 4)
SEPARATE — the obstruction lives strictly inside the legs-separate world. -/
theorem arcCupObstructionLeftTail_legsSeparate :
    isSameComponent
      (processArcSpine (ArcWireState.mk (List.range 4) [] 4 0 [] [])
        arcCupObstructionLeftTailAtoms).links 0 1 = false := by decide

/-- The RIGHT tail keeps the head's fresh legs SEPARATE as well. -/
theorem arcCupObstructionRightTail_legsSeparate :
    isSameComponent
      (processArcSpine (ArcWireState.mk (List.range 4) [] 4 0 [] [])
        arcCupObstructionRightTailAtoms).links 0 1 = false := by decide

set_option maxHeartbeats 1600000 in
/-- ★ The two COMPOSITE extracts — over the SAME peeled cup at window 0 on bottom boundary
2 — are EQUAL: the composite merges the two legs into one strand and sees only the joined
event data. -/
theorem arcCupObstruction_composite_extract_eq :
    extractArc 2
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range 2) [] 2 0 [] []) 0)
          arcCupObstructionLeftTailAtoms)
      = extractArc 2
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range 2) [] 2 0 [] []) 0)
            arcCupObstructionRightTailAtoms) := by decide +kernel

set_option maxHeartbeats 1600000 in
/-- ★ The two FRESH tail extracts — at the moved boundary 4 — DIFFER: the fresh run keeps
the legs separate, so the internal cup counts remember which leg the tail cup attached to
(`[1,0,0,0,1,0,0,0]` vs `[0,1,0,0,0,1,0,0]`). -/
theorem arcCupObstruction_freshTail_extract_ne :
    ¬ (extractArc 4
          (processArcSpine (ArcWireState.mk (List.range 4) [] 4 0 [] [])
            arcCupObstructionLeftTailAtoms)
        = extractArc 4
            (processArcSpine (ArcWireState.mk (List.range 4) [] 4 0 [] [])
              arcCupObstructionRightTailAtoms)) := by decide +kernel

/-! ## The refuted universal -/

/-- The UNCONDITIONAL cup-head cancellation — the literal mirror of
`arcCapHeadFolded_extractArc_cancel` with the cup's boundary arithmetic (fresh boundary
`bottomCount + 2`, window fitting the bottom boundary): equal composite extracts over the
same peeled cup would force equal fresh tail extracts.  FALSE — see
`not_arcCupHeadCancellationUnconditional`. -/
def ArcCupHeadCancellationUnconditional : Prop :=
  ∀ {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat),
    windowPosition ≤ bottomCount →
    ∀ (firstAtoms secondAtoms :
        List (SpineAtom adjunctionModeSignature overallSource overallTarget)),
    SpineBoundaryChained (bottomCount + 2) firstAtoms →
    SpineBoundaryChained (bottomCount + 2) secondAtoms →
    extractArc bottomCount
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) firstAtoms)
      = extractArc bottomCount
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) secondAtoms) →
    extractArc (bottomCount + 2)
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms)
      = extractArc (bottomCount + 2)
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            secondAtoms)

/-- ★ **The unconditional cup-head cancellation is REFUTED.**  The witness pair meets every
hypothesis — chained tails, a fitting base-parity window, even fresh-separated legs — with
equal composite extracts, yet distinct fresh extracts.  The composite provably forgets the
leg-split of the tail's event data. -/
theorem not_arcCupHeadCancellationUnconditional :
    ¬ ArcCupHeadCancellationUnconditional := fun cancellation =>
  arcCupObstruction_freshTail_extract_ne
    (cancellation 2 0 (Nat.zero_le 2)
      arcCupObstructionLeftTailAtoms arcCupObstructionRightTailAtoms
      arcCupObstructionLeftTail_isChained arcCupObstructionRightTail_isChained
      arcCupObstruction_composite_extract_eq)

/-! ## Honesty marker -/

/-- **Honesty marker — the unconditional cup-head cancellation is REFUTED (peel campaign H,
the cup-cancel spike).**  `not_arcCupHeadCancellationUnconditional`: two chained tails over
the same peeled cup (window 0, bottom boundary 2, base parity, legs fresh-separated in both
runs) share the composite extract yet differ at the fresh boundary — the composite joins
the cup's legs into one strand, so it sees only the SUM of the two leg components' internal
event counts, and the leg-split is forgotten.  The cap cancellation
(`arcCapHeadFolded_extractArc_cancel`) is unaffected: a cap head CONSUMES its two ports
before the tail runs, so its composite fields are splices, not merges.  Corrected route for
the head-cancellation assembly's cup leg: the matched remainder must be CHOSEN inside the
second list's through-the-head trace orbit (on the witness pair, the window-0 tail cup has
an empty generator domain, hence swaps through the head — re-selecting which cup realizes
the head aligns the leg attachment), not derived from composite equality alone.  `= true`. -/
def fxMode_hasArcCupCancelObstruction : Bool := true

end FX1Poly.Polygraph
