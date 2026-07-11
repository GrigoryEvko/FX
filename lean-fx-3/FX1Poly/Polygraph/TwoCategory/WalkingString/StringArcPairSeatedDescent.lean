import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPairSeatedDescent
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringAdjointTripleModeParity

/-! # WalkingString/StringArcPairSeatedDescent — the cap-step gap-closing exclusion at the adjoint triple
(FC-3 r22, B2 P2)

The backward seating descent (`WalkingAdjunction/ArcPairSeatedDescent`) has three parts, of which TWO are pure
`Nat`/`ArcWireState` positional lemmas with NO signature at all — `ArcPairSeated`, `arcPairSeated_beforeCupStep`,
and the positional core `arcPairSeated_beforeCapStep` (which excludes the gap-closing cap by an explicit
hypothesis).  Those are colour-blind and REUSED VERBATIM (imported directly), so the string descent needs only the
ONE colour-aware wrapper: the parity refutation of the gap-closing cap.

At the single adjunction a consuming cap always has `tip` parity, so the arc wrapper hardwires it.  At the adjoint
triple a cap can seat at EITHER parity (`counitLower` at `tip`, `counitUpper` at `base`), so the exclusion is
conditioned on BOTH the seat and the window carrying `tip` parity — exactly the two hypotheses the arc wrapper
also takes.  The refutation is then pure parity arithmetic (`adjointTripleModeAtDistance` on the successor is the
opposite mode), re-keyed through the string parity substrate `StringAdjointTripleModeParity`.

Raw Lean 4 + Init; the refutation is one `rw` chain closing on `AdjointTripleMode.noConfusion`.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **Backward descent through a cap at the adjoint triple.**  When the seat AND the window both carry `tip`
parity, the gap-closing exclusion is FREE from parity: the window at the seat's successor would have the OPPOSITE
parity (`base`), contradicting its `tip` parity — so a cap at the seat's successor cannot exist, and a seated pair
descends through the cap.  The clone of `arcPairSeated_beforeCapStep_ofTipParities` re-keyed through the string
parity; the positional core `arcPairSeated_beforeCapStep` is reused verbatim (it is colour-blind). -/
theorem stringArcPairSeated_beforeCapStep_ofTipParities (state : ArcWireState)
    (windowPosition : Nat) {leftNode rightNode seatAfter : Nat}
    {sourceMode : AdjointTripleMode}
    (hasSeatTipParity :
      adjointTripleModeAtDistance sourceMode seatAfter = AdjointTripleMode.tip)
    (hasWindowTipParity :
      adjointTripleModeAtDistance sourceMode windowPosition = AdjointTripleMode.tip)
    (windowFits : windowPosition + 2 ≤ state.openWires.length)
    (seatedAfter : ArcPairSeated leftNode rightNode seatAfter
      (stepCapArc state windowPosition)) :
    (ArcPairSeated leftNode rightNode seatAfter state ∧ seatAfter + 2 ≤ windowPosition)
      ∨ (ArcPairSeated leftNode rightNode (seatAfter + 2) state
          ∧ windowPosition ≤ seatAfter) := by
  refine arcPairSeated_beforeCapStep state windowPosition ?_ windowFits seatedAfter
  intro isGapClosing
  rw [isGapClosing] at hasWindowTipParity
  have oppositeIsTip :
      adjointTripleOppositeMode (adjointTripleModeAtDistance sourceMode seatAfter)
        = AdjointTripleMode.tip := hasWindowTipParity
  rw [hasSeatTipParity] at oppositeIsTip
  exact AdjointTripleMode.noConfusion oppositeIsTip

/-! ## Honesty marker -/

/-- **Honesty marker — the cap-step gap-closing exclusion is SHIPPED at the adjoint triple (FC-3 r22, B2 P2).**
`stringArcPairSeated_beforeCapStep_ofTipParities` re-keys the arc wrapper `arcPairSeated_beforeCapStep_ofTipParities`
through the string parity: when seat and window both carry `tip` parity, no gap-closing cap can seat at the
successor.  The positional core (`arcPairSeated_beforeCapStep`), the cup-step (`arcPairSeated_beforeCupStep`), and
the `ArcPairSeated` predicate are pure `Nat`/`ArcWireState` and reused verbatim.  What this marker does NOT claim:
threading the descent backward through a whole untouched prefix and assembling the `WordBubblesToFront` witness
from the located certificate — the word descent master, phantom-locked at its arc source, is the standing residual
(the next round).  `= true`. -/
def fxString_hasArcPairSeatedDescent : Bool := true

end FX1Poly.Polygraph
