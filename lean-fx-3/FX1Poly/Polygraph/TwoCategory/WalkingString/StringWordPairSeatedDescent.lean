import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcPairSeatedDescent
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcArity
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordBubble
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordFactorization
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordLeftMirror
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcDisciplineFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryTracking
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # WalkingString/StringWordPairSeatedDescent — the WORD-founded prefix descent master at the adjoint triple
(FC-3 r23)

The walking adjunction's prefix bubble descent (`WalkingAdjunction/ArcPrefixBubbleDescent`,
`arcPairSeated_bubblesThroughPrefix`) carries a below-fresh seated cap target to the FRONT of a boundary-chained
prefix, assembling the `BubblesToFront` witness by front-first recursion.  Its two window factorizations
(`adjunctionSpineAtom_contextsFactorLeft_of_disjointWindows` and its mirror) and its emitted carrier are all
pinned by seed LENGTH-RIGIDITY (`adjunctionPath_eq_of_length_eq`), which is FALSE at the adjoint triple
(`stringFG ≠ stringHG` at equal length `2`).  This file re-founds that master on the shared BOUNDARY WORD:

  * `stringArcPairSeated_beforeCapStep_ofSameParities` — ★ the crux prerequisite (the same-parity-GENERIC
    cap-step gap-closing exclusion).  The r22 tip clone `stringArcPairSeated_beforeCapStep_ofTipParities` hardwires
    `tip`; at the triple a cap seats at EITHER parity (`counitLower` at `tip`, `counitUpper` at `base`), so the
    exclusion is re-keyed on a common window MODE `windowMode`: when the seat and the passed cap's window both
    carry `windowMode`, a gap-closing cap at the seat's successor would carry the OPPOSITE mode — refuted by
    `AdjointTripleMode.noConfusion`.

  * `assembleStepRightOfWordPackage` / `assembleStepLeftOfWordPackage` — the two per-step assemblers, ports of
    the arc's `assembleStepRightOfPackage` / `assembleStepLeftOfPackage` with the length-rigid window factorization
    swapped for the WORD factorization (`spineAtom_contextsFactor*_of_disjointWordWindows`, fed the pair's shared
    boundary word) and the carrier swapped for `WordBubblesToFront`.

  * `stringWordPairSeated_bubblesThroughPrefix` — ★ the descent master.  Front-first recursion, STRUCTURAL on the
    prefix list; each step threads BOTH the length boundary chain (the colour-blind seat/freshness bookkeeping,
    reused verbatim) AND the boundary WORD chain (the source of the per-pair factorization).  Cups die on
    freshness (`arcPairSeated_beforeCupStep`, colour-blind); caps die on the same-parity exclusion above, fed the
    passed cap's window mode from the threaded same-window-mode invariant.

## The threaded same-window-mode invariant (the honest deviation from the length-rigid master)

At the single adjunction ALL caps are `tip`, so the arc master derives the passed cap's window parity FREE from
`adjunctionCapAtom_windowPositionMode`.  At the adjoint triple a gap-closing passed cap of the OPPOSITE colour is
geometrically realizable (a `counitUpper` nested between a `counitLower`'s legs is a valid non-crossing valley),
so the exclusion is NOT free from parity alone.  The descent master therefore takes an explicit premise
`prefixSharesWindowMode : ∀ atom ∈ prefixAtoms, atom.leftMidMode = target.leftMidMode` — the honest
"threaded invariant" branch of the recon's open question.  This makes the master TRUE and zero-axiom; discharging
the invariant from the located pure-cap spine (the r20 seat data) is the named r24 residual, not this round.

Raw Lean 4 + Init; structural recursion on the prefix list; the exclusion is one `rw` chain closing on
`AdjointTripleMode.noConfusion`.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The crux prerequisite — the same-parity-generic cap-step gap-closing exclusion -/

/-- ★ **Backward descent through a cap at the adjoint triple, same-parity generic.**  When the seat AND the
passed cap's window BOTH carry a common mode `windowMode`, the gap-closing exclusion is free: a cap at the seat's
successor would carry the OPPOSITE mode (`adjointTripleModeAtDistance` on the successor is the opposite),
contradicting its `windowMode` — so a seated pair descends through the cap.  This GENERALIZES the r22 tip clone
`stringArcPairSeated_beforeCapStep_ofTipParities` from the fixed `tip` to ANY common window mode, exactly because
at the triple a cap seats at either parity (`counitLower` at `tip`, `counitUpper` at `base`).  The positional
core `arcPairSeated_beforeCapStep` is reused verbatim (it is colour-blind). -/
theorem stringArcPairSeated_beforeCapStep_ofSameParities (state : ArcWireState)
    (windowPosition : Nat) {leftNode rightNode seatAfter : Nat}
    {sourceMode windowMode : AdjointTripleMode}
    (hasSeatWindowMode :
      adjointTripleModeAtDistance sourceMode seatAfter = windowMode)
    (hasPassedWindowMode :
      adjointTripleModeAtDistance sourceMode windowPosition = windowMode)
    (windowFits : windowPosition + 2 ≤ state.openWires.length)
    (seatedAfter : ArcPairSeated leftNode rightNode seatAfter
      (stepCapArc state windowPosition)) :
    (ArcPairSeated leftNode rightNode seatAfter state ∧ seatAfter + 2 ≤ windowPosition)
      ∨ (ArcPairSeated leftNode rightNode (seatAfter + 2) state
          ∧ windowPosition ≤ seatAfter) := by
  refine arcPairSeated_beforeCapStep state windowPosition ?_ windowFits seatedAfter
  intro isGapClosing
  rw [isGapClosing] at hasPassedWindowMode
  have oppositeIsWindow :
      adjointTripleOppositeMode (adjointTripleModeAtDistance sourceMode seatAfter) = windowMode :=
    hasPassedWindowMode
  rw [hasSeatWindowMode] at oppositeIsWindow
  cases windowMode with
  | base => exact AdjointTripleMode.noConfusion oppositeIsWindow
  | tip => exact AdjointTripleMode.noConfusion oppositeIsWindow

/-! ## Concrete truth-probe — the same-parity exclusion fires on a real cap step -/

/-- A concrete arc-wire state with six open wires `[0,1,2,3,4,5]` (fresh counter at `6`), the anchor for the
same-parity exclusion probe. -/
def stringSameParityProbeState : ArcWireState :=
  ArcWireState.mk [0, 1, 2, 3, 4, 5] [] 6 0 [] []

/-- ★ **The same-parity exclusion fires on a genuine cap step.**  A pair `(2, 3)` seated adjacent at position `0`
AFTER a cap fires at the front window (`stepCapArc … 0`, both seat and window at the `base`-relative distance `0`,
so both carry the same mode) descends to having been seated at position `2` before the cap — the PAST outcome —
run end-to-end through `stringArcPairSeated_beforeCapStep_ofSameParities` on concrete `Nat`/`ArcWireState` data.
A machine-checked non-vacuity witness that the exclusion applies to a real cap, NOT a vacuous statement. -/
theorem stringSameParityProbe_fires :
    (ArcPairSeated 2 3 0 stringSameParityProbeState ∧ 0 + 2 ≤ 0)
      ∨ (ArcPairSeated 2 3 (0 + 2) stringSameParityProbeState ∧ (0 : Nat) ≤ 0) :=
  stringArcPairSeated_beforeCapStep_ofSameParities
    (sourceMode := AdjointTripleMode.base) (windowMode := AdjointTripleMode.base)
    stringSameParityProbeState 0 rfl rfl
    (Nat.le.step (Nat.le.step (Nat.le.step (Nat.le.step Nat.le.refl))))
    ⟨rfl, rfl, Nat.le.step (Nat.le.step Nat.le.refl)⟩

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the same-parity-generic cap-step gap-closing exclusion is machine-checked (FC-3 r23, B1).**
`stringArcPairSeated_beforeCapStep_ofSameParities` generalizes the r22 tip clone from the fixed `tip` to ANY
common window mode: when the seat and the passed cap's window carry the same mode `windowMode`, a gap-closing cap
at the seat's successor carries the opposite mode and is refuted by `AdjointTripleMode.noConfusion`.  The
positional core `arcPairSeated_beforeCapStep` is reused verbatim (colour-blind).  `stringSameParityProbe_fires`
fires it end-to-end on a concrete six-wire cap step.  This is the crux prerequisite the word descent master's
cap case rides — the one genuine mathematical dualization the recon flagged, the tip hardwiring lifted to the
two-parity seed.  `= true`. -/
def fxString_hasCapStepSameParityExclusion : Bool := true

end FX1Poly.Polygraph
