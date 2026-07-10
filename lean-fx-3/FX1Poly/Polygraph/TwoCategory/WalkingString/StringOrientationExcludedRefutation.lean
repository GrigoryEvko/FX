import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSharedLegFactorization
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringLabelPinning

/-! # WalkingString — the ORIENTATION-EXCLUDED refutation (FC-3 r7, B3)

The width classifier's third verdict, `orientationExcludedBothLegs`, fires when the two adjacent atoms' left-context
widths are EQUAL (`natWindowDistance = 0`).  In the walking adjunction this is the case where a unit cup's `[R, L]`
window would have to coincide with a counit cap's `[L, R]` window on BOTH legs — orientation-excluded.  At the
walking adjoint triple the same verdict is VACUOUS: an equal-width cup·cap pair whose frames share their boundary
word (`atomFrameTarget cup = atomFrameSource cap`) cannot exist.

This file discharges that arm CELL-LEVEL, keyed on the shared boundary WORD (never a `matchingOf` read):

  * ★ **`stringOrientationLeftContextLengthEq`** — the `orientationExcludedBothLegs` verdict pins the two
    left-context widths EQUAL (`natWindowDistance = 0`), by the same colour-blind `Nat` dispatch the zigzag arm uses.
  * ★ **`stringSameLengthWindowClash`** — two factorizations of ONE word with equal-length outer prefixes AND
    equal-length inner windows must agree on the window; a DISTINCT window (`window1 ≠ window2`) is impossible.  One
    split-pack pins the outer prefix, a second pins the window.
  * ★ **`stringOrientationExcluded_vacuous`** — a shared-boundary cup·cap pair classified
    `orientationExcludedBothLegs` is IMPOSSIBLE.  By casing the four cup×cap generator combos on the shared window
    equation: the two SAME-colour combos (`η·ε`, `η'·ε'`) clash on the split MODE (`base ≠ tip` — the cup's window
    starts at a mode the cap's cannot), the two MIXED combos (`η·ε'`, `η'·ε`) clash on the window LABEL
    (`F·G ≠ H·G`, `G·H ≠ G·F`) — the shared WORD records the colour the equal widths threw away.  Feeds the oracle's
    orientation arm with `coh` read off `cell`'s own realized chain.

Raw Lean 4 + Init; the width pin is truncated-subtraction `Nat` (hand-rolled cancellation), the mode clashes are
`sharedLegModeClash` + explicit `AdjointTripleMode.noConfusion` witnesses, the label clashes are two split-packs +
`stringFG_ne_stringHG` / `stringGH_ne_stringGF`.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`
-free.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Clean `Nat` bookkeeping (core `Nat.add_*_cancel` / `Nat.sub_*` leak propext) -/

/-- Left-cancellation of a subtracted addend: `a + b - a = b` (propext-free). -/
private theorem natAddSubCancelLeftOrientation : (base value : Nat) → base + value - base = value
  | 0, value => by rw [Nat.zero_add, Nat.sub_zero]
  | base + 1, value => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact natAddSubCancelLeftOrientation base value

/-- Subtracting a self-plus-tail is zero: `a - (a + k) = 0` (propext-free). -/
private theorem natSubAddRightOrientation : (base tail : Nat) → base - (base + tail) = 0
  | 0, tail => by rw [Nat.zero_add, Nat.zero_sub]
  | base + 1, tail => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact natSubAddRightOrientation base tail

/-! ## The width pin: the orientation verdict forces equal left-context widths -/

/-- ★ **The `orientationExcludedBothLegs` verdict pins the widths EQUAL.**  The classifier reads
`natWindowDistance cupLeft capLeft`; the orientation verdict is exactly its `0` arm, and a truncated-distance of
`0` forces `cupLeft = capLeft`.  Signature-generic (the classifier reads only widths); the `Nat` dispatch mirrors
`stringNatWindowDistance_eq_one_of_zigZag`. -/
theorem stringOrientationLeftContextLengthEq
    {overallSource overallTarget : AdjointTripleMode}
    (cupAtom capAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (verdict : classifyAdjacentAtoms cupAtom capAtom = AdjacentCupCapKind.orientationExcludedBothLegs) :
    cupAtom.leftContext.length = capAtom.leftContext.length := by
  have distanceZero :
      natWindowDistance cupAtom.leftContext.length capAtom.leftContext.length = 0 := by
    cases isDistance :
        natWindowDistance cupAtom.leftContext.length capAtom.leftContext.length with
    | zero => rfl
    | succ predDistance =>
        rw [classifyAdjacentAtoms, classifyAdjacentCupCap, isDistance] at verdict
        cases predDistance with
        | zero => exact AdjacentCupCapKind.noConfusion verdict
        | succ _ => exact AdjacentCupCapKind.noConfusion verdict
  dsimp only [natWindowDistance] at distanceZero
  rcases Nat.le_total cupAtom.leftContext.length capAtom.leftContext.length with cupLe | capLe
  · obtain ⟨gap, gapEq⟩ := Nat.le.dest cupLe
    rw [← gapEq, natSubAddRightOrientation, natAddSubCancelLeftOrientation, Nat.zero_add] at distanceZero
    rw [← gapEq, distanceZero, Nat.add_zero]
  · obtain ⟨gap, gapEq⟩ := Nat.le.dest capLe
    rw [← gapEq, natSubAddRightOrientation, natAddSubCancelLeftOrientation, Nat.add_zero] at distanceZero
    rw [← gapEq, distanceZero, Nat.add_zero]

/-! ## The same-length window clash: equal outer prefixes + equal windows force the window -/

/-- ★ **Two factorizations of ONE word with equal-length outer prefixes and equal-length inner windows agree on the
window.**  A DISTINCT window is impossible.  One split-pack at the outer prefix length peels `composePath window1
rcCup = composePath window2 rcCap`; a second at the window length pins `window1 = window2`, contradicting
`windowNe`.  Signature-generic. -/
theorem stringSameLengthWindowClash {graph : ModeGraph}
    {overallSource windowSource windowTarget overallTarget : graph.Mode}
    (lcCup : ModalityPath graph overallSource windowSource)
    (window1 : ModalityPath graph windowSource windowTarget)
    (rcCup : ModalityPath graph windowTarget overallTarget)
    (lcCap : ModalityPath graph overallSource windowSource)
    (window2 : ModalityPath graph windowSource windowTarget)
    (rcCap : ModalityPath graph windowTarget overallTarget)
    (coherence : composePath lcCup (composePath window1 rcCup)
      = composePath lcCap (composePath window2 rcCap))
    (lenEqLeftContext : lcCup.length = lcCap.length)
    (lenEqWindow : window1.length = window2.length)
    (windowNe : window1 ≠ window2) : False := by
  have outerSplit := composePath_splitPackEqOfPrefixLengthEq lcCup
    (composePath window1 rcCup) lcCap (composePath window2 rcCap) coherence lenEqLeftContext
  injection outerSplit with _outerMidEqual outerInner
  injection outerInner with _prefixEqual windowSuffixEqual
  have innerSplit := composePath_splitPackEqOfPrefixLengthEq window1 rcCup window2 rcCap
    windowSuffixEqual lenEqWindow
  injection innerSplit with _innerMidEqual innerInner
  injection innerInner with windowEqual _rcEqual
  exact windowNe windowEqual

/-! ## The orientation-excluded refutation proper -/

/-- ★★ **A shared-boundary cup·cap pair classified `orientationExcludedBothLegs` is IMPOSSIBLE.**  From the shared
window equation `atomFrameTarget cup = atomFrameSource cap` and the equal-width verdict, casing the four cup×cap
generator combos: the two SAME-colour snakes clash on the split MODE (`base ≠ tip`) via `sharedLegModeClash`, and
the two MIXED combos clash on the window LABEL (`F·G ≠ H·G`, `G·H ≠ G·F`) via `stringSameLengthWindowClash`.  This
is the orientation arm the descent oracle dispatches when the widths coincide — vacuously, because at equal widths a
shared-boundary cup·cap cannot exist.  `coh` is fed off `cell`'s own realized chain by the caller. -/
theorem stringOrientationExcluded_vacuous
    {overallSource overallTarget : AdjointTripleMode}
    (cupAtom capAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (isCup : cupAtom.isCupAtom = true) (isCap : capAtom.isCupAtom = false)
    (verdict : classifyAdjacentAtoms cupAtom capAtom = AdjacentCupCapKind.orientationExcludedBothLegs)
    (coh : atomFrameTarget cupAtom = atomFrameSource capAtom) : False := by
  have lenEq : cupAtom.leftContext.length = capAtom.leftContext.length :=
    stringOrientationLeftContextLengthEq cupAtom capAtom verdict
  obtain ⟨cupLeftMid, cupRightMid, lcCup, cupDom, cupCod, genCup, rcCup⟩ := cupAtom
  obtain ⟨capLeftMid, capRightMid, lcCap, capDom, capCod, genCap, rcCap⟩ := capAtom
  dsimp only [atomFrameTarget, atomFrameSource] at coh
  dsimp only at lenEq
  cases genCup with
  | counitLower => nomatch isCup
  | counitUpper => nomatch isCup
  | unitLower =>
      cases genCap with
      | unitLower => nomatch isCap
      | unitUpper => nomatch isCap
      | counitLower =>
          dsimp only [stringFG, stringGF] at coh
          exact sharedLegModeClash lcCup
            (composePath (ModalityPath.cons AdjointTripleModality.left
              (ModalityPath.cons AdjointTripleModality.right
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base))) rcCup)
            lcCap
            (composePath (ModalityPath.cons AdjointTripleModality.right
              (ModalityPath.cons AdjointTripleModality.left
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip))) rcCap)
            coh lenEq (fun modeEqual => AdjointTripleMode.noConfusion modeEqual)
      | counitUpper =>
          dsimp only [stringFG, stringHG] at coh
          exact stringSameLengthWindowClash lcCup stringFG rcCup lcCap stringHG rcCap
            coh lenEq rfl stringFG_ne_stringHG
  | unitUpper =>
      cases genCap with
      | unitLower => nomatch isCap
      | unitUpper => nomatch isCap
      | counitUpper =>
          dsimp only [stringGH, stringHG] at coh
          exact sharedLegModeClash lcCup
            (composePath (ModalityPath.cons AdjointTripleModality.right
              (ModalityPath.cons AdjointTripleModality.coLeft
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip))) rcCup)
            lcCap
            (composePath (ModalityPath.cons AdjointTripleModality.coLeft
              (ModalityPath.cons AdjointTripleModality.right
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base))) rcCap)
            coh lenEq (fun modeEqual => AdjointTripleMode.noConfusion modeEqual)
      | counitLower =>
          dsimp only [stringGH, stringGF] at coh
          exact stringSameLengthWindowClash lcCup stringGH rcCup lcCap stringGF rcCap
            coh lenEq rfl stringGH_ne_stringGF

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the ORIENTATION-EXCLUDED arm is discharged cell-level (FC-3 r7, B3).**
`stringOrientationExcluded_vacuous` proves a shared-boundary cup·cap pair classified `orientationExcludedBothLegs`
(equal left-context widths) cannot exist: the width pin (`stringOrientationLeftContextLengthEq`) plus a four-combo
generator case split, the same-colour combos refuted by the split-MODE clash (`sharedLegModeClash`,
`base ≠ tip`), the mixed combos by the window-LABEL clash (`stringSameLengthWindowClash` +
`stringFG_ne_stringHG` / `stringGH_ne_stringGF`).  Keyed on the shared boundary WORD (no `matchingOf` read),
signature-generic where the classifier is.  This is the third and last of the descent oracle's three verdict arms
to be refuted/produced cell-level.

  What this marker does NOT close (gates stay `false`): it inhabits only the orientation arm; the zigzag-STRAIGHTEN
  band collapse and the oracle wire-up remain, and `fxString_hasAdjointTripleCompleteness` stays `false`.
  `= true`. -/
def fxString_hasOrientationExcludedRefutation : Bool := true

end FX1Poly.Polygraph
