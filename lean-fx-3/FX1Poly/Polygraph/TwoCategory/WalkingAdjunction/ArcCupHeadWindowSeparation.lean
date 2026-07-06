import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineTraceDecision
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCancelObstruction

/-! # ArcCupHeadWindowSeparation — the head-cup window lives in `internalCupCounts`, not the boundary matching

The cup-head discharge (`ArcCupReselectionOrbit`, `ArcCupCaseOrbitReduction`) still owes `windowPin` —
`movedTarget.leftContext.length = headAtom.leftContext.length`, the re-selected cup landing at the head's
window.  ANGLE B asks the prior question: is the head cup's window even RECOVERABLE from the arc structure,
or is it genuinely lost?  If it is a function of the `FullArcStructure`, `windowPin` is a readoff; if lost,
`windowPin` must be produced by the planar re-selection.

This brick pins the answer WITH A MACHINE-CHECKED WITNESS — and it is the sharp answer: the head window is
NOT lost, but it is INVISIBLE to the boundary matching and VISIBLE only in `internalCupCounts`.

The witness is two boundary-chained, cup-headed spines over the bottom boundary `L·R` (length `2`):

  * `spineHeadWindowZero` = (cup at window `0`) then the connecting cap at window `1` — the head cup seats
    its legs at the FRONT (`whiskerRight`);
  * `spineHeadWindowTwo`  = (cup at window `2`) then the same connecting cap at window `1` — the head cup
    seats its legs at the BACK (`whiskerLeft`).

Both fire the cup at `base`-parity, so both are mode-realizable, and both are `SpineBoundaryChained 2`.  Their
head cups differ ONLY in window (`0` vs `2`, `atomReadoff`).  And the two arc structures:

  * agree on the ENTIRE boundary `DiagramType` — same port counts, same partner matching `[2,3,0,1]`, same
    loop count (`boundaryDiagram_isWindowBlind`);
  * agree on the cup/cap TOTALS (`cupCapTotals_areWindowBlind`);
  * DIFFER exactly in `internalCupCounts` (`[1,0,1,0]` vs `[0,1,0,1]`) and `internalCapCounts`
    (`internalCupCounts_separateHeadWindow` / `internalCapCounts_separateHeadWindow`).

So the boundary matching (the `matchingOf` shadow, `diagram.partner`) is BLIND to the head-cup window, while
`internalCupCounts` — the per-strand turnback census that survives arc-equality — SEPARATES the two windows.
The head cup at window `0` lands its turnback on the strand of the even boundary ports (`[1,0,1,0]`); at window
`2` on the odd ports (`[0,1,0,1]`).  The window is a function of `internalCupCounts`, not of the partner.

## What this settles for the cup-head crux

`windowPin` is NOT blocked by window-loss: the head window is recoverable from `internalCupCounts` (the field
`arcStructureOf`-equality preserves).  The residual that DOES block the cup case is `tailsCancel`
(`ArcCupCancelObstruction` — the composite forgets which LEG a tail cup attached to), a DIFFERENT quantity.
This is exactly parallel to `arcCupObstructionPinsRefuted`: it removes a candidate route (reading the window
off the boundary matching is DEAD — the partner is window-blind here) and points at the surviving one
(`internalCupCounts`).  The general readoff (window as a total function of `internalCupCounts` over EVERY
chained cup-headed spine) is the reconstruction residual — not shipped here; this brick ships the concrete
separation and the negative half (partner is not enough).

Raw Lean 4 + Init; the arc equalities/disequalities close by kernel `decide` on the computable arc fold; the
chains by `spineBoundaryChained_spine`; the atom readoffs by `rfl`.  Per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The witness cells -/

/-- The head cup at window `0` over the bottom boundary `L·R` (length `2`): `whiskerRight L·R unit` seats the
unit's two legs at the FRONT, leaving `L·R·L·R`. -/
def cupHeadAtWindowZero :
    RawTwoCellExpr adjunctionModeSignature
      (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
        adjunctionLeftThenRight)
      (composePath adjunctionLeftThenRight adjunctionLeftThenRight) :=
  RawTwoCellExpr.whiskerRight adjunctionLeftThenRight adjunctionUnitTwoCell

/-- The head cup at window `2` over the bottom boundary `L·R` (length `2`): `whiskerLeft L·R unit` seats the
unit's two legs at the BACK, leaving `L·R·L·R`. -/
def cupHeadAtWindowTwo :
    RawTwoCellExpr adjunctionModeSignature
      (composePath adjunctionLeftThenRight
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base))
      (composePath adjunctionLeftThenRight adjunctionLeftThenRight) :=
  RawTwoCellExpr.whiskerLeft adjunctionLeftThenRight adjunctionUnitTwoCell

/-- The connecting cap at window `1` over `L·R·L·R`: `whiskerLeft L (whiskerRight R counit)` consumes the
`R·L` at positions `1,2`, leaving `L·R`.  The SAME cap closes both head cups' end states. -/
def connectingCapAtWindowOne :=
  RawTwoCellExpr.whiskerLeft
    (singletonModalityPath (graph := adjunctionGraph) AdjunctionModality.left)
    (RawTwoCellExpr.whiskerRight
      (singletonModalityPath (graph := adjunctionGraph) AdjunctionModality.right)
      adjunctionCounitTwoCell)

/-- The window-`0`-headed witness spine: cup at window `0`, then the connecting cap at window `1`. -/
def spineHeadWindowZero := RawTwoCellExpr.vcomp cupHeadAtWindowZero connectingCapAtWindowOne

/-- The window-`2`-headed witness spine: cup at window `2`, then the SAME connecting cap at window `1`. -/
def spineHeadWindowTwo := RawTwoCellExpr.vcomp cupHeadAtWindowTwo connectingCapAtWindowOne

/-! ## Both witnesses are boundary-chained, cup-headed, and differ ONLY in the head window -/

/-- The window-`0` witness is boundary-chained at `2` (it is the spine of a well-typed cell). -/
theorem spineHeadWindowZero_isChained :
    SpineBoundaryChained 2 spineHeadWindowZero.spine :=
  spineHeadWindowZero.spineBoundaryChained_spine

/-- The window-`2` witness is boundary-chained at `2`. -/
theorem spineHeadWindowTwo_isChained :
    SpineBoundaryChained 2 spineHeadWindowTwo.spine :=
  spineHeadWindowTwo.spineBoundaryChained_spine

/-- The window-`0` witness's atoms, as `(window, dom arity, cod arity)`: a cup `(0, 2)` at window `0`, then
the cap `(2, 0)` at window `1`.  Its HEAD is a cup at window `0`. -/
theorem spineHeadWindowZero_atomReadoff :
    spineHeadWindowZero.spine.map
      (fun atom => (atom.leftContext.length, atom.generatorDom.length, atom.generatorCod.length))
      = [(0, 0, 2), (1, 2, 0)] := rfl

/-- The window-`2` witness's atoms: a cup `(0, 2)` at window `2`, then the cap `(2, 0)` at window `1`.  Its
HEAD is a cup at window `2` — differing from `spineHeadWindowZero`'s head ONLY in the window. -/
theorem spineHeadWindowTwo_atomReadoff :
    spineHeadWindowTwo.spine.map
      (fun atom => (atom.leftContext.length, atom.generatorDom.length, atom.generatorCod.length))
      = [(2, 0, 2), (1, 2, 0)] := rfl

/-! ## The boundary matching is BLIND to the head window; `internalCupCounts` RECOVERS it -/

set_option maxHeartbeats 1600000 in
/-- ★ **The boundary `DiagramType` is blind to the head-cup window.**  The two witnesses — head cups at
windows `0` and `2` — share the ENTIRE boundary type: same port counts, same partner matching `[2,3,0,1]`,
same loop count.  So the `matchingOf` shadow (the partner) cannot recover the window. -/
theorem boundaryDiagram_isWindowBlind :
    (arcStructureOf spineHeadWindowZero).diagram = (arcStructureOf spineHeadWindowTwo).diagram := by
  decide +kernel

set_option maxHeartbeats 1600000 in
/-- ★ The cup/cap TOTALS are blind to the head-cup window too (one cup, one cap on each side). -/
theorem cupCapTotals_areWindowBlind :
    (arcStructureOf spineHeadWindowZero).cupCount = (arcStructureOf spineHeadWindowTwo).cupCount
      ∧ (arcStructureOf spineHeadWindowZero).capCount = (arcStructureOf spineHeadWindowTwo).capCount := by
  decide +kernel

set_option maxHeartbeats 1600000 in
/-- ★ **`internalCupCounts` SEPARATES the head windows** the boundary matching could not: window `0` seats
the head cup's turnback on the even boundary ports (`[1,0,1,0]`), window `2` on the odd ports (`[0,1,0,1]`).
This is the field that carries the window through arc-equality. -/
theorem internalCupCounts_separateHeadWindow :
    (arcStructureOf spineHeadWindowZero).internalCupCounts
      ≠ (arcStructureOf spineHeadWindowTwo).internalCupCounts := by decide +kernel

set_option maxHeartbeats 1600000 in
/-- ★ `internalCapCounts` separates the two head windows as well (the connecting cap rides the same
window-selected strand): `[1,0,1,0]` vs `[0,1,0,1]`. -/
theorem internalCapCounts_separateHeadWindow :
    (arcStructureOf spineHeadWindowZero).internalCapCounts
      ≠ (arcStructureOf spineHeadWindowTwo).internalCapCounts := by decide +kernel

/-- ★ **The two arc structures differ — and the difference is the head window.**  Same boundary matching,
same totals, but distinct `internalCupCounts`.  Hence a full `arcStructureOf`-equality would force the head
windows to agree: the head-cup window IS recoverable from `arcStructureOf` (it is NOT genuinely lost). -/
theorem arcStructures_differ_byHeadWindow :
    arcStructureOf spineHeadWindowZero ≠ arcStructureOf spineHeadWindowTwo := by
  intro structuresEqual
  exact internalCupCounts_separateHeadWindow
    (congrArg FullArcStructure.internalCupCounts structuresEqual)

/-! ## Honesty marker -/

/-- **Honesty marker — the head-cup window lives in `internalCupCounts`, not the boundary matching.**  Two
boundary-chained, cup-headed spines whose head cups differ ONLY in window (`0` vs `2`,
`spineHeadWindowZero_atomReadoff` / `spineHeadWindowTwo_atomReadoff`) share the whole boundary `DiagramType`
(`boundaryDiagram_isWindowBlind`, partner `[2,3,0,1]`) and the cup/cap totals
(`cupCapTotals_areWindowBlind`), yet are separated by `internalCupCounts`
(`internalCupCounts_separateHeadWindow`, `[1,0,1,0]` vs `[0,1,0,1]`) — so `arcStructureOf` distinguishes them
(`arcStructures_differ_byHeadWindow`).  What this SETTLES for the cup-head crux (ANGLE B): the head window is
NOT genuinely lost — it is a function of `internalCupCounts` (the field arc-equality preserves), and the
boundary matching alone (`diagram.partner`) is provably INSUFFICIENT to recover it.  The residual that blocks
the cup case is therefore `tailsCancel` (`ArcCupCancelObstruction` — the composite forgets the leg the tail
attached to), a different quantity, NOT window-loss.  What this marker does NOT claim: the general readoff
(the head window as a total function of `internalCupCounts` over every chained cup-headed spine — the
reconstruction residual) nor `windowPin` itself.  `= true`. -/
def fxMode_hasArcCupHeadWindowSeparation : Bool := true

end FX1Poly.Polygraph
