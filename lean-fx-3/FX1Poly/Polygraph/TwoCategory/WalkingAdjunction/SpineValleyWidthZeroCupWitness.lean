import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyWidthZeroCupPeelRefuted

/-! # SpineValleyWidthZeroCupWitness — the route-2 mechanism, PROVEN on the refuting pair (Track B)

`SpineValleyWidthZeroCupPeelRefuted` machine-checked that the width-`0` head-cup diagram peel
(`WidthZeroCupHeadDiagramPeel`) is UNCONDITIONALLY FALSE: over a shared width-`0` head cup the two
interchange-reordered disjoint tail cups (`widthZeroPeelTailCupAtWindowZero` at window `0`,
`widthZeroPeelTailCupAtWindowTwo` at window `2`) have EQUAL width-`0` boundary matching yet DIFFERENT
width-`2` tail arc structures.  So `WidthZeroPureCupDeterminacy` cannot be routed through width-`2` arc
equality + `pureCupSpine_sort` (the refuted arc route).

The refutation left a promissory note (`SpineValleyWidthZeroCupPeelRefuted` marker): the determinacy is
NOT thereby false — the two witness spines ARE `SpineTraceEquiv`, reached "only through a
`SpineTraceEquiv`-level interchange route, NOT through width-`2` arc equality".  This file DISCHARGES that
note on the exact refuting pair, positivity-FREE, by a SINGLE Godement / interchange step — validating the
route-2 mechanism end to end:

  * the head cup and the tail cup are two horizontally-INDEPENDENT cups over the empty seed;
  * a single `SpineGodementStep.godement` transposes them (`cellAlpha = id`, `cellAlphaUpper = unit`,
    `cellBeta = unit`, `cellBetaUpper = id`), carrying `head :: tail@window2` to `head :: tail@window0`;
  * CRUCIALLY the step transposes the HEAD cup with the TAIL cup (the head participates in the Godement
    block), NOT a `consCongr` past a shared head — a `consCongr` would leave the single atoms `tail@0`
    versus `tail@2`, which are genuinely distinct and NOT trace-equivalent.  This is exactly the "sort
    ACROSS head" discipline the refutation's cup-blindness forces.

So on the very pair that kills the arc route, the `SpineTraceEquiv`-level interchange route succeeds by one
step.  The two Godement block spines coincide with the two witness spines DEFINITIONALLY (the whisker
accumulators `composePath nil id` / `composePath id LR` reduce on the nose), so the witness is a bare
constructor application.

## What this file does and does NOT claim

  * ★ `widthZeroPeelReorderings_spineTraceEquiv` — the two refuting witness spines are `SpineTraceEquiv`.
    This is `WidthZeroPureCupDeterminacy` PROVEN on its sharpest concrete instance, positivity-free,
    through the interchange route the refutation demanded.

  * It does NOT prove the GENERAL `WidthZeroPureCupDeterminacy` (all width-`0` pure-cup spines with equal
    matching).  The general theorem needs a matching-level (union-find) LOCATE + bubble-to-tail +
    drop-injectivity at width `0` — the analogues of the shipped arc-based `pureCupSpine_lastCup_isShortChord`
    / `locateAux` / `dropLastCup_arc_injective`, all of which are positivity-gated (they route through
    `arcDiagram_eq_matching`, whose `0 < bottomCount` is genuinely needed for the arc↔wire simulation).
    Porting that stack to the plain `WireState`/`processSpine` union-find at width `0` is the standing
    residual; no gate flag is flipped.

Raw Lean 4 + Init; the witness is one `SpineGodementStep` constructor under `SpineTraceEquiv.ofStep` + `symm`,
the block spines matching the witness spines by `rfl`.  Per-declaration `#assert_no_axioms` gated in the audit
twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The route-2 mechanism, PROVEN on the refuting pair.**  The two interchange-reordered disjoint tail
cups over the shared width-`0` head cup — the exact pair whose width-`2` arc structures SEPARATE
(`widthZeroPeelTailArcsSeparate`), refuting the arc route — have `SpineTraceEquiv` spines.  The witness is a
SINGLE Godement / interchange step transposing the head cup with the tail cup: `cellAlpha = id_base`,
`cellAlphaUpper = unit`, `cellBeta = unit`, `cellBetaUpper = id_(L.R)`, empty boundary accumulators.  Its two
block spines are DEFINITIONALLY `widthZeroPeelHeadCup :: widthZeroPeelTailCupAtWindowTwo.spine` and
`widthZeroPeelHeadCup :: widthZeroPeelTailCupAtWindowZero.spine` (the whisker accumulators reduce on the
nose), so the step fires directly and `symm` orients it to the window-`0`→window-`2` direction.  Positivity
is never invoked; the head cup PARTICIPATES in the transposition (no `consCongr` past a shared head). -/
theorem widthZeroPeelReorderings_spineTraceEquiv :
    SpineTraceEquiv adjunctionModeSignature
      (widthZeroPeelHeadCup :: widthZeroPeelTailCupAtWindowZero.spine)
      (widthZeroPeelHeadCup :: widthZeroPeelTailCupAtWindowTwo.spine) := by
  -- The single Godement / interchange step transposing the head cup with the tail cup.
  -- Elaborated WITHOUT the expected type driving unification, so every implicit boundary
  -- 1-cell is solved from the explicit blocks' types; the two block spines then reduce
  -- DEFINITIONALLY to the two witness spines (whisker accumulators `composePath _ id` reduce).
  have transposeStep :=
    SpineGodementStep.godement
      (@RawTwoCellExpr.id adjunctionModeSignature AdjunctionMode.base AdjunctionMode.base
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base))
      adjunctionUnitTwoCell
      adjunctionUnitTwoCell
      (@RawTwoCellExpr.id adjunctionModeSignature AdjunctionMode.base AdjunctionMode.base
        adjunctionLeftThenRight)
      (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
      (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
      ([] : List (SpineAtom adjunctionModeSignature AdjunctionMode.base AdjunctionMode.base))
  exact SpineTraceEquiv.symm (SpineTraceEquiv.ofStep transposeStep)

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the route-2 interchange mechanism is PROVEN on the refuting pair.**
`widthZeroPeelReorderings_spineTraceEquiv` shows the two interchange-reordered disjoint tail cups over the
shared width-`0` head cup are `SpineTraceEquiv`, via a SINGLE Godement step transposing the head cup with the
tail cup — positivity-free, discharging the promissory note the refutation `not_widthZeroCupHeadDiagramPeel`
left open (the determinacy is reached through the `SpineTraceEquiv`-level interchange route, never through the
refuted width-`2` arc equality).

  What this marker does NOT claim (the gate stays `false`):
  * The GENERAL `WidthZeroPureCupDeterminacy` — all width-`0` pure-cup spines with equal `matchingOfSpineList 0`
    are `SpineTraceEquiv`.  The general case needs a matching-level (union-find) LOCATE + bubble-to-tail +
    drop-injectivity at width `0`: the analogues of the shipped arc-based `pureCupSpine_lastCup_isShortChord`,
    `locateAux`, and `dropLastCup_arc_injective`, all positivity-gated through `arcDiagram_eq_matching`.
    Those union-find invariants (forest / freshness / short-chord readoff) are shipped only for the ARC state
    `ArcWireState`/`processArcSpine`, not for the plain `WireState`/`processSpine` this route requires — the
    standing port.

So this file validates the mechanism (a single head↔tail interchange discharges the sharpest instance) and
isolates the general residual to the plain-`WireState` union-find port.  `convOfMapEq` and the fib-3 gate flags
stay `false`.  `= true`. -/
def fxMode_hasSpineValleyWidthZeroCupWitness : Bool := true

end FX1Poly.Polygraph
