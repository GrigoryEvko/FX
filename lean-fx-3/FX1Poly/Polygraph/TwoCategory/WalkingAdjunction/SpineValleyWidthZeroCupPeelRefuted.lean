import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyWidthZeroCupPeel

/-! # SpineValleyWidthZeroCupPeelRefuted — the width-0 head-cup diagram peel is FALSE (Track B floor)

`SpineValleyWidthZeroCupPeel` isolated `WidthZeroPureCupDeterminacy` to a single residual
`WidthZeroCupHeadDiagramPeel`: peeling a SHARED width-`0` cup head off two pure-cup tails should carry the
width-`0` boundary MATCHING equality of the headed spines to a width-`2` ARC-structure equality of the
tails.  The optimistic reading was that the peel is a positivity-FREE, tractable node (a bounded
Catalan-style tail-chord peel).  **That reading is wrong: the peel is unconditionally FALSE**, and this
file pins the refutation with a machine-checked, kernel-decided witness pair, exactly mirroring the
shipped `not_arcCupHeadCancellationUnconditional`.

## Why it is false — interchange-blindness of the width-`0` matching

The two witness tails are the two REORDERINGS of one disjoint tail cup fired over the head cup's width-`2`
codomain boundary:

  * `widthZeroPeelTailCupAtWindowZero` — a cup fired at window `0` (leg ids `2,3` inserted to the LEFT of
    the head's legs `0,1`);
  * `widthZeroPeelTailCupAtWindowTwo` — the SAME cup fired at window `2` (leg ids `2,3` inserted to the
    RIGHT of the head's legs).

Both are pure cups, both boundary-chained at `2`.  Over the shared width-`0` head cup:

  * the two WIDTH-`0` head matchings are EQUAL (`matchingOfSpineList 0` = `[1,0,3,2]` on both): the width-`0`
    extract has NO bottom ports, so it sees only the two disjoint top cups as an unordered pair of chords —
    it is BLIND to which disjoint cup fired first (Eckmann–Hilton interchange collapses the two orders);
  * the two WIDTH-`2` tail ARC structures DIFFER (their `matchingOfSpineList 2` = `[4,5,3,2,0,1]` vs
    `[2,3,0,1,5,4]`): at width `2` the head's legs `0,1` are BOTTOM through-strands, so the tail matching is
    order-RIGID — it records whether the tail cup sits left or right of the through-strands.

So a route that reduces the pure-cup determinacy to a width-`2` ARC EQUALITY of the tails is unsound: the
width-`0` matching hypothesis is strictly weaker than width-`2` arc equality on the pure-cup class.  (This
is the SAME cup-blindness the shipped `ArcCupCancelObstruction` pins with caps; here it is pinned at the
pure-cup granularity with NO cap — the two disjoint cups are genuinely interchange-equal.)

## Consequence — the corrected route for `WidthZeroPureCupDeterminacy`

`WidthZeroPureCupDeterminacy` itself is NOT refuted (the two witness spines ARE `SpineTraceEquiv` — disjoint
cups commute by interchange), but it CANNOT be obtained through `WidthZeroCupHeadDiagramPeel` /
`pureCupSpine_sort` (which demand ARC equality, false here).  The determinacy must instead go through a
`SpineTraceEquiv`-level interchange argument (reorder disjoint tail cups) — the "through-the-head trace
reselection orbit" foreshadowed in `ArcCupCancelObstruction`.  The reduction
`widthZeroPureCupDeterminacy_of_headDiagramPeel` in the companion file remains a valid theorem but is
VACUOUS (its hypothesis is refuted here); no gate flag is flipped either way.

Raw Lean 4 + Init; the witness equalities/disequalities close by kernel `decide` on the computable
matching / arc folds.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The witness head cup + the two interchange-reordered pure-cup tails -/

/-- The shared width-`0` head cup: the seed `unit` firing `id_base ⇒ (left then right)` with empty whisker
contexts (window `0`, dom arity `0`, cod arity `2`) — the forced head of any width-`0` pure-cup spine
(`cupHeadChainedZero_eq`). -/
def widthZeroPeelHeadCup : SpineAtom adjunctionModeSignature AdjunctionMode.base AdjunctionMode.base :=
  { leftMidMode := AdjunctionMode.base, rightMidMode := AdjunctionMode.base,
    leftContext := identityPath (graph := adjunctionGraph) AdjunctionMode.base,
    generatorDom := ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base,
    generatorCod := adjunctionLeftThenRight,
    generator := AdjunctionTwoCell.unit,
    rightContext := identityPath (graph := adjunctionGraph) AdjunctionMode.base }

/-- The LEFT reordering: a tail cup fired at window `0` over the head's width-`2` codomain (`unit` on the
left, the boundary `L.R` whiskered on the right). -/
def widthZeroPeelTailCupAtWindowZero :=
  RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
    adjunctionLeftThenRight adjunctionUnitTwoCell

/-- The RIGHT reordering: the SAME tail cup fired at window `2` (the boundary `L.R` whiskered on the left,
`unit` on the right) — the interchange-partner of `widthZeroPeelTailCupAtWindowZero`. -/
def widthZeroPeelTailCupAtWindowTwo :=
  RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
    adjunctionLeftThenRight adjunctionUnitTwoCell

/-! ## The witness facts (kernel-decided on the computable folds) -/

/-- ★ **The width-`0` head matchings COLLAPSE.**  Over the shared head cup the two interchange-reordered
tails have EQUAL width-`0` boundary matching — the width-`0` extract has no bottom ports and cannot tell the
two disjoint cups apart. -/
theorem widthZeroPeelHeadMatchingsCollapse :
    matchingOfSpineList 0 (widthZeroPeelHeadCup :: widthZeroPeelTailCupAtWindowZero.spine)
      = matchingOfSpineList 0 (widthZeroPeelHeadCup :: widthZeroPeelTailCupAtWindowTwo.spine) := by
  decide

/-- ★ **The width-`2` tail arc structures SEPARATE.**  At width `2` the head's legs are bottom
through-strands, so the two tails' arc structures DIFFER — the tail matching records whether the tail cup
sits left or right of the through-strands. -/
theorem widthZeroPeelTailArcsSeparate :
    arcStructureOfSpineList 2 widthZeroPeelTailCupAtWindowZero.spine
      ≠ arcStructureOfSpineList 2 widthZeroPeelTailCupAtWindowTwo.spine := by
  decide

/-! ## The refutation -/

/-- ★ **`WidthZeroCupHeadDiagramPeel` is unconditionally FALSE.**  The witness pair meets EVERY hypothesis
of the peel — a shared width-`0` cup head (dom arity `0`, cod arity `2`, empty whisker contexts), two
pure-cup tails boundary-chained at `2`, and EQUAL width-`0` head matchings — yet the concluded width-`2` tail
ARC equality FAILS (`widthZeroPeelTailArcsSeparate`).  So the peel route (reduce the pure-cup determinacy to
a width-`2` arc equality, then `pureCupSpine_sort`) is unsound: the width-`0` matching is interchange-blind
while the width-`2` arc structure is order-rigid. -/
theorem not_widthZeroCupHeadDiagramPeel : ¬ WidthZeroCupHeadDiagramPeel := fun peel =>
  widthZeroPeelTailArcsSeparate
    (peel widthZeroPeelHeadCup widthZeroPeelTailCupAtWindowZero.spine
      widthZeroPeelTailCupAtWindowTwo.spine rfl rfl rfl rfl
      (AllCupArity.cons rfl rfl AllCupArity.nil) (AllCupArity.cons rfl rfl AllCupArity.nil)
      widthZeroPeelTailCupAtWindowZero.spineBoundaryChained_spine
      widthZeroPeelTailCupAtWindowTwo.spineBoundaryChained_spine
      widthZeroPeelHeadMatchingsCollapse)

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the width-`0` head-cup diagram peel is REFUTED (Track B floor).**
`not_widthZeroCupHeadDiagramPeel`: a shared width-`0` cup head over the two interchange-reordered disjoint
tail cups meets every peel hypothesis (pure cups, chained at `2`, equal width-`0` head matchings) yet the
width-`2` tail arc structures differ.  The width-`0` matching is BLIND to the firing order of two disjoint
top cups (Eckmann–Hilton interchange), while the width-`2` arc structure is order-RIGID — so the peel's
target (width-`2` arc EQUALITY of the tails) is strictly stronger than its hypothesis (width-`0` matching
equality) and cannot follow.

  What this marker establishes (and does NOT claim):
  * The peel `WidthZeroCupHeadDiagramPeel` and any width-`2` matching transport sharpening it are FALSE, so
    `widthZeroPureCupDeterminacy_of_headDiagramPeel` (companion file) is a valid but VACUOUS reduction.
  * `WidthZeroPureCupDeterminacy` is NOT thereby refuted — the two witness spines are `SpineTraceEquiv`
    (disjoint cups commute).  The determinacy remains an OPEN (true) residual, reachable only through a
    `SpineTraceEquiv`-level interchange route, NOT through width-`2` arc equality + `pureCupSpine_sort`.
  * `convOfMapEq` and the fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasSpineValleyWidthZeroCupPeelRefuted : Bool := true

end FX1Poly.Polygraph
