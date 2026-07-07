import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRangeInterleave

/-! # MatchingCupWindowScanSplit — the single-cup partner-scan window split (assembled)

The CUP mirror of the cap-window interleave, ASSEMBLED into one scan equation.  A cup fired at
boundary window `windowPosition` splices two fresh legs at that position, so the whole (composite)
boundary carries two extra candidates `windowPosition` and `windowPosition + 1` sitting between the
below-window candidates and the shifted tail images.  The generic interleave kit
(`MatchingRangeInterleave`) already supplies the three raw pieces:

  * `rangeInterleaveAtWindow` — the composite candidate range `List.range ((windowPosition + 2) +
    tailCount)` splits as `(below ++ [leg, leg+1]) ++ shiftedTail`;
  * `findPartnerScan_dropMiddle_ofAllFail` — a scan sails through an all-failing middle segment;
  * `rangeShiftImageAtWindow` — the two-zone index shift maps the fresh range `List.range
    (windowPosition + tailCount)` onto exactly `below ++ shiftedTail`;
  * `findPartnerScan_mapCongr` — a scan over a shifted candidate list is the shift of the base scan
    under a per-candidate whole-test correspondence.

This file threads the four together into ONE lemma: given that the two fresh-leg candidates FAIL the
survivor's exclude-and-root test (`windowPairFails`) and that every fresh candidate's whole test
corresponds to its composite image's test (`testCorr`), the composite partner scan over the whole
range returns the index shift of the fresh (mid-state) partner scan.  That is exactly the
"survivor's partner scan returns `shiftPastPosition` of the mid-state scan result" leg the
`MatchingPartnerScanSplit` / `MatchingRangeInterleave` honesty markers flag as un-assembled — at the
scan level, modulo the two genuinely-semantic hypotheses (the fresh-leg misses and the folded-state
root correspondence, which are the standing valley-descent residual #2185).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The single-cup partner-scan window split, assembled.**  When a cup splices two fresh legs at
boundary window `windowPosition` (so the composite total is the fresh total plus two, with the two
extra candidates `windowPosition`, `windowPosition + 1` at the window), the composite partner scan
over `List.range ((windowPosition + 2) + tailCount)` equals the index shift of the fresh partner scan
over `List.range (windowPosition + tailCount)` — PROVIDED:

  * the index shift is the two-zone splice map (`fixesBelowWindow` / `shiftsPastWindow` — identity
    below the window, plus-two at or beyond it);
  * the two fresh-leg candidates FAIL the composite exclude-and-root test (`windowPairFails`); and
  * every fresh candidate's composite-image whole test equals its fresh whole test (`testCorr`).

Proof: `rangeInterleaveAtWindow` splits the composite range around the window pair;
`findPartnerScan_dropMiddle_ofAllFail` drops the all-failing pair; `rangeShiftImageAtWindow`
identifies the surviving candidates with the shifted fresh range; `findPartnerScan_mapCongr` pulls
the shift out.  The two provisos are the un-discharged semantic content (#2185). -/
theorem findPartnerScan_range_cupWindowSplit
    (compositeLinks freshLinks : List (Nat × Nat))
    (compositeBoundary freshBoundary : List Nat)
    (compositeRoot freshRoot freshExclude : Nat) (indexShift : Nat → Nat)
    (windowPosition tailCount : Nat)
    (fixesBelowWindow : ∀ index, index < windowPosition → indexShift index = index)
    (shiftsPastWindow : ∀ index, windowPosition ≤ index → indexShift index = index + 2)
    (windowPairFails : ∀ leg, leg ∈ [windowPosition, windowPosition + 1] →
      (leg != indexShift freshExclude
          && unionFindRootOf compositeLinks (natListGetAt compositeBoundary leg) == compositeRoot)
        = false)
    (testCorr : ∀ candidate, candidate ∈ List.range (windowPosition + tailCount) →
      (indexShift candidate != indexShift freshExclude
          && unionFindRootOf compositeLinks
              (natListGetAt compositeBoundary (indexShift candidate)) == compositeRoot)
        = (candidate != freshExclude
            && unionFindRootOf freshLinks (natListGetAt freshBoundary candidate) == freshRoot)) :
    findPartnerScan compositeLinks compositeBoundary compositeRoot (indexShift freshExclude)
        (List.range ((windowPosition + 2) + tailCount))
      = indexShift
        (findPartnerScan freshLinks freshBoundary freshRoot freshExclude
          (List.range (windowPosition + tailCount))) := by
  rw [rangeInterleaveAtWindow windowPosition tailCount,
    findPartnerScan_dropMiddle_ofAllFail compositeLinks compositeBoundary compositeRoot
      (indexShift freshExclude) (List.range windowPosition) [windowPosition, windowPosition + 1]
      ((List.range tailCount).map (fun offset => (windowPosition + 2) + offset)) windowPairFails,
    ← rangeShiftImageAtWindow indexShift windowPosition tailCount fixesBelowWindow shiftsPastWindow]
  exact findPartnerScan_mapCongr compositeLinks freshLinks compositeBoundary freshBoundary
    compositeRoot freshRoot freshExclude indexShift (List.range (windowPosition + tailCount)) testCorr

/-! ## Honesty marker -/

/-- **Honesty marker — the single-cup partner-scan window split is ASSEMBLED (scan level).**
`findPartnerScan_range_cupWindowSplit` threads the four generic interleave pieces
(`rangeInterleaveAtWindow`, `findPartnerScan_dropMiddle_ofAllFail`, `rangeShiftImageAtWindow`,
`findPartnerScan_mapCongr`) into one equation: the composite (whole-valley) partner scan is the index
shift of the fresh (mid-state) partner scan.  This discharges the "assembled … partner leg" the
`MatchingRangeInterleave` and `MatchingPartnerScanSplit` markers flag as unclaimed — for the CUP case,
at the scan level.  What this marker does NOT claim: the two remaining hypotheses discharged at the
FOLDED cup state — `windowPairFails` (the two fresh legs actually miss the survivor's component
through the whole cup fold) and `testCorr` (the composite/fresh root correspondence at every folded
state).  Those are the standing "mid-state rigidity / index-shift bijection" residual (the
valley-descent beam #2185); nor the multi-cup block fold (composing the per-cup shifts and threading
the two provisos through each cup).  No gate flag is flipped.  `= true`. -/
def fxMode_hasCupWindowScanSplit : Bool := true

end FX1Poly.Polygraph
