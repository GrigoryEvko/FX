import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescWellFormedFoldWidth

/-! # BRAUER r25 GAP γ (witness) — `throughStrandPerm` is a RANGE-PERMUTATION + the corrected `middle` decode

The corrected extractor's `middle` block is `permutationToCrossingWord throughBottoms.length (throughStrandPerm …)`.
Decoding it (the THROUGH chain's `middle`-phase seam) is the shipped conjugator roundtrip
`permuteOfCrossingWord_permutationToCrossingWord`, gated by `IsPermutationOfRange (throughStrandBottoms …).length
(throughStrandPerm …)`.  This file BUNDLES that gate from its three fields — two of which are the r25 GAP γ content
proved on the count machinery (`throughStrandPerm_length_eq_throughStrandBottoms`, `throughStrandPerm_isDistinct`,
`WiringDescArcReadOffCount`), the third the shipped bound (`throughStrandPerm_isBounded`,
`WiringDescWellFormedFoldWidth`) — and reads the middle decode off it (`correctedMiddle_decodesReadOff`).

This is GAP γ's IsPermutationOfRange witness: the ledger implied the whole roundtrip was unbuilt, but only the
`isDistinct` field was genuine new content (crux = `arcMiddleCountBelow` strict-monotone-on-members ⟹ rank injective);
`hasWidthLength` fell out of the r17 through-count symmetry and `isBounded` was already shipped.  It flips NO master —
the THROUGH per-arc 5-phase node-identity assembly (the heavy part) stays r26.

Raw Lean 4 + Init, STRUCTURAL, propext-free; `decide` only on the closed 3-through witness. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The IsPermutationOfRange bundle -/

/-- ★★★ **GAP γ — `throughStrandPerm` is an `IsPermutationOfRange`.**  For every well-formed boundary involution, the
TOP-indexed through permutation `throughStrandPerm` is a genuine range-permutation of width `#throughStrandBottoms`:
DISTINCT (`throughStrandPerm_isDistinct` — rank injectivity), of the right LENGTH
(`throughStrandPerm_length_eq_throughStrandBottoms` — the through-count symmetry), and BOUNDED
(`throughStrandPerm_isBounded`, shipped).  This is the exact gate the shipped conjugator roundtrip consumes. -/
theorem throughStrandPerm_isPermutationOfRange (bottomCount topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (bottomCount + topCount) partner) :
    IsPermutationOfRange (throughStrandBottoms bottomCount partner).length
      (throughStrandPerm bottomCount topCount partner) where
  hasWidthLength := throughStrandPerm_length_eq_throughStrandBottoms bottomCount topCount partner wf
  isDistinct := throughStrandPerm_isDistinct bottomCount topCount partner wf
  isBounded := throughStrandPerm_isBounded bottomCount topCount partner wf

/-! ## The corrected `middle` decode -/

/-- ★★ **The corrected extractor's `middle` block decodes to `throughStrandPerm`.**  Its `middle` staircase is
`permutationToCrossingWord throughBottoms.length (throughStrandPerm …)`, so `permuteOfCrossingWord throughBottoms.length`
inverts it — via the shipped roundtrip fed the r25 GAP γ `IsPermutationOfRange` witness.  This is the THROUGH chain's
`middle`-phase decode seam (the analog of `correctedBottomPerm_decodesReadOff` for the through block). -/
theorem correctedMiddle_decodesReadOff (d : DiagramType)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner) :
    permuteOfCrossingWord (throughStrandBottoms d.bottomCount d.partner).length
        (reconstructStandardFormExt5Corrected d).middle
      = throughStrandPerm d.bottomCount d.topCount d.partner := by
  show permuteOfCrossingWord (throughStrandBottoms d.bottomCount d.partner).length
      (permutationToCrossingWord (throughStrandBottoms d.bottomCount d.partner).length
        (throughStrandPerm d.bottomCount d.topCount d.partner))
    = throughStrandPerm d.bottomCount d.topCount d.partner
  exact permuteOfCrossingWord_permutationToCrossingWord (throughStrandBottoms d.bottomCount d.partner).length
    (throughStrandPerm d.bottomCount d.topCount d.partner)
    (throughStrandPerm_isPermutationOfRange d.bottomCount d.topCount d.partner wf)

/-! ## The concrete firing — three through strands mutually crossing (a genuine 3-cycle) -/

/-- Three through strands with a CYCLIC crossing (`0→top1`, `1→top2`, `2→top0`): partner `[4,5,3,2,0,1]`, an
involution on `3 + 3` boundary ports whose `throughStrandPerm` is the genuine 3-cycle `[2, 0, 1]` — GAP γ's
non-trivial `isDistinct` witness. -/
def threeThroughCrossingDiagram : DiagramType :=
  { bottomCount := 3, topCount := 3, partner := [4, 5, 3, 2, 0, 1], loops := 0 }

/-- The 3-through crossing diagram is a boundary involution (each field `decide`-checked). -/
theorem isBoundaryInvolution_threeThroughCrossing :
    IsBoundaryInvolution (threeThroughCrossingDiagram.bottomCount + threeThroughCrossingDiagram.topCount)
      threeThroughCrossingDiagram.partner where
  hasBoundaryLength := rfl
  mapsInRange := by decide
  isSelfInverse := by decide
  isFixedPointFree := by decide

/-- ★★ **GAP γ FIRES — the 3-cycle `throughStrandPerm` is a range-permutation.**  Instantiating
`throughStrandPerm_isPermutationOfRange` on the mutually-crossing 3-through witness: `[2, 0, 1]` is distinct, length 3,
bounded — the genuine multi-through content, exercised (not `decide`d). -/
theorem throughStrandPerm_isPermutationOfRange_fires3Through :
    IsPermutationOfRange (throughStrandBottoms threeThroughCrossingDiagram.bottomCount
        threeThroughCrossingDiagram.partner).length
      (throughStrandPerm threeThroughCrossingDiagram.bottomCount threeThroughCrossingDiagram.topCount
        threeThroughCrossingDiagram.partner) :=
  throughStrandPerm_isPermutationOfRange threeThroughCrossingDiagram.bottomCount
    threeThroughCrossingDiagram.topCount threeThroughCrossingDiagram.partner
    isBoundaryInvolution_threeThroughCrossing

/-- ★★ **The middle decode FIRES on the 3-through witness.**  The corrected `middle` block of the mutually-crossing
3-through diagram decodes to its `throughStrandPerm = [2, 0, 1]` — the general decode, exercised on a genuine 3-cycle. -/
theorem correctedMiddle_decodesReadOff_fires3Through :
    permuteOfCrossingWord (throughStrandBottoms threeThroughCrossingDiagram.bottomCount
        threeThroughCrossingDiagram.partner).length
        (reconstructStandardFormExt5Corrected threeThroughCrossingDiagram).middle
      = throughStrandPerm threeThroughCrossingDiagram.bottomCount threeThroughCrossingDiagram.topCount
          threeThroughCrossingDiagram.partner :=
  correctedMiddle_decodesReadOff threeThroughCrossingDiagram isBoundaryInvolution_threeThroughCrossing

/-! ## Honesty marker -/

/-- ★★ **Honesty marker — GAP γ `throughStrandPerm` range-permutation witness SHIPPED (r25).**  The middle
through-strand permutation is a genuine `IsPermutationOfRange` for every well-formed involution
(`throughStrandPerm_isPermutationOfRange`), so the corrected `middle` block decodes to it
(`correctedMiddle_decodesReadOff`) via the shipped roundtrip.  A NEW ingredient marker; it flips NO master — the
THROUGH per-arc 5-phase node-identity assembly + the all-class classifier stay r26.  `= true`. -/
def fxBrauer_hasThroughStrandPermPerm : Bool := true

end FX1Poly.Polygraph
