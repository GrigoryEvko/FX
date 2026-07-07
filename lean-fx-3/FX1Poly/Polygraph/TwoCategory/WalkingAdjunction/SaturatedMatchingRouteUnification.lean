import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedSpineTraceLift

/-! # mode-3 keystone — the two completeness routes UNIFIED onto the single canonical residual

Two independent reductions of the fib-3 keystone's sole remaining residual (the completeness field
`convOfMapEq` of `SaturatedMatchingCanonicalization`; soundness is CLOSED via the boundary discipline) are
already shipped, each producing the WHOLE `SaturatedMatchingCanonicalization` from its own residual:

  * the **canonical-cell** route (`SaturatedMatchingStaircaseReduction`): a
    `CanonicalMatchingStaircaseData` — a matching-only canonical cell per cell (`canonicalCellOf` +
    `canonRespectsMatching`) plus the per-cell reconstruction `reconstructs`
    (`MatchingStaircaseReconstructs`);
  * the **existence** route (`SaturatedSpineTraceLift`): a `MatchingReductsShareSpineTrace` — matching-equal
    cells have saturated reducts whose spines are trace-equivalent (no canonical choice made).

This file relates the two: the canonical-cell residual IMPLIES the existence residual, so closing
`MatchingStaircaseReconstructs` closes BOTH routes at once, and the existence residual is a genuine
weakening of the canonical one.

  * ★ `matchingReductsShareSpineTrace_ofMatchingStaircase` — a `CanonicalMatchingStaircaseData` yields
    `MatchingReductsShareSpineTrace`: take each cell's own canonical staircase as its reduct.  The two
    reducts are LITERALLY EQUAL (their source cells share a boundary matching, and `canonicalCellOf`
    depends only on that matching — `canonRespectsMatching`), so their spines are equal and the required
    `SpineTraceEquiv` is `refl`; each reduct is saturated-convertible to its source by `reconstructs`.

The asymmetry is genuine and informative: the canonical route hands back a matching-determined FUNCTION
(a normal form), from which the existence witnesses are read off trivially; the existence route asserts
only that SOME trace-equivalent-spined reducts exist and carries no canonical choice, so it cannot recover
a `canonicalCellOf`.  Hence `MatchingStaircaseReconstructs` is the STRONGER of the two open residuals — the
single obligation whose discharge closes the entire fib-3 keystone by either capstone.

Raw Lean 4 + Init; the reduction is a five-tuple with `refl`/`reconstructs` fields and one
`canonRespectsMatching`-driven spine rewrite.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The canonical-cell residual implies the existence residual.**  A `CanonicalMatchingStaircaseData`
(the canonical-staircase route's residual) yields a `MatchingReductsShareSpineTrace` (the existence
route's): for matching-equal `cellA`, `cellB`, take each cell's own canonical staircase as its reduct.
`data.reconstructs` gives the two source-to-reduct saturated convertibilities; and because the two source
cells have equal boundary matchings and `data.canonicalCellOf` depends ONLY on the matching
(`data.canonRespectsMatching`), the two reducts are EQUAL, so their spines are equal and the demanded
`SpineTraceEquiv` between reduct spines is reflexivity.

So closing `MatchingStaircaseReconstructs` closes BOTH shipped keystone routes at once, and the existence
residual `MatchingReductsShareSpineTrace` is a genuine weakening of the canonical-cell residual: the
canonical route hands back a matching-determined normal form from which the existence witnesses are read
off trivially, whereas the existence route makes no canonical choice.  `MatchingStaircaseReconstructs` is
therefore the stronger — the single obligation whose discharge closes the entire fib-3 keystone. -/
theorem matchingReductsShareSpineTrace_ofMatchingStaircase
    (data : CanonicalMatchingStaircaseData) : MatchingReductsShareSpineTrace := by
  intro sourceMode targetMode sourcePath targetPath cellA cellB matchingsEqual
  refine ⟨data.canonicalCellOf cellA, data.canonicalCellOf cellB,
    data.reconstructs cellA, data.reconstructs cellB, ?_⟩
  have canonicalCellsEqual : data.canonicalCellOf cellA = data.canonicalCellOf cellB :=
    data.canonRespectsMatching cellA cellB matchingsEqual
  rw [canonicalCellsEqual]
  exact SpineTraceEquiv.refl _

/-! ## Honesty marker -/

/-- **Honesty marker — the two keystone routes are UNIFIED; the canonical residual is the stronger.**
`matchingReductsShareSpineTrace_ofMatchingStaircase` derives the existence residual
`MatchingReductsShareSpineTrace` from the canonical-cell residual `CanonicalMatchingStaircaseData`, so
`MatchingStaircaseReconstructs` — the reconstruction field of the canonical data, given any matching-only
`canonicalCellOf` — is a SINGLE obligation whose discharge closes the entire fib-3 keystone via EITHER
capstone (`saturatedMatchingCanonicalization_ofMatchingStaircase` directly, or
`saturatedMatchingCanonicalization_ofMatchingReductsShareSpineTrace` through this reduction).  What this
marker does NOT claim: an inhabitant of either residual — both remain the genuine open Joyal–Street /
Schanuel–Street reconstruction (`fxMode_hasArcCellReconstruction = false`), the same combinatorial
normalization core the arc campaign targets.  What it DOES establish: the two shipped routes are not
independent — the canonical route dominates, so the reconstruction effort has one target, not two.
`= true`. -/
def fxMode_hasMatchingKeystoneRoutesUnified : Bool := true

end FX1Poly.Polygraph
