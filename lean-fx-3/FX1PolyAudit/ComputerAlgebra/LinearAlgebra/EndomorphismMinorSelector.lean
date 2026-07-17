import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.EndomorphismMinorSelector

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/EndomorphismMinorSelector — zero-axiom gate

Per-declaration zero-axiom gate for the WP-ENDO r2 general `k×k` minor selector (the `minorRankGeneral`
wall): the function-valued submatrix selector, the general minor determinant, the three `2`-index
selections of `{0,1,2}`, the dimension-`3` rank via the nine `2×2` minors, the rank-`3` dissimilarity
predicate, the per-rank groundings (`0` through `3` on a `3×3`), the rank-`2`-versus-rank-`1`
separation certificate, and the marker.

The selector is deliberately function-valued (`Nat → Nat` index selection) rather than list-valued:
`List.getD` pulls `propext` into the substrate, so the whole minor engine — and every rank grounding —
would inherit it.  The function-valued form keeps the entire file free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The general minor selector (function-valued index selection).
#assert_no_axioms FX1Poly.ComputerAlgebra.selectSubmatrix
#assert_no_axioms FX1Poly.ComputerAlgebra.intMinorDet

-- The three `2`-index selections of `{0,1,2}`.
#assert_no_axioms FX1Poly.ComputerAlgebra.selectPairLow
#assert_no_axioms FX1Poly.ComputerAlgebra.selectPairOuter
#assert_no_axioms FX1Poly.ComputerAlgebra.selectPairHigh

-- The general-minor groundings on a `3×3`.
#assert_no_axioms FX1Poly.ComputerAlgebra.intMinorDetTopLeftTwoOfThreeExample
#assert_no_axioms FX1Poly.ComputerAlgebra.intMinorDetOuterTwoOfThreeExample

-- The dimension-`3` rank via the nine `2×2` minors + its dissimilarity predicate.
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismRank3
#assert_no_axioms FX1Poly.ComputerAlgebra.EndomorphismDissimilarByRank3

-- The per-rank groundings (`0` through `3`) + the rank-`2`-versus-rank-`1` separator.
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismRank3ZeroExample
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismRank3OneExample
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismRank3TwoExample
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismRank3ThreeExample
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismRank3SeparatesRankTwoFromRankOne

-- The marker.
#assert_no_axioms FX1Poly.ComputerAlgebra.fxEndo_hasGeneralMinorSelector

end FX1PolyAudit
