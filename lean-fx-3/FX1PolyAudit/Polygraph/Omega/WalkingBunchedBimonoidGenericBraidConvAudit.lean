import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidGenericBraidConv

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidGenericBraidConvAudit — zero-axiom gate for the
generic-width adjacent-braid CONV atom, DERIVED term-mode from the axiomatic width-3 Yang-Baxter hexagon row
(WP-PROP r24, THE BRAID DECISION, branch (a)).

Per-declaration `#assert_no_axioms` on the common-pad core letters, the snoc reshape, the per-letter reshapes,
the triple collapse, the Yang-Baxter atom, the core braid, the `sigmaAt`-connection legs, the two triple
reshapes, the headline generic braid, the width-3 matrix pin, and the delivery marker — PLUS an independent
(non-fuel) `#print axioms` on the same declarations.  The project `#assert_no_axioms` macro is fuel-based; the
independent `#print axioms` closes the gate.  (The private arithmetic backbone `braidRestSuccConvFold` is checked
transitively through the public `sigmaAtBraidReshapeRightConv` that consumes it.) -/

namespace FX1PolyAudit

-- A1 — the common-pad width-3-core letters.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBraidCoreLetterRight
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBraidCoreLetterLeft

-- A2 — the dim-1 snoc reshape primitive.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAWordPowOneIsGenConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAWordPowSnocConv

-- A3 — the per-letter reshapes to common-pad core form.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBraidReshapeRightPure
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBraidReshapeLeftPure

-- A4 — the triple collapse + the Yang-Baxter atom + the core braid.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBraidTripleCollapse
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBraidAtomConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBraidCoreConv

-- A5 — the sigmaAt-connection legs (the arithmetic threaded here).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtBraidReshapeRightConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtBraidReshapeLeftConv

-- A6 — the two triple reshapes + the headline generic braid + the matrix pin + the marker.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBraidTripleReshapeLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBraidTripleReshapeRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidGenericBraidConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidGenericBraidThreeZeroMatrixShared
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_genericAdjacentBraidConvShipped

-- Independent (non-fuel) axiom prints on the atom, the core braid, the headline, the pin, and the marker.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAWordPowSnocConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBraidReshapeRightPure
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBraidReshapeLeftPure
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBraidTripleCollapse
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBraidAtomConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBraidCoreConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtBraidReshapeRightConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtBraidReshapeLeftConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBraidTripleReshapeLeftSide
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBraidTripleReshapeRightSide
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidGenericBraidConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidGenericBraidThreeZeroMatrixShared
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_genericAdjacentBraidConvShipped

end FX1PolyAudit
