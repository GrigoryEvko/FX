import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidWideCollision

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidWideCollisionAudit — zero-axiom gate for the wide
bialgebra collision lifted from matrix to convertibility at the base + degenerate ends, with the general routing
recursion walled (WP-PROP r6, #2033).

Per-declaration `#assert_no_axioms` on: the collision family; the width-2 CONV base; the boundary source / target
lemmas; the two degenerate unit collapses; the staged (2,2) normal form; the wide matrix probes; and the B1
markers (including the two `= false` routing-residual markers).

Independent `#print axioms` on the width-2 CONV base and the two degenerate collapses closes the gate. -/

namespace FX1PolyAudit

-- The collision family + the width-2 CONV base.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideCollision
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWidthTwoCollisionConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideCollisionTwoTwoMatrix

-- The boundary lemmas + the degenerate unit collapses.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaFanSource
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuFoldTarget
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCollisionMuFoldOneCollapse
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCollisionDeltaFanOneCollapse

-- The staged (2,2) normal form + the wide matrix probes.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBialgebraNormalFormTwoTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBialgebraNormalFormTwoTwoMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideCollisionMatrixThreeByTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideCollisionMatrixTwoByThree

-- The B1 markers (established + the two routing residuals + the ledger).
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_widthTwoCollisionLiftedToConv
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_wideCollisionMatrixConcreteAtWidthThree
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_wideSwapGeneralRiffleWordUnbuilt
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_wideCollisionConvRecursionUnbuilt
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_wideCollisionRoundSixLedgerShipped

-- Independent (non-fuel) axiom prints on the CONV theorems.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWidthTwoCollisionConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCollisionMuFoldOneCollapse
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCollisionDeltaFanOneCollapse

end FX1PolyAudit
