import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidRiffleAssembly

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidRiffleAssemblyAudit — zero-axiom gate for the general
`wideSwap(m,n)` riffle word (the r7 wall falls), the staged bialgebra NF matched to the collision, the Coxeter
sorted-NF scaffold, and the honest star partial (WP-PROP r8, #2033).

Per-declaration `#assert_no_axioms` on every def / theorem / marker, PLUS independent (non-fuel) `#print axioms`
on the three recursive riffle defs (`blockPastBlock`/`riffleIn`/`wideSwap` — the structural-recursion witnesses),
the flagship `wideSwap 2 2 = middleSwap` matrix theorem, and the staged-NF-matches-collision probe.  The
project `#assert_no_axioms` macro is fuel-based; the independent `#print axioms` closes the gate. -/

namespace FX1PolyAudit

-- B1 — the three-layer riffle word (the general wideSwap, the r7 wall falls).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockPastBlock
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRiffleIn
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSwap
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockPastBlockTwoTwoMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRiffleInTwoOneIsMiddleSwap
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSwapOneOneMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSwapTwoOneIsIdentity
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSwapOneTwoIsIdentity
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSwapTwoTwoMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSwapTwoTwoIsMiddleSwap
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSwapThreeTwoMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_wideSwapGeneralRiffleWordShipped

-- Independent (non-fuel) axiom prints on the three recursive riffle defs + the flagship matrix theorem.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockPastBlock
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRiffleIn
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSwap
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSwapTwoTwoIsMiddleSwap

end FX1PolyAudit
