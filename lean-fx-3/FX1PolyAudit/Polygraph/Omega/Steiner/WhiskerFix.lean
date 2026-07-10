import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Steiner.WhiskerFix

/-! # FX1PolyAudit/Polygraph/Omega/Steiner/WhiskerFix — zero-axiom gate (OMEGA-2.5 r1, B3)

Per-declaration `#assert_no_axioms` on the acceptance test: the concrete faithful demo computad /
valuation / cells, and the three headline facts — the whiskerings are distinct, `linearize` CONFLATES the
whiskered pair, and `linearizeFull` DISTINGUISHES it (the lossy-whisker obstruction dissolved at chain
granularity).  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The concrete faithful witness
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerDemoComputad
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerDemoValuation
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskeringGen
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerMainCell
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskeredCell

-- The acceptance test: conflation vs distinction
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerFix_whiskering_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerFix_linearize_conflates
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerFix_linearizeFull_distinguishes

end FX1PolyAudit
