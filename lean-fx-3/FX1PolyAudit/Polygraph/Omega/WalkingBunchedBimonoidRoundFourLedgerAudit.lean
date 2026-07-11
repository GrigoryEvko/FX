import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidRoundFourLedger

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidRoundFourLedgerAudit — zero-axiom gate for the WP-PROP r4
grand ledger (#2033, the 110-percent grind).

Per-declaration `#assert_no_axioms` on the r4 ledger markers: the three delivered bricks (hexagon / perm-layer /
star-scope), the remaining NAMED nodes with their exact goals (Node A matMul-assoc + general units, Node C
general routing, the star = r5), the additive-only invariant, and the grand scoreboard. -/

namespace FX1PolyAudit

-- The r4 deliverables (B1-B3).
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_r4HexagonDelivered
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_r4PermLayerDelivered
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_r4StarScopeNamed

-- The remaining NAMED nodes with exact goals.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_r4RemainingNodeMatMulAssoc
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_r4RemainingNodeGeneralUnits
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_r4RemainingNodeGeneralRouting
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_r4StarIsRFive

-- The additive-only invariant + the grand ledger.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_r4UpstreamWallsByteIntact
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_roundFourGrandLedgerShipped

end FX1PolyAudit
