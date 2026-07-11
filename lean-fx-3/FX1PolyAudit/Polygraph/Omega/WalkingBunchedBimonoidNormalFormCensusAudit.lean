import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidNormalFormCensus

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidNormalFormCensusAudit — zero-axiom gate for the
NF-induction census + the #2033 star scope (WP-PROP r4, #2033, the 110-percent grind).

Per-declaration `#assert_no_axioms` on the NF-census delivery: the vcomp-case perm-of-a-diagonal witness, the
star's congruence scope + the NAMED (unproven) star statement + the three row-family embeddings, and the ledger
markers.  The star statement is a NAMED proposition, NOT proven — the star markers do NOT flip. -/

namespace FX1PolyAudit

-- B1 — the vcomp-case witness (permutation-of-a-diagonal).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermutedDiagTwoThree
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermutedDiagRoundTrip
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_nfInductionCensusShipped

-- B2 — the star scope + the NAMED star + the three embeddings.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStarCongruenceScope
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStarStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSoundRowEmbedsIntoStarScope
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidHexagonRowEmbedsIntoStarScope
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrictAxiomEmbedsIntoStarScope
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_starScopeStrictSoundHexagon
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_nfInductionStarStillRFive

-- B3 — the reached fragment + the ledger.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_nfReachedFragmentBlockDiagPlusPerm
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_normalFormCensusLedgerShipped

end FX1PolyAudit
