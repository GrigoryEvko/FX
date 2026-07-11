import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidStarAssembly

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidStarAssemblyAudit — zero-axiom gate for the re-stated
`additive AND well-typed` star, the two-guard exclusion of both self-attack counterexamples, and the honest
no-flip star ledger (WP-PROP r7, #2033).

Per-declaration `#assert_no_axioms` on: the re-stated star statement; the matrix match + the headline
additive-but-not-well-typed datum; the two-guard exclusion + the both-guards-needed bundle; and the B4 markers
(including the `= false` no-flip marker).

Independent `#print axioms` on the exclusion + the both-guards bundle + the headline datum closes the gate. -/

namespace FX1PolyAudit

-- The re-stated star statement.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStarStatementAdditiveWellTyped

-- The matrix match + the headline datum + the exclusion + the both-guards bundle.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMisdeclaredMuMatchesAddMuMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMisdeclaredMuIsAdditiveButNotWellTyped
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRestatedStarExcludesMisdeclaredDatum
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStarNeedsBothGuards

-- The B4 markers (re-stated star + two-guard exclusion + gated legs + no-flip + ledger).
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_restatedStarCarriesWellTypedness
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_restatedStarExcludesBothCounterexamples
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_starLegsGatedOnB1AndB2
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedWellTypedStarStillOpen
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_starAssemblyRoundSevenLedgerShipped

-- Independent (non-fuel) axiom prints on the exclusion + the both-guards bundle + the headline datum.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRestatedStarExcludesMisdeclaredDatum
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStarNeedsBothGuards
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMisdeclaredMuIsAdditiveButNotWellTyped

end FX1PolyAudit
