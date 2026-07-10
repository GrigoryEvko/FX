import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.DesignLockOmega3WithId

/-! # FX1PolyAudit/Polygraph/Omega/DesignLockOmega3WithIdAudit — zero-axiom gate (OMEGA-3 r2, B5).

Per-declaration `#assert_no_axioms` on the OMEGA-3 r2 ledger markers (the shipped-piece markers, the
surviving-wall markers, the honest re-assessment, and the OMEGA-4 handoff record). -/

namespace FX1PolyAudit

-- DesignLockOmega3WithId.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega3_idCongrSiblingShippedR2
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega3_soundnessCascadeShippedR2
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega3_conservativeAndFixedWhiskerShippedR2
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega3_convFormEckmannHiltonAndShiftShippedR2
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega3_generalWhiskeredMapInOpenR2
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega3_multiGeneratorBookkeepingOpenR2
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega3_omega3CompleteReassessedR2
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega3_omegaFourSquierAscentHandoffRecordedR2

end FX1PolyAudit
