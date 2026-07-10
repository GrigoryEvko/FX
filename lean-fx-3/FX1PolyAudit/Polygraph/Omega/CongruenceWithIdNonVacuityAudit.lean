import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.CongruenceWithIdNonVacuity

/-! # FX1PolyAudit.Polygraph.Omega.CongruenceWithIdNonVacuityAudit — zero-axiom gate for the idCongr
non-vacuity witnesses (OMEGA-3 r2, B1).

Per-declaration `#assert_no_axioms` on the concrete idCongr convertibility, the crown-carrier vcompIdLeft
jam discharge, and the free embedding witness. -/

namespace FX1PolyAudit

-- CongruenceWithIdNonVacuity.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.idCongr_word3_nonVacuous
#assert_no_axioms FX1Poly.Polygraph.Omega.crownJam_dischargedWithId
#assert_no_axioms FX1Poly.Polygraph.Omega.embed_word3_nonVacuous

end FX1PolyAudit
