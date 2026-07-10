import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.ThinWalkerMigration

/-! # FX1PolyAudit.Polygraph.TwoCategory.Table.ThinWalkerMigration — zero-axiom gate for the thin-class walker
migrations as table values (POLY-TAB r1, P3).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.idempotentWalker_iff_generic
#assert_no_axioms FX1Poly.Polygraph.idempotentRouteAgreement
#assert_no_axioms FX1Poly.Polygraph.idempotentRouteAgreement_holds
#assert_no_axioms FX1Poly.Polygraph.involutionWalker_iff_generic
#assert_no_axioms FX1Poly.Polygraph.involutionRouteAgreement
#assert_no_axioms FX1Poly.Polygraph.involutionRouteAgreement_holds
#assert_no_axioms FX1Poly.Polygraph.monadRelationFamily_bridge_is_precedent
#assert_no_axioms FX1Poly.Polygraph.monadSeparatingRouteAgreement
#assert_no_axioms FX1Poly.Polygraph.monadSeparatingRouteAgreement_holds
#assert_no_axioms FX1Poly.Polygraph.fxTab_hasThinClassWalkerMigrations
#assert_no_axioms FX1Poly.Polygraph.fxTab_hasKZWalkerMigration
#assert_no_axioms FX1Poly.Polygraph.fxTab_hasKZMonadConvGenericRepoint

end FX1PolyAudit
