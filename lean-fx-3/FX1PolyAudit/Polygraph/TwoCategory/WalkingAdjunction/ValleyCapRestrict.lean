import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCapRestrict

/-! # FX1PolyAudit/…/ValleyCapRestrict — zero-axiom gate

Per-declaration zero-axiom gate for the cap-side restriction `capRestrict` (F) on `DiagramType` (Piece II tail):
the reconstruction function plus the two copied-field agreements and the SURVIVOR-BOTTOM partner-field keystone.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.extractDiagram_partner_getAt
#assert_no_axioms FX1Poly.Polygraph.survivorTopTotal
#assert_no_axioms FX1Poly.Polygraph.firstIndexWhere
#assert_no_axioms FX1Poly.Polygraph.nthSurvivorTop
#assert_no_axioms FX1Poly.Polygraph.capRestrict
#assert_no_axioms FX1Poly.Polygraph.capRestrict_bottomCount_eq
#assert_no_axioms FX1Poly.Polygraph.capRestrict_loops_eq
#assert_no_axioms FX1Poly.Polygraph.capRestrict_partner_survivorBottom
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasCapRestrictSurvivorField

end FX1PolyAudit
