import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCapTopPartner

/-! # FX1PolyAudit/…/ValleyCapTopPartner — zero-axiom gate

Per-declaration zero-axiom gate for the cap-TOP partner field of the full `capRestrict` `DiagramType.ext`
(Piece II tail): the generic least-passing-index combinator, `nthSurvivorTop` correctness, the append arity
discipline, and the cap-TOP partner-field agreement (via the shipped `matchingOf` partner involution).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.firstIndexWhere_range_eq_of_minimal
#assert_no_axioms FX1Poly.Polygraph.nthSurvivorTop_correct
#assert_no_axioms FX1Poly.Polygraph.spineHasCupCapAtoms_append
#assert_no_axioms FX1Poly.Polygraph.capRestrict_partner_capTop
#assert_no_axioms FX1Poly.Polygraph.matchingOf_partner_below
#assert_no_axioms FX1Poly.Polygraph.bottomSurvivor_of_partnerAbove
#assert_no_axioms FX1Poly.Polygraph.capRestrict_reconstructs
#assert_no_axioms FX1Poly.Polygraph.sameWholeMatching_capBlockMatchingEq

end FX1PolyAudit
