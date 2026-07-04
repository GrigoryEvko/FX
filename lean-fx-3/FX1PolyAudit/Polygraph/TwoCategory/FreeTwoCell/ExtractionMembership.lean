import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ExtractionMembership

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/ExtractionMembership — zero-axiom gate

Per-declaration zero-axiom gate for the hand-rolled list membership kit and the
enumeration's membership constructors/destructor.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.listMemConsCases
#assert_no_axioms FX1Poly.Polygraph.listMemAppendOfLeft
#assert_no_axioms FX1Poly.Polygraph.listMemAppendOfRight
#assert_no_axioms FX1Poly.Polygraph.listMemAppendCases
#assert_no_axioms FX1Poly.Polygraph.listMemFilterMapOfMem
#assert_no_axioms FX1Poly.Polygraph.listMemFilterMapInverted
#assert_no_axioms FX1Poly.Polygraph.frontExtractions_containsHead
#assert_no_axioms FX1Poly.Polygraph.frontExtractions_containsForwardLift
#assert_no_axioms FX1Poly.Polygraph.frontExtractions_containsReverseLift
#assert_no_axioms FX1Poly.Polygraph.frontExtractions_nilHasNoMember
#assert_no_axioms FX1Poly.Polygraph.frontExtractions_memCases

end FX1PolyAudit
