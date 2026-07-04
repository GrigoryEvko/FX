import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCompositeView

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingCompositeView — zero-axiom gate

Per-declaration zero-axiom gate for the composite boundary view agreement: the boundary
correspondence instance and the two-directional Bool agreement (the private range/read
plumbing is covered transitively).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.interfaceCorresponds_ofCompositeBoundaryPosition
#assert_no_axioms FX1Poly.Polygraph.compositeBoundaryView_agrees_ofExtractEq
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasCompositeBoundaryViewAgreement

end FX1PolyAudit
