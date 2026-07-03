import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerReconstruction

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingPartnerReconstruction — zero-axiom gate

Per-declaration zero-axiom gate for the extract→view reconstruction: the partner-map read,
the same-component view, the extract read-back, the per-state characterization, the
reconstruction of the connectivity-view simulation from extract equality, and the honesty
marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.diagramPartnerAt
#assert_no_axioms FX1Poly.Polygraph.diagramSameComponentView
#assert_no_axioms FX1Poly.Polygraph.diagramPartnerAt_extract
#assert_no_axioms FX1Poly.Polygraph.matchingSameComponent_eq_diagramView
#assert_no_axioms FX1Poly.Polygraph.matchingConnectivityViewSim_ofExtractEq
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingExtractViewReconstruction

end FX1PolyAudit
