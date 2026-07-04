import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCanonicalPairs

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingCanonicalPairs — zero-axiom gate

Per-declaration zero-axiom gate for the positional boundary pairing: the pairing itself, the
two position families, the zone-discipline port discharge, the view-simulation canonical
transfer, and the fully discharged composite transfer (the private range kit is covered
transitively).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.canonicalBoundaryPair_ofBottomPort
#assert_no_axioms FX1Poly.Polygraph.canonicalBoundaryPair_ofTopPosition
#assert_no_axioms FX1Poly.Polygraph.canonicalBoundaryPair_selfOfPortImage
#assert_no_axioms FX1Poly.Polygraph.canonicalTransfers_ofViewSim
#assert_no_axioms FX1Poly.Polygraph.compositeConnectivity_transfersAcrossInterface
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasCanonicalBoundaryPairing

end FX1PolyAudit
