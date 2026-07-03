import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingInterfaceSegment

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingInterfaceSegment — zero-axiom gate

Per-declaration zero-axiom gate for the segment-transfer discharge: the packaged
correspondence, the canonical-data segment discharge, and the composite transfer at the
discharged relation (the private support-scan plumbing is covered transitively).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.interfaceCorresponds_ofBelowBase
#assert_no_axioms FX1Poly.Polygraph.interfaceCorresponds_ofCanonicalPair
#assert_no_axioms FX1Poly.Polygraph.segmentTransfers_ofCanonicalPairs
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_applyJoinEvents_transferAcrossInterface_ofCanonicalPairs
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasInterfaceSegmentDischarge

end FX1PolyAudit
