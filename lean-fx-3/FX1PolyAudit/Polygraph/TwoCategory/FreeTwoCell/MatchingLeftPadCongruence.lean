import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingLeftPadCongruence

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingLeftPadCongruence — zero-axiom gate

Per-declaration zero-axiom gate for the LEFT-padded extract congruence: the paired read data,
the four-zone taxonomy (pad bottom / shifted bottom / pad top / shifted top), the padded
connectivity-view agreement, the extract-level payoff, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.LeftPadPairedRead
#assert_no_axioms FX1Poly.Polygraph.leftPadSim_pairedReadTaxonomy
#assert_no_axioms FX1Poly.Polygraph.matchingSameComponent_ofLeftPadSimPair
#assert_no_axioms FX1Poly.Polygraph.extractDiagram_ofLeftPadSimPair
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingLeftPadExtractCongruence

end FX1PolyAudit
