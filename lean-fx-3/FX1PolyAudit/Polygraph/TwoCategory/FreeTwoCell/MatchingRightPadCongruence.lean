import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRightPadCongruence

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingRightPadCongruence — zero-axiom gate

Per-declaration zero-axiom gate for the padded extract congruence: the paired read data, the
four-zone taxonomy, the padded connectivity-view agreement, the extract-level payoff, and the
honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.RightPadPairedRead
#assert_no_axioms FX1Poly.Polygraph.rightPadSim_pairedReadTaxonomy
#assert_no_axioms FX1Poly.Polygraph.matchingSameComponent_ofRightPadSimPair
#assert_no_axioms FX1Poly.Polygraph.extractDiagram_ofRightPadSimPair
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingRightPadExtractCongruence

end FX1PolyAudit
