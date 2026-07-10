import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringAdjacentPairLocate

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringAdjacentPairLocate — zero-axiom gate (FC-3 r8, B1)

Per-declaration zero-axiom gate for the DATA-valued adjacent cup·cap locate: the split carrier and its cons, the
total structural locate, the completeness bridge, and the two truth-probes.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.SpineAdjacentCupCapSplit
#assert_no_axioms FX1Poly.Polygraph.SpineAdjacentCupCapSplit.cons
#assert_no_axioms FX1Poly.Polygraph.locateAdjacentCupCapSplit
#assert_no_axioms FX1Poly.Polygraph.locateAdjacentCupCapSplit_eq_none_isValley
#assert_no_axioms FX1Poly.Polygraph.stringProbeCupAtom
#assert_no_axioms FX1Poly.Polygraph.stringProbeCapAtom
#assert_no_axioms FX1Poly.Polygraph.stringProbeLocate_fires
#assert_no_axioms FX1Poly.Polygraph.stringProbeLocate_declines
#assert_no_axioms FX1Poly.Polygraph.fxString_hasStringDataValuedLocate

end FX1PolyAudit
