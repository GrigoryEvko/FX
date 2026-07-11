import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringTwoSpeciesMatchingProbe

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringTwoSpeciesMatchingProbe — zero-axiom gate (FC-3 r12, B3)

Per-declaration zero-axiom gate for the two-species scrambled-pair matching-invariance truth-probe
(`stringTwoSpeciesWindow_matchingInvariant`) and the marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringTwoSpeciesWindow_matchingInvariant
#assert_no_axioms FX1Poly.Polygraph.fxString_hasTwoSpeciesMatchingProbe

end FX1PolyAudit
