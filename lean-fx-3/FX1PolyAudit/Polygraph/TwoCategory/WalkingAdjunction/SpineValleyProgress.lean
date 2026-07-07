import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyProgress

/-! # FX1PolyAudit/…/SpineValleyProgress — zero-axiom gate

Per-declaration zero-axiom gate for the VALLEY PROGRESS lemma — the machine-checked refutation that the
valley-normalization's "innermost cup-cap partner pair exists" premise needs an arc-structure readoff.  The
first-cup progress lemma `hasAdjacentCupThenCap_of_not_valley`, its concrete split, the spine specialization,
and the pair classifier must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.allCups
#assert_no_axioms FX1Poly.Polygraph.isCapThenCupValley
#assert_no_axioms FX1Poly.Polygraph.hasAdjacentCupThenCap_of_cup_of_not_allCups
#assert_no_axioms FX1Poly.Polygraph.hasAdjacentCupThenCap_of_not_valley
#assert_no_axioms FX1Poly.Polygraph.hasAdjacentCupThenCap_split
#assert_no_axioms FX1Poly.Polygraph.SpineAtom.isCupAtom
#assert_no_axioms FX1Poly.Polygraph.hasAdjacentCupThenCap_of_not_valley_spine
#assert_no_axioms FX1Poly.Polygraph.natWindowDistance
#assert_no_axioms FX1Poly.Polygraph.classifyAdjacentCupCap
#assert_no_axioms FX1Poly.Polygraph.classifyAdjacentAtoms
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyProgress

end FX1PolyAudit
