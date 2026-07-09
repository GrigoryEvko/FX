import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanNoLoops

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringFussCatalanNoLoops — zero-axiom gate (FC-1 A)

Per-declaration zero-axiom gate for the strand-orientation discipline (the chirality refutation, the seed, the
step-level loop link) and the no-loops theorem assembled modulo the two per-step residuals.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringPathLabels_length
#assert_no_axioms FX1Poly.Polygraph.StringOrientationDiscipline
#assert_no_axioms FX1Poly.Polygraph.stringDisciplinedCap_windowDistinct
#assert_no_axioms FX1Poly.Polygraph.stringBothCapWords_notCupWord
#assert_no_axioms FX1Poly.Polygraph.stringInitialDiscipline
#assert_no_axioms FX1Poly.Polygraph.stringStepCap_loopsPreserved_ofDisciplined
#assert_no_axioms FX1Poly.Polygraph.stringCapsDistinctAlongFold_ofDisciplinePreserved
#assert_no_axioms FX1Poly.Polygraph.stringMatchingOf_loops_zero_ofDisciplinePreserved
#assert_no_axioms FX1Poly.Polygraph.fxString_hasOrientationDiscipline
#assert_no_axioms FX1Poly.Polygraph.fxString_hasNoLoopsAssembledModuloTwoResiduals
#assert_no_axioms FX1Poly.Polygraph.fxString_hasOrientationDisciplineFoldInvariance

end FX1PolyAudit
