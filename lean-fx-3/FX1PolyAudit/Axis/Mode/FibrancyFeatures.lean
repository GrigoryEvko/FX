import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.FibrancyFeatures

/-! # FX1PolyAudit/Axis/Mode/FibrancyFeatures — zero-axiom gate

Per-declaration zero-axiom gate for the φ-cube (the Geometric coordinate of the grade↔mode spectrum):
the cube order laws, the interior/join facts, the total maps from the shipped classifiers, the
richer-than-discrete payoff, and every honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Axis.FibrancyFeatures.le_refl
#assert_no_axioms FX1Poly.Axis.FibrancyFeatures.le_trans
#assert_no_axioms FX1Poly.Axis.FibrancyFeatures.le_antisymm
#assert_no_axioms FX1Poly.Axis.FibrancyFeatures.strict_le
#assert_no_axioms FX1Poly.Axis.FibrancyFeatures.le_omega
#assert_no_axioms FX1Poly.Axis.FibrancyFeatures.directedRelational_eq_join
#assert_no_axioms FX1Poly.Axis.featuresOfFibrancyKind
#assert_no_axioms FX1Poly.Axis.featuresOfFibrancyKind_fibrant
#assert_no_axioms FX1Poly.Axis.featuresOfFibrancyKind_exotype
#assert_no_axioms FX1Poly.Axis.featuresOfAdjointClass
#assert_no_axioms FX1Poly.Axis.featuresOfAdjointClass_tangible
#assert_no_axioms FX1Poly.Axis.featuresOfAdjointClass_sharp
#assert_no_axioms FX1Poly.Axis.featuresOfAdjointClass_sinister
#assert_no_axioms FX1Poly.Axis.featuresOfAdjointClass_transparent
#assert_no_axioms FX1Poly.Axis.featuresOfAdjointClass_ne_directedRelational
#assert_no_axioms FX1Poly.Axis.featuresOfAdjointClass_ne_omega
#assert_no_axioms FX1Poly.Axis.fxFibrancyFeatures_hasCube
#assert_no_axioms FX1Poly.Axis.fxFibrancyFeatures_hasClassifierReading
#assert_no_axioms FX1Poly.Axis.fxFibrancyFeatures_hasRicherInterior

end FX1PolyAudit
