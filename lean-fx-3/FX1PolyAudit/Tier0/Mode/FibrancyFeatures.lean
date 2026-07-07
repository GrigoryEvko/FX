import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.FibrancyFeatures

/-! # FX1PolyAudit/Tier0/Mode/FibrancyFeatures — zero-axiom gate

Per-declaration zero-axiom gate for the φ-cube (the Geometric coordinate of the grade↔mode spectrum):
the cube order laws, the interior/join facts, the total maps from the shipped classifiers, the
richer-than-discrete payoff, and every honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.FibrancyFeatures.le_refl
#assert_no_axioms FX1Poly.Tier0.FibrancyFeatures.le_trans
#assert_no_axioms FX1Poly.Tier0.FibrancyFeatures.le_antisymm
#assert_no_axioms FX1Poly.Tier0.FibrancyFeatures.strict_le
#assert_no_axioms FX1Poly.Tier0.FibrancyFeatures.le_omega
#assert_no_axioms FX1Poly.Tier0.FibrancyFeatures.directedRelational_eq_join
#assert_no_axioms FX1Poly.Tier0.featuresOfFibrancyKind
#assert_no_axioms FX1Poly.Tier0.featuresOfFibrancyKind_fibrant
#assert_no_axioms FX1Poly.Tier0.featuresOfFibrancyKind_exotype
#assert_no_axioms FX1Poly.Tier0.featuresOfAdjointClass
#assert_no_axioms FX1Poly.Tier0.featuresOfAdjointClass_tangible
#assert_no_axioms FX1Poly.Tier0.featuresOfAdjointClass_sharp
#assert_no_axioms FX1Poly.Tier0.featuresOfAdjointClass_sinister
#assert_no_axioms FX1Poly.Tier0.featuresOfAdjointClass_transparent
#assert_no_axioms FX1Poly.Tier0.featuresOfAdjointClass_ne_directedRelational
#assert_no_axioms FX1Poly.Tier0.featuresOfAdjointClass_ne_omega
#assert_no_axioms FX1Poly.Tier0.fxFibrancyFeatures_hasCube
#assert_no_axioms FX1Poly.Tier0.fxFibrancyFeatures_hasClassifierReading
#assert_no_axioms FX1Poly.Tier0.fxFibrancyFeatures_hasRicherInterior

end FX1PolyAudit
