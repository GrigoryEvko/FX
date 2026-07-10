import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.RealCoprojectionLeft

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.RealCoprojectionLeft — zero-axiom gate for the genuine-generator
LEFT coprojection `onTwoCell`

Per-declaration zero-axiom gate for the 2-generator left embedding, its get-alignment, the left coprojection's
mode-injectivity, the real left coprojection, the non-vacuity witness, and the honesty marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.embedLeftTwoGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutTwoGenGetLeft
#assert_no_axioms FX1Poly.Polygraph.Amalgam.inclusionLeft_onModes_injective
#assert_no_axioms FX1Poly.Polygraph.Amalgam.inclusionLeftTwoReal
#assert_no_axioms FX1Poly.Polygraph.Amalgam.inclusionLeftTwoReal_onUnit_index
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasRealGeneratorCoprojectionLeft

end FX1PolyAudit
