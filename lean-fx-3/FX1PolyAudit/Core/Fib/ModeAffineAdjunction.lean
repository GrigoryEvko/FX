import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Fib.ModeAffineAdjunction

/-! # FX1PolyAudit.Core.Fib.ModeAffineAdjunction — zero-axiom gate (A1-MODE-AFFINE)

Per-declaration zero-axiom gate for the affine dimension modality μ_affine ⊣ μ_affine†: the two modality 1-cells,
the adjunction data, the mode-axis identity, the unit/counit generator facts, and the honest triangle-saturation
marker. Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.Fib.affineDimensionModality
#assert_no_axioms FX1Poly.Core.Fib.affineDimensionModalityDagger
#assert_no_axioms FX1Poly.Core.Fib.affineDimensionModalityAdjunction
#assert_no_axioms FX1Poly.Core.Fib.affineDimensionModality_overFxModeAxis
#assert_no_axioms FX1Poly.Core.Fib.affineDimensionModalityAdjunction_unit_isSeedUnit
#assert_no_axioms FX1Poly.Core.Fib.affineDimensionModalityAdjunction_counit_isSeedCounit
#assert_no_axioms FX1Poly.Core.Fib.affineModalityAdjunction_triangleLawsNeedSaturation

end FX1PolyAudit
