import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.GrayCategory

/-! # FX1PolyAudit/AuditTier0ModeGrayCategory — zero-axiom gate for mode-5's Gray-category

Per-declaration zero-axiom gate for `mode-5` (`FX1Poly/Tier0/Mode/GrayCategory.lean`): the two whisker-order
2-cells the interchanger mediates (`RawTwoCategory.interchangeSource` / `interchangeTarget`), the semistrict
3-category interface `RawGrayCategory` (with the invertible INTERCHANGER 3-cell), the locally-discrete realizing
instance and the free mode Gray-category, the strict-interchange smoke, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The interchanger boundary (the two whisker orders)
#assert_no_axioms FX1Poly.Tier0.RawTwoCategory.interchangeSource
#assert_no_axioms FX1Poly.Tier0.RawTwoCategory.interchangeTarget

-- The semistrict 3-category interface + the realizing instances
#assert_no_axioms FX1Poly.Tier0.RawGrayCategory
#assert_no_axioms FX1Poly.Tier0.locallyDiscreteGrayCategory
#assert_no_axioms FX1Poly.Tier0.freeModeGrayCategory
#assert_no_axioms FX1Poly.Tier0.freeModeGrayCategory_twoCategory
#assert_no_axioms FX1Poly.Tier0.locallyDiscreteGrayCategory_interchanger_isRefl

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasNonTrivialInterchanger
#assert_no_axioms FX1Poly.Tier0.fxMode_hasGrayTensorProduct
#assert_no_axioms FX1Poly.Tier0.fxMode_hasTricategoryCoherence

end FX1PolyAudit
