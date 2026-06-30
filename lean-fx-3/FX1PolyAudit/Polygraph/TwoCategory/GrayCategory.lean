import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.GrayCategory

/-! # FX1PolyAudit.Polygraph.TwoCategory.GrayCategory — zero-axiom gate (mirror shard)

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.TwoCategory.GrayCategory`: the two
whisker-order 2-cells the interchanger mediates (`RawTwoCategory.interchangeSource` / `interchangeTarget`), the
semistrict 3-category interface `RawGrayCategory` (with the invertible INTERCHANGER 3-cell), the locally-discrete
realizing instance and the strict-interchange smoke, plus the honesty markers.

Each declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The interchanger boundary (the two whisker orders)
#assert_no_axioms FX1Poly.Tier0.RawTwoCategory.interchangeSource
#assert_no_axioms FX1Poly.Tier0.RawTwoCategory.interchangeTarget

-- The semistrict 3-category interface + the realizing instance + the strict-interchange smoke
#assert_no_axioms FX1Poly.Tier0.RawGrayCategory
#assert_no_axioms FX1Poly.Tier0.locallyDiscreteGrayCategory
#assert_no_axioms FX1Poly.Tier0.locallyDiscreteGrayCategory_interchanger_isRefl

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasNonTrivialInterchanger
#assert_no_axioms FX1Poly.Tier0.fxMode_hasGrayTensorProduct
#assert_no_axioms FX1Poly.Tier0.fxMode_hasTricategoryCoherence

end FX1PolyAudit
