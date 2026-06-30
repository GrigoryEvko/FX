import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.GrayCategory

/-! # FX1PolyAudit/AuditTier0ModeGrayCategory — zero-axiom gate for mode-5's free Gray-category

Per-declaration zero-axiom gate for `mode-5`'s mode-axis deliverable (`FX1Poly/Tier0/Mode/GrayCategory.lean`):
the free mode 1-category exhibited as a (strict, locally-discrete) Gray-category (`freeModeGrayCategory`) and its
base round-trip.  The GENERIC Gray-category core it builds on (`RawTwoCategory.interchangeSource` /
`interchangeTarget`, `RawGrayCategory`, `locallyDiscreteGrayCategory`,
`locallyDiscreteGrayCategory_interchanger_isRefl`, the honesty markers) is gated in
`FX1PolyAudit.Polygraph.TwoCategory.GrayCategory`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The free mode Gray-category
#assert_no_axioms FX1Poly.Tier0.freeModeGrayCategory
#assert_no_axioms FX1Poly.Tier0.freeModeGrayCategory_twoCategory

end FX1PolyAudit
