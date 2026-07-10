import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupSlideSoundness

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCupSlideSoundness — zero-axiom gate (WP-BRAUER-4 r4, B2)

Per-declaration zero-axiom gate for the V2 soundness arm: the cup-slide row is `BrauerConv`-convertible in arbitrary
horizontal context (`brauerConv_cupSlide_inContext`, the general keystone arm), a genuinely boundary-CHANGING
non-minimal instance (`brauerConv_cupSlide_inWiderContext`) backed by the diagram-equality non-vacuity check
(`cupSlide_shifted_diagramEq`), the distinctness witness, and the soundness marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the ONE new arm + the boundary-CHANGING non-minimal instance
#assert_no_axioms FX1Poly.Polygraph.brauerConv_cupSlide_inContext
#assert_no_axioms FX1Poly.Polygraph.brauerConv_cupSlide_inWiderContext

-- non-vacuity at the non-minimal instance
#assert_no_axioms FX1Poly.Polygraph.cupSlide_shifted_diagramEq
#assert_no_axioms FX1Poly.Polygraph.brauerConv_cupSlide_inWiderContext_distinct

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCupSlideConvSoundness

end FX1PolyAudit
