import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutInteriorOrdinalReanchor

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutInteriorOrdinalReanchor — zero-axiom gate for the r19
per-ordinal wall-shift law + the definitional interior-ordinal placement (WP-AMALG-2 r19, B1)

Per-declaration zero-axiom gate for the per-ordinal wall offsets (`wallOffsetDomAt` / `wallOffsetCodAt` /
`cumGapDomBelow` / `cumGapCodBelow`), the per-ordinal shift-composition law `wallShiftComposesAt`, the definitional
placement corollaries, the deep wire-changing nest probes, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallOffsetDomAt
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallOffsetCodAt
#assert_no_axioms FX1Poly.Polygraph.Amalgam.cumGapDomBelow
#assert_no_axioms FX1Poly.Polygraph.Amalgam.cumGapCodBelow
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallShiftComposesAt
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallOffsetAt_gapDomLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallOffsetAt_gapCodLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.muNestBody
#assert_no_axioms FX1Poly.Polygraph.Amalgam.muNest_interiorOrdinalShifts
#assert_no_axioms FX1Poly.Polygraph.Amalgam.muNest_wallShiftComposesInterior
#assert_no_axioms FX1Poly.Polygraph.Amalgam.muNest_wallShiftComposesTrailing
#assert_no_axioms FX1Poly.Polygraph.Amalgam.muNest_placementDefinitional
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_interiorOrdinalPlacementDefinitional
#assert_no_axioms FX1Poly.Polygraph.Amalgam.interiorOrdinalReanchorNoWallFlip

end FX1PolyAudit
