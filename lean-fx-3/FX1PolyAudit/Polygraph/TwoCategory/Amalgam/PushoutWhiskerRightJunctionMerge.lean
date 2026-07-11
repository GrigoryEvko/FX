import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerRightJunctionMerge

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWhiskerRightJunctionMerge — zero-axiom gate for the r21 B2
whiskerRight (trailing) producer merge law + the whiskerRight junction residual naming (WP-AMALG-2 r21, B2 — arm b')

Per-declaration zero-axiom gate for the direction-symmetric producer merge law, its trailing slot count, the trailing
route-agreement probe, the trailing junction slot-count probe, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.firingBlockLayout_composePathRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.spliceFrameBlocks_firingBlockLayout_slotCountRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightJunctionMerge_producerRouteAgrees
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightJunctionMerge_sliceSlotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasFiringBlockProducerMergeLawRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_whiskerRightJunctionCanonicalStaysResidual

end FX1PolyAudit
