import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerLeftJunctionMerge

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWhiskerLeftJunctionMerge — zero-axiom gate for the r21 B1
producer-level junction merge law (WP-AMALG-2 r21, B1 — arm b core)

Per-declaration zero-axiom gate for the frame-block splice, the producer-nonemptiness lemma, the splice cons pushers,
the accumulator-general and `firingBlockLayout`-form producer merge laws, the splice slot count, the whisker-of-identity
route-agreement truth-probe, the junction slot-count probes, and the producer-merge-law honesty marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.spliceFrameBlocks
#assert_no_axioms FX1Poly.Polygraph.Amalgam.spliceFrameBlocks_cons_cons
#assert_no_axioms FX1Poly.Polygraph.Amalgam.firingBlockLayoutAux_ne_nil
#assert_no_axioms FX1Poly.Polygraph.Amalgam.spliceFrameBlocks_firingBlockCons
#assert_no_axioms FX1Poly.Polygraph.Amalgam.firingBlockLayoutAux_composePath
#assert_no_axioms FX1Poly.Polygraph.Amalgam.firingBlockLayout_composePath
#assert_no_axioms FX1Poly.Polygraph.Amalgam.spliceFrameBlocks_firingBlockLayout_slotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftJunctionMerge_producerRouteAgrees
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftJunctionMerge_sliceSlotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftJunctionMerge_sliceSlotCountWallHeavy
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasFiringBlockProducerMergeLaw

end FX1PolyAudit
