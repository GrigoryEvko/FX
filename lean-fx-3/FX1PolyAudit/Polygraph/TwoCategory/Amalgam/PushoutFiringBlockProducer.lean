import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFiringBlockProducer

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFiringBlockProducer — zero-axiom gate for the r19 coarse
firing-block producer + by-construction slot-count spec + round-trips (WP-AMALG-2 r19, B2)

Per-declaration zero-axiom gate for the propext-safe append associativity, the identity-payload block, the coarse
producer, the slot-count spec, the domain / codomain word invariants + round-trips, the degenerate-path probes, and
the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutWordAppendAssoc
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idBlockPair
#assert_no_axioms FX1Poly.Polygraph.Amalgam.firingBlockLayoutAux
#assert_no_axioms FX1Poly.Polygraph.Amalgam.firingBlockLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.firingBlockLayoutAux_length
#assert_no_axioms FX1Poly.Polygraph.Amalgam.firingBlockLayout_slotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.firingBlockLayoutAux_domWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.firingBlockLayoutAux_codWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutPathWord_firingBlockLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapDomLayout_firingBlockLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapCodLayout_firingBlockLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.firingBlockLayout_allWall_slotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.firingBlockLayout_allGap_slotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.firingBlockLayout_wallGapWall_slotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.firingBlockLayout_meetsSpecOnWallSplitter
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasFiringBlockProducer
#assert_no_axioms FX1Poly.Polygraph.Amalgam.firingBlockProducerShipsFlipsResidual

end FX1PolyAudit
