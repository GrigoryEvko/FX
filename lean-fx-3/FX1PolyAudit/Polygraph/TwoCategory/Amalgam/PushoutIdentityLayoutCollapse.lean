import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutIdentityLayoutCollapse

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutIdentityLayoutCollapse — zero-axiom gate for the r20 B2 arm
(a): the multi-block identity-layout collapse conv + the general `id`-arm canonical factorization (WP-AMALG-2 r20, B2)

Per-declaration zero-axiom gate for the `AllIdBlocks` predicate, the boundary-equality lemma, the list-form and
producer-form identity collapses, the producer all-identity witness, the cast reassociation bridge, the general `id`
arm (`pushoutFactorizeIdCanonical` / `idCanonicalFactorization`), the slot-count probe, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.AllIdBlocks
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idBlockPairConsVcompCollapse
#assert_no_axioms FX1Poly.Polygraph.Amalgam.allIdBlocks_gapDomEqCod
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapVcompLayoutIdBlocksCollapse
#assert_no_axioms FX1Poly.Polygraph.Amalgam.firingBlockLayoutAux_allIdBlocks
#assert_no_axioms FX1Poly.Polygraph.Amalgam.firingBlockLayoutIdCollapse
#assert_no_axioms FX1Poly.Polygraph.Amalgam.castBoundaryIdReassoc
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeIdCanonical
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idCanonicalFactorization
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idCanonicalFactorizationSlotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasIdCanonicalCollapse
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idCanonicalCollapseShipsResidual

end FX1PolyAudit
