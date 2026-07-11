import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizeCanonical

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFactorizeCanonical — zero-axiom gate for the r19 canonical
factorization subtype + arms + width-matching adjudication (WP-AMALG-2 r19, B3)

Per-declaration zero-axiom gate for the `CanonicalFactorization` subtype, the `gen` arm, the `id`-arm slot-spec +
boundary equality, the width-matching adjudication, the honesty markers, and the master pins.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.CanonicalFactorization
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mulCanonicalFactorization
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mulCanonicalSlotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idCanonicalArmMeetsSlotSpec
#assert_no_axioms FX1Poly.Polygraph.Amalgam.firingBlockLayoutAux_gapDomEqCod
#assert_no_axioms FX1Poly.Polygraph.Amalgam.widthVariationAbsorbedByThreeFaces
#assert_no_axioms FX1Poly.Polygraph.Amalgam.seamMiddleWidthShared
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasCanonicalFactorizationArms
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_idCanonicalCollapseStaysGated
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_whiskerJunctionMergeStaysWalled
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_vcompCommonRefinementZipStaysWalled
#assert_no_axioms FX1Poly.Polygraph.Amalgam.canonicalArmsLeaveMastersWalled

end FX1PolyAudit
