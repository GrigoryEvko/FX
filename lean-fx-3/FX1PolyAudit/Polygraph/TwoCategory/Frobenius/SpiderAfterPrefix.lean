import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Frobenius.SpiderAfterPrefix

/-! # FX1PolyAudit.Polygraph.TwoCategory.Frobenius.SpiderAfterPrefix — zero-axiom gate (WP-FROB r4, FROB-4)

Per-declaration zero-axiom gate for the spider PREFIX BRIDGE: the loops-free transfer clones
(`canonicalTransfers_ofViewParts`, `compositeConnectivity_transfersAcrossInterface_ofViewParts`,
`compositeBoundaryView_agrees_ofViewParts`), the loops-free two-word functoriality port
(`processBrauer_forgetView_eq_ofCanonicalViewParts`), the prefix bridge itself
(`spiderConv_relation_afterPrefix`), and the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- FROB-4: the loops-free transfer clones (extract equality replaced by length + view parts)
#assert_no_axioms FX1Poly.Polygraph.canonicalTransfers_ofViewParts
#assert_no_axioms FX1Poly.Polygraph.compositeConnectivity_transfersAcrossInterface_ofViewParts
#assert_no_axioms FX1Poly.Polygraph.compositeBoundaryView_agrees_ofViewParts

-- FROB-4: the loops-free two-word functoriality port + the prefix bridge
#assert_no_axioms FX1Poly.Polygraph.processBrauer_forgetView_eq_ofCanonicalViewParts
#assert_no_axioms FX1Poly.Polygraph.spiderConv_relation_afterPrefix

-- FROB-4: the honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSpiderForgetViewFunctoriality
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSpiderPrefixBridge

end FX1PolyAudit
