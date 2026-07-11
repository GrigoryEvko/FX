import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTConnectCapClass

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescTConnectCapClass — zero-axiom gate (BRAUER r22, the
T-CONNECT routing collapse + the per-arc-class connectivity probes/firings)

Per-declaration zero-axiom gate: the bottom–bottom cap-arc reduction
(`matchingSameComponent_bottomBottom_eq_isSameComponent`), the GENERAL routing collapse
(`partnerIndexOf_reads_arc_general`), the per-class connectivity probes
(`tConnectCapClass_connectivity_allCaps` / `_adversarialB`, `tConnectCapClass_nonArc_adversarialB`,
`tConnectCapClass_roundtrip_allCaps`), the adversarial-B involution witness
(`isBoundaryInvolution_adversarialBDiagram`), the routed firings
(`partnerIndexOf_readsCapArc_allCaps_zero` / `_one`, `partnerIndexOf_readsArc_adversarialB_cap` / `_through` /
`_cup`), the r22 markers (`fxBrauer_hasTConnectRoutingCollapse`, `fxBrauer_hasTConnectPerClassProbed`,
`fxBrauer_hasTConnectThroughWall`), and the r22 grand ledger (`fxBrauer_r22GrandLedger`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.matchingSameComponent_bottomBottom_eq_isSameComponent
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_reads_arc_general
#assert_no_axioms FX1Poly.Polygraph.tConnectCapClass_connectivity_allCaps
#assert_no_axioms FX1Poly.Polygraph.tConnectCapClass_roundtrip_allCaps
#assert_no_axioms FX1Poly.Polygraph.tConnectCapClass_connectivity_adversarialB
#assert_no_axioms FX1Poly.Polygraph.tConnectCapClass_nonArc_adversarialB
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_readsCapArc_allCaps_zero
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_readsCapArc_allCaps_one
#assert_no_axioms FX1Poly.Polygraph.isBoundaryInvolution_adversarialBDiagram
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_readsArc_adversarialB_cap
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_readsArc_adversarialB_through
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_readsArc_adversarialB_cup
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasTConnectRoutingCollapse
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasTConnectPerClassProbed
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasTConnectThroughWall
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_r22GrandLedger

-- ★ BRAUER r25 B2 (CUP, partial): the top–top / bottom–top join-site matching reductions, the fresh interleaved-cups
-- decode + join probes, and the ingredient marker.
#assert_no_axioms FX1Poly.Polygraph.matchingSameComponent_topTop_eq_isSameComponent
#assert_no_axioms FX1Poly.Polygraph.matchingSameComponent_bottomTop_eq_isSameComponent
#assert_no_axioms FX1Poly.Polygraph.isBoundaryInvolution_interleavedCups
#assert_no_axioms FX1Poly.Polygraph.cupChainTopDecodeProbe_interleavedCups
#assert_no_axioms FX1Poly.Polygraph.cupChainJoinProbe_interleavedCups
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasTopTopMatchingReduction

end FX1PolyAudit
