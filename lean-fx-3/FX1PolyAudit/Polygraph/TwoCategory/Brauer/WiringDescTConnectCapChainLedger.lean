import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTConnectCapChainLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescTConnectCapChainLedger — zero-axiom gate (BRAUER r24, the cap
chain routed + CUP / THROUGH probes + the exact #2013 ledger)

Per-declaration zero-axiom gate: the general cap-class partner read-off (`partnerIndexOf_readsCapArc_general`) and its
firing, the CUP nested-cups probes (`cupChainTopDecodeProbe_nestedCups`, `cupChainJoinProbe_nestedCups`), the THROUGH
adversarial-B probe (`throughChainProbe_adversarialB`), and the r24 ledger (`fxBrauer_r24CapChainLedger`) — the
machine-checked `rfl`-conjunction recording the two NEW cap-chain ingredient markers true and every master wall false.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_readsCapArc_general
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_readsCapArc_firesAllCaps_zero
#assert_no_axioms FX1Poly.Polygraph.cupChainTopDecodeProbe_nestedCups
#assert_no_axioms FX1Poly.Polygraph.cupChainJoinProbe_nestedCups
#assert_no_axioms FX1Poly.Polygraph.throughChainProbe_adversarialB
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasTConnectCapClassRouted
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_r24CapChainLedger

end FX1PolyAudit
