import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Ledger.Bridge.BridgeRelationalSconeIdentityPath

/-! # FX1PolyAudit/AuditBridgeRelationalSconeIdentityPath — NATIVE-58 identity-path audit shard

Per-declaration zero-axiom gate for the reflexivity-bridge (identity-path) membership in the
relational Bridge scone: the canonical reflexivity bridge, its SN, the endpoint-β operational
coherence, the reflexive-scone membership, and the canonical concrete witness.  Free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.reflexivityBridge
#assert_no_axioms FX1Poly.Typed.reflexivityBridge_isStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.reflexivityBridge_endpointBetaComputes
#assert_no_axioms FX1Poly.Typed.reflexivityBridge_memberOfReflexiveScone
#assert_no_axioms FX1Poly.Typed.reflexivityBridge_canonicalMemberAtDataValue

end FX1PolyAudit
