import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Ledger.Bridge.BridgeRelationalScone

/-! # FX1PolyAudit/AuditBridgeRelationalScone — NATIVE-57 relational-Bridge-scone audit shard

Per-declaration zero-axiom gate for the relational Bridge scone: the relation-carrying member
predicate, the internalized free-theorem extraction, the SN/intro projections, the
carrier-congruence, and the inhabited/empty teeth.  Free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.bridgeRelationalCandidate
#assert_no_axioms FX1Poly.Typed.bridgeRelationalCandidate.intro
#assert_no_axioms FX1Poly.Typed.bridgeRelationalCandidate_extractsRelation
#assert_no_axioms FX1Poly.Typed.bridgeRelationalCandidate_memberIsStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.bridgeRelationalCandidate_congrInCarrier
#assert_no_axioms FX1Poly.Typed.bridgeRelationalScone_inhabitedAtRelatedEndpoints
#assert_no_axioms FX1Poly.Typed.bridgeRelationalScone_emptyAtUnrelatedEndpoints
#assert_no_axioms FX1Poly.Typed.bridgeRelationalScone_tracksCarrierRelation

end FX1PolyAudit
