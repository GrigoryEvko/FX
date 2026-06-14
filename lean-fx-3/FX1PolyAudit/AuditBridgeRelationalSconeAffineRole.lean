import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Ledger.Bridge.BridgeRelationalSconeAffineRole

/-! # FX1PolyAudit/AuditBridgeRelationalSconeAffineRole — NATIVE-59 affine-role audit shard

Per-declaration zero-axiom gate for the affine premise's semantic role in the relational Bridge
scone: endpoint distinctness, the off-diagonal endpoint-β computations, off-diagonal membership, the
count-1/count-0 grade facts, the count-2 rejection, and the separation bundle.  Free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.intervalZero_ne_intervalOne
#assert_no_axioms FX1Poly.Typed.affineIdentityPath_endpointZeroComputes
#assert_no_axioms FX1Poly.Typed.affineIdentityPath_endpointOneComputes
#assert_no_axioms FX1Poly.Typed.affineIdentityPath_sconeMemberOffDiagonal
#assert_no_axioms FX1Poly.Typed.affineBody_occurrenceCountIsOne
#assert_no_axioms FX1Poly.Typed.constantBody_occurrenceCountIsZero
#assert_no_axioms FX1Poly.Typed.duplicatingBody_failsAffinePremise
#assert_no_axioms FX1Poly.Typed.affinePremise_separatesDiagonalFromRelational

end FX1PolyAudit
