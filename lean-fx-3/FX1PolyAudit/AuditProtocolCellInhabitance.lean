import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.ProtocolCellInhabitance

/-! # AuditProtocolCellInhabitance — zero-axiom gate for CELLSORT-REWIRE brick 1

The session/channel generators inhabit the `.protocol` cell sort, with
protocol-sorted channel children.  Each pin must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.sessionSend_inhabitsProtocolSort
#assert_no_axioms FX1Poly.Core.sessionRecv_inhabitsProtocolSort
#assert_no_axioms FX1Poly.Core.sessionSelect_inhabitsProtocolSort
#assert_no_axioms FX1Poly.Core.sessionOffer_inhabitsProtocolSort
#assert_no_axioms FX1Poly.Core.sessionClose_inhabitsProtocolSort
#assert_no_axioms FX1Poly.Core.channelSplit_inhabitsProtocolSort
#assert_no_axioms FX1Poly.Core.channelJoin_inhabitsProtocolSort

#assert_no_axioms FX1Poly.Core.sessionSend_channelChildIsProtocol
#assert_no_axioms FX1Poly.Core.channelJoin_bothChildrenAreProtocol
#assert_no_axioms FX1Poly.Core.channelCapacity_staysTermSort

end FX1PolyAudit
