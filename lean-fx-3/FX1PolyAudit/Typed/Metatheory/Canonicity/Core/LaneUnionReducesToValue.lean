import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Canonicity.Core.LaneUnionReducesToValue

/-! # FX1PolyAudit/AuditLaneUnionReducesToValue
    — zero-axiom gate for the lane-generic reduces-to-value form of canonicity over the single union
    judgment

`HasTypeUnion.closedLaneDataCandidateFromNormalization` / `…closedLaneReducesToValueFromNormalization`:
uniform in the data lane (bool/nat/option/either/product/identity/pi/list), the machine-checked reduction
of closed-data head canonicity to the deferred union SN/SR arc — union SN plus along-reduction typing of the
reachable normal forms assemble `dataTaitCandidate (LaneValue target ·)` membership, and
`dataTaitCandidate.closedReducesToValue` extracts "reduces to a head value".  Must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.closedLaneDataCandidateFromNormalization
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.closedLaneReducesToValueFromNormalization

end FX1PolyAudit
