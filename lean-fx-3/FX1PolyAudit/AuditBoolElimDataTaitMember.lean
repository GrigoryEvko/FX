import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.Core.BoolElimDataTaitMember

/-! # FX1PolyAudit/AuditBoolElimDataTaitMember
    — zero-axiom gate for the FTGEN-11 reconciliation proof-of-concept

`IsNeutral.closedUnderStepStar` (neutrality preserved along a reduction chain),
`dataTaitCandidate.memberOfStronglyNormalizingNeutral` (SN neutral is a data-candidate member), and
`boolElimDataTaitMember` (the `boolElim` arm over the head-expansion-closed `dataTaitCandidate`, with NO
`headExpand` hypothesis — the demonstrator that the elim arms re-base onto the formation-side candidate).  Must
be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.IsNeutral.closedUnderStepStar
#assert_no_axioms FX1Poly.Core.dataTaitCandidate.memberOfStronglyNormalizingNeutral
#assert_no_axioms FX1Poly.Core.boolElimDataTaitMember

end FX1PolyAudit
