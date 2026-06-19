import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.Core.NatRecDataTaitMember
import FX1Poly.Core.Eliminators.Core.ListElimDataTaitMember

/-! # FX1PolyAudit/AuditRecursorDataTaitMembers
    — zero-axiom gate for the remaining recursor arms of the FTGEN-11 reconciliation

`natRecDataTaitMember` (the dependent-recursor twin) and `listElimDataTaitMember` (the list recursor, whose cons
ι is a nested `gen_app` spine) over the head-expansion-closed `dataTaitCandidate`, both with NO `headExpand`
hypothesis.  Together with `natElimDataTaitMember` they complete the recursor family of the reconciliation.  Must
be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.natRecDataTaitMember
#assert_no_axioms FX1Poly.Core.listElimDataTaitMember
-- FTGEN-11.1 propagated: natRec recursion discharged from the IH (succReductMember → succBranchSubstClosed).
-- (listElim was already recursion-self-contained: its dataTait member takes the recursion-free
-- consBranchApplication, not a consReductMember — no 11.1 work needed there.)
#assert_no_axioms FX1Poly.Core.natRecDataTaitMemberSelfContained

end FX1PolyAudit
