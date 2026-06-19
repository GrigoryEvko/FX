import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.Core.NatElimDataTaitMember

/-! # FX1PolyAudit/AuditNatElimDataTaitMember
    — zero-axiom gate for the FTGEN-11 RECURSIVE-eliminator reconciliation

`natElimDataTaitMember` (the `natElim` arm over the head-expansion-closed `dataTaitCandidate`, with NO
`headExpand` hypothesis and the RECURSIVE successor-reduct premise threaded over that candidate) — the
demonstrator that the FTGEN-11 reconciliation handles recursion, not just the trivial `boolElim` match.  Must
be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.natElimDataTaitMember

end FX1PolyAudit
