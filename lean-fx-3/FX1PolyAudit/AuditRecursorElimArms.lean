import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Reducibility.Candidate.RecursorElimArms

/-! # FX1PolyAudit/AuditRecursorElimArms
    — zero-axiom gate for the recursive-eliminator FT arms (FTGEN-11): natElim / natRec / listElim

`natElimRecursiveElim`, `natRecRecursiveElim`, `listElimRecursiveElim` — direct applications of the shipped
Core `…ReducibleScrutineeMember` Acc-induction theorems, keyed to the arc's recursive-elim role over
`canonicalDataCandidate`.  Must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.natElimRecursiveElim
#assert_no_axioms FX1Poly.Typed.natRecRecursiveElim
#assert_no_axioms FX1Poly.Typed.listElimRecursiveElim

end FX1PolyAudit
