import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Reducibility.Candidate.DataElimReconciledArms

/-! # FX1PolyAudit/AuditDataElimReconciledArms
    — zero-axiom gate for the FTGEN-11 intro+elim-compose-on-one-candidate theorems

`boolReducibilityComposesIntroElim` (bool / two-branch match) and `idJReducibilityComposesIntroElim` (idJ /
path-induction): each feeds a data-INTRODUCTION member (a constructor value, via
`dataTaitCandidate.memberOfValue`) into the corresponding data-ELIMINATION theorem (`*DataTaitMember`), both
speaking the single `dataElimReducibilityCandidate` (= `dataTaitCandidate`).  The arc-level payoff of the
FTGEN-11 reconciliation.  Must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.boolReducibilityComposesIntroElim
#assert_no_axioms FX1Poly.Typed.idJReducibilityComposesIntroElim

end FX1PolyAudit
