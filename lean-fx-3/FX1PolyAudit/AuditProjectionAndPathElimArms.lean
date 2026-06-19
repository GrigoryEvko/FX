import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Reducibility.Candidate.ProjectionAndPathElimArms

/-! # FX1PolyAudit/AuditProjectionAndPathElimArms
    — zero-axiom gate for the projection + path-induction FT arms (FTGEN-11, closed layer)

`fstClosedArm`, `sndClosedArm`, `idJClosedArm`, `idStrictRecClosedArm` — direct applications of the shipped
Core `…ClosedIsMember` theorems, keyed to the arc's projection / path-induction elim roles over
`canonicalDataCandidate`.  Must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.fstClosedArm
#assert_no_axioms FX1Poly.Typed.sndClosedArm
#assert_no_axioms FX1Poly.Typed.idJClosedArm
#assert_no_axioms FX1Poly.Typed.idStrictRecClosedArm

end FX1PolyAudit
