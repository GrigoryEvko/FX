import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Reducibility.Candidate.MatchElimArms

/-! # FX1PolyAudit/AuditMatchElimArms
    — zero-axiom gate for the option / either match FT arms (FTGEN-11, closed layer)

`optionMatchClosedArm`, `eitherMatchClosedArm` — direct applications of the shipped Core
`optionMatchClosedIsMember` / `eitherMatchClosedIsMember`, keyed to the arc's two-branch-match elim role over
`canonicalDataCandidate`.  Must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.optionMatchClosedArm
#assert_no_axioms FX1Poly.Typed.eitherMatchClosedArm

end FX1PolyAudit
