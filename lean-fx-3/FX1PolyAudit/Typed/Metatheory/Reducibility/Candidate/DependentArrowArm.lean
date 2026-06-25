import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Reducibility.Candidate.DependentArrowArm

/-! # FX1PolyAudit/AuditDependentArrowArm
    — zero-axiom gate for the function-space intro + elim FT arms (FTGEN-8 / FTGEN-10)

`dependentProductCandidate` (the Π shape candidate), `dependentProductElim` (FTGEN-10, the app arm),
`dependentProductIntro` (FTGEN-8, the λ abstraction arm) — direct applications of the shipped Core
`DependentArrowCandidate.application` / `.abstraction`; must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.dependentProductCandidate
#assert_no_axioms FX1Poly.Typed.dependentProductElim
#assert_no_axioms FX1Poly.Typed.dependentProductIntro

end FX1PolyAudit
