import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.IntroGateDispatch

/-! # FX1PolyAudit.Typed.Metatheory.SubjectReduction.IntroGateDispatch — zero-axiom gate (SR-DSL-5 intro dispatch)

Per-declaration zero-axiom gate for the introducer-congruence gate dispatch: the isolated `pathLam` branch
premise and the gate inhabitant that dispatches the sixteen shipped branches + the `pathLam` premise over
`introRuleOf_cases`. Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.PathLamIntroGateBranchCloses
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.unionIntroCongruenceClosesOfPathLam

end FX1PolyAudit
