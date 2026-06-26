import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.StepStarCellCongruence

/-! # FX1PolyAudit/.../StepStarCellCongruence — zero-axiom gate

Per-declaration zero-axiom gate for the DIRECTED (`StepStar`) cell-congruence helpers that SR-DSL-2's
`templateStepStarUnderChildStep` assembles (the directed twins of `Conv.subst0` / `Conv.substPair` /
`Conv.piTyCode_cong` / `Conv.weakenBy*`).  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.StepStar.subst0Both
#assert_no_axioms FX1Poly.Core.StepStar.substPairAll
#assert_no_axioms FX1Poly.Core.StepStar.weakenByStar
#assert_no_axioms FX1Poly.Core.StepStar.weakenBodyUnderOneBinderByStar
#assert_no_axioms FX1Poly.Core.StepStar.weakenBodyUnderTwoBindersByStar
#assert_no_axioms FX1Poly.Typed.StepStar.piTyCodeDomainStar
#assert_no_axioms FX1Poly.Typed.StepStar.piTyCodeCodomainStar
#assert_no_axioms FX1Poly.Typed.StepStar.piTyCode_cong

end FX1PolyAudit
