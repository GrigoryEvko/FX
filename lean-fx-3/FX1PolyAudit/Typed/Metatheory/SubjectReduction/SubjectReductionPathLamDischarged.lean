import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.SubjectReductionPathLamDischarged

/-! # FX1PolyAudit.Typed.Metatheory.SubjectReduction.SubjectReductionPathLamDischarged — zero-axiom gate

The per-declaration `#assert_no_axioms` gate for the SR arc with the `pathLam` node discharged (A1-SR-RECLOSE):
the unconditional introducer-congruence gate, the single-step congruence closer modulo only the well-founded
self-reference, and the two single-step union SR masters (up-to-`Conv` and classifier-preserving) modulo only
that self-reference. -/

namespace FX1PolyAudit

-- ★ The whole introducer-congruence gate, unconditional (all 17 rows, pathLam discharged)
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.unionIntroCongruenceClosesUnconditional

-- ★ The single-step congruence closer modulo only UnionChildSubjectReduction (pathLam no longer a premise)
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.unionCongruenceCloserModuloChildSR

-- ★ The single-step union SR masters modulo only the self-reference
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.singleStepSubjectReductionModuloChildSR
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.singleStepSubjectReductionPreservingModuloChildSR

end FX1PolyAudit
