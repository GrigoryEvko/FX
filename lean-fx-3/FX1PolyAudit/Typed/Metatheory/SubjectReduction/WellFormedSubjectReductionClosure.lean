import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.WellFormedSubjectReductionClosure

/-! # FX1PolyAudit.Typed.Metatheory.SubjectReduction.WellFormedSubjectReductionClosure — zero-axiom gate

Per-declaration zero-axiom gate for the well-formed-context single- and multi-step subject-reduction tie-off frame
(SR-WF-TIEOFF #1784): the `WfContextUnion`-carrying bounded / universal self-reference, the closure frame, the
fuel induction (redex half discharged), and the final single- and multi-step SR masters modulo the residual
well-formed congruence master.  Each must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.UnionChildSubjectReductionBelowWf
#assert_no_axioms FX1Poly.Typed.UnionChildSubjectReductionWf
#assert_no_axioms FX1Poly.Typed.UnionChildSubjectReductionWf.toBelowWf
#assert_no_axioms FX1Poly.Typed.UnionChildSubjectReductionBelowWf.weakenWf
#assert_no_axioms FX1Poly.Typed.unionChildSubjectReductionWfOfAllBelow
#assert_no_axioms FX1Poly.Typed.UnionCongruenceClosesBoundedWf
#assert_no_axioms FX1Poly.Typed.unionChildSubjectReductionBelowWfOfCongruenceCloser
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.singleStepSubjectReductionWf
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.singleStepSubjectReductionPreservingWf
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.multiStepSubjectReductionPreservingWf

end FX1PolyAudit
