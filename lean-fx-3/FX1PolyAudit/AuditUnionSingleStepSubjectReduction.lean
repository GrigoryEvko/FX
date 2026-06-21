import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSingleStepSubjectReduction

/-! # FX1PolyAudit/AuditUnionSingleStepSubjectReduction — TYTAB-2-FT gate-2 single-step SR master audit shard

Per-declaration zero-axiom gate for the assembled single-step union subject-reduction master (gate 2 of
TYTAB-2-FT, #1697): the two named gate interfaces (`UnionDeferredRedexCloser` / `UnionCongruenceCloser`), the
up-to-`Conv` master (`singleStepSubjectReductionFromClosers`), and the classifier-PRESERVING master
(`singleStepSubjectReductionPreservingFromClosers`, the exact shape the consistency route consumes).  Every
declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.UnionDeferredRedexCloser
#assert_no_axioms FX1Poly.Typed.UnionCongruenceCloser
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.singleStepSubjectReductionFromClosers
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.singleStepSubjectReductionPreservingFromClosers

-- Gate-2 redex half DISCHARGED: the 2-way dispatcher + the deferred-redex-free single-step SR masters.
#assert_no_axioms FX1Poly.Typed.unionRootStepSubjectReductionToTypedOrCongruence
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.singleStepSubjectReductionUpToCongruence
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.singleStepSubjectReductionPreservingUpToCongruence

end FX1PolyAudit
