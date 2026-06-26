import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.ObligationReclassifiesUnderDrift

/-! # FX1PolyAudit/.../ObligationReclassifiesUnderDrift — zero-axiom gate

Per-declaration zero-axiom gate for the SR-DSL-4 atom (`obligationReclassifiesUnderDrift`) and its
subject-reduction-along-a-chain helper.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.subjectReductionAlongChainAtFixedClassifier
#assert_no_axioms FX1Poly.Typed.obligationReclassifiesUnderDrift

end FX1PolyAudit
