import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.ObligationReclassifiesUnderDriftBounded

/-! # FX1PolyAudit/.../ObligationReclassifiesUnderDriftBounded — zero-axiom gate for the bounded single-step subject-SR atom

Per-declaration zero-axiom gate for the fuel-bounded single-step subject-reduction atom
(`subjectReductionAtFixedClassifierStepBelow`, the load-bearing piece of the SR-WF-TIEOFF intro bounded
congruence driver's `cons` arm).  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.subjectReductionAtFixedClassifierStepBelow

end FX1PolyAudit
