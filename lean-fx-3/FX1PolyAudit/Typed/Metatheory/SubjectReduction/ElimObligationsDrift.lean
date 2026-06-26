import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimObligationsDrift

/-! # FX1PolyAudit/.../ElimObligationsDrift — zero-axiom gate

Per-declaration zero-axiom gate for the SR-DSL-4 obligation-list driver `premisesHoldUnderObligationsDrift`
(folds the per-obligation reclassifier over the `ObligationsDrift` relation).  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.premisesHoldUnderObligationsDrift

end FX1PolyAudit
