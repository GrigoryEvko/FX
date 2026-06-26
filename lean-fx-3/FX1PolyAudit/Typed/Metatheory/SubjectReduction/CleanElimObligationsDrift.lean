import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.CleanElimObligationsDrift

/-! # FX1PolyAudit/.../CleanElimObligationsDrift — zero-axiom gate

Per-declaration zero-axiom gate for the clean-eliminator `ObligationsDrift` construction
(`appObligationsDriftUnderArgStep`) — the end-to-end SR-DSL-4 pipeline validation on `app`.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.appObligationsDriftUnderArgStep
#assert_no_axioms FX1Poly.Typed.pathAppObligationsDriftUnderArgStep
#assert_no_axioms FX1Poly.Typed.fstObligationsDriftUnderArgStep
#assert_no_axioms FX1Poly.Typed.sndObligationsDriftUnderArgStep

end FX1PolyAudit
