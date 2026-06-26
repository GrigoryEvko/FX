import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.RecursorElimObligationsDrift

/-! # FX1PolyAudit/.../RecursorElimObligationsDrift — zero-axiom gate

Per-declaration zero-axiom gate for the binder-extended recursor (`natElim` / `natRec`) `ObligationsDrift`
constructions — the only eliminators whose step-branch obligation context reads the motive, exercising the
`consContextHeadConv` driver arm (head-binding conversion + classifier reclassification with directly-supplied
after-formedness).  Includes the typed-strength universe-membership preservation helper.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.universeMembershipPreservedUnderStep
#assert_no_axioms FX1Poly.Typed.natElimObligationsDriftUnderArgStep
#assert_no_axioms FX1Poly.Typed.natRecElimObligationsDriftUnderArgStep

end FX1PolyAudit
