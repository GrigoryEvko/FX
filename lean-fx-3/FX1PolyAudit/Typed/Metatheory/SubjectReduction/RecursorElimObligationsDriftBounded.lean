import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.RecursorElimObligationsDriftBounded

/-! # FX1PolyAudit/.../RecursorElimObligationsDriftBounded — zero-axiom gate for the bounded recursor drift

Per-declaration zero-axiom gate for the fuel-bounded `ObligationsDriftBelow` builders of the recursors
(`natElim` / `natRec`) plus the `natZero` typing and the bounded universe-membership preservation.  Must be free
of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.natZeroTypedInContext
#assert_no_axioms FX1Poly.Typed.universeMembershipPreservedUnderStepBelow
#assert_no_axioms FX1Poly.Typed.natElimObligationsDriftUnderArgStepBounded
#assert_no_axioms FX1Poly.Typed.natRecElimObligationsDriftUnderArgStepBounded

end FX1PolyAudit
