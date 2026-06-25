import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Canonicity.Forms.ClosedBoolCanonicityFromFundamental

/-! # FX1PolyAudit/.../ClosedBoolCanonicityFromFundamental — the UNCONDITIONAL bool-canonicity gate (FTGEN-14)

Per-declaration zero-axiom gate for closed bool canonicity delivered by the **reducibility bypass** (the first
data instance of FTGEN-14): a closed union derivation at `boolTypeCell` yields (via the generic fundamental
theorem) a bounded-reducible member, the bool candidate bridge carries it into `dataTaitCandidate boolIsValue`,
and the value disjunct (after refuting neutral via `IsNeutral.noClosedSubstImage`) reflects back to a `boolTrue`
/`boolFalse` normal form.  The bool generalization of `HasTypeUnion.emptyTypeConsistency`.

Must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.boolValueReflectThroughClosingWeakening
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.closedBoolCanonicity

end FX1PolyAudit
