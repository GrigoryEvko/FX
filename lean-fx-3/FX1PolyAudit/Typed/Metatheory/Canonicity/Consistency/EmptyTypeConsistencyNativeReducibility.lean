import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Canonicity.Consistency.EmptyTypeConsistencyNativeReducibility

/-! # FX1PolyAudit/.../EmptyTypeConsistencyNativeReducibility — the UNCONDITIONAL consistency-leg gate (#1697)

Per-declaration zero-axiom gate for the native consistency delivered by the **reducibility bypass**: a closed
union derivation at the empty type yields (via the generic fundamental theorem) a bounded-reducible member, the
candidate bridge carries it into the empty Tait candidate, and the reverse neutral reflection
(`IsNeutral.noClosedSubstImage`) refutes it.  No gate-2 congruence closer, no universe-flag-uniqueness, no
path-free bookkeeping — strictly stronger than `coreFragmentConsistencyFromElimCongruenceCloserSnDischarged`.

Must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.emptyTypeConsistency
#assert_no_axioms FX1Poly.Typed.HasTypeUnionNativeOnly.emptyTypeConsistency

end FX1PolyAudit
