import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Invertibility.FiniteNoGap

/-! # FX1PolyAudit/Polygraph/Invertibility/FiniteNoGap — zero-axiom gate

Per-declaration zero-axiom gate for HL23 Cor 4.35: the guarded `inductiveClosure_of_acc`, the well-founded
coinductive ⊆ inductive collapse, and the fixpoints-agree `↔` (the kernel instantiation is gated in
`FX1PolyAudit/Core/Metatheory/Normalization/StrongNorm/StrongNormalizationBridge.lean`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega` — in particular the `Acc`-recursion in `inductiveClosure_of_acc` and `WellFounded.apply` must not
leak `propext`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Invertibility.inductiveClosure_of_acc
#assert_no_axioms FX1Poly.Polygraph.Invertibility.coinductiveClosure_subset_inductiveClosure_of_wellFounded
#assert_no_axioms FX1Poly.Polygraph.Invertibility.fixpoints_agree_of_wellFounded

end FX1PolyAudit
