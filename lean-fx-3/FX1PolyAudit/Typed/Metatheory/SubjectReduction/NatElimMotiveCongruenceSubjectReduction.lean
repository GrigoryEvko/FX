import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.NatElimMotiveCongruenceSubjectReduction

/-! # FX1PolyAudit/.../NatElimMotiveCongruenceSubjectReduction — zero-axiom gate for the first motive arm

Per-declaration zero-axiom gate for `natZeroTyped` and the `natElim` MOTIVE-position congruence subject
reduction (the first complete hard eliminator-congruence arm: branch drift + drifted-classifier formedness +
context conversion).  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.natZeroTyped
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.natElimMotiveCongruenceSubjectReduction

end FX1PolyAudit
