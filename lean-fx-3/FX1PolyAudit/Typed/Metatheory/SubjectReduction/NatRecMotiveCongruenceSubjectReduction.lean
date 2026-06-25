import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.NatRecMotiveCongruenceSubjectReduction

/-! # FX1PolyAudit/.../NatRecMotiveCongruenceSubjectReduction — zero-axiom gate for the natRec motive arm

Per-declaration zero-axiom gate for the `natRec` MOTIVE-position congruence subject reduction (the recursor mirror
of the natElim motive arm).  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.natRecMotiveCongruenceSubjectReduction

end FX1PolyAudit
