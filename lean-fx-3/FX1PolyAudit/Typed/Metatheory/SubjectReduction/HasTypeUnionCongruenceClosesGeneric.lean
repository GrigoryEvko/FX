import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionCongruenceClosesGeneric

/-! # FX1PolyAudit/.../HasTypeUnionCongruenceClosesGeneric — zero-axiom gate for the SR-DSL-5 skeleton

Per-declaration zero-axiom gate for the off-`emptyTypeCell` generic congruence master: the single-step-SR
self-reference + the three congruence gates + `congruenceClosesGenericAux` + the `UnionCongruenceCloser`
reduction.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.UnionChildSubjectReduction
#assert_no_axioms FX1Poly.Typed.UnionFormationCongruenceCloses
#assert_no_axioms FX1Poly.Typed.UnionIntroCongruenceCloses
#assert_no_axioms FX1Poly.Typed.UnionElimCongruenceCloses
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.congruenceClosesGenericAux
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.unionCongruenceCloserOfGates

end FX1PolyAudit
