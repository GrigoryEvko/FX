import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionFormationCongruenceGate

/-! # FX1PolyAudit/.../HasTypeUnionFormationCongruenceGate — zero-axiom gate for the formation congruence gate

Per-declaration zero-axiom gate for the FORMATION congruence gate inhabitant (`UnionFormationCongruenceCloses`,
the first of the three gates `unionCongruenceCloserOfGates` reduces the native congruence mountain to).  Must be
free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.unionFormationCongruenceClosesGate
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.singleStepSubjectReductionModuloIntroElimGates

end FX1PolyAudit
