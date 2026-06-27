import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionFormationCongruenceBoundedGate

/-! # FX1PolyAudit/.../HasTypeUnionFormationCongruenceBoundedGate — zero-axiom gate for the FUEL-BOUNDED formation gate

Per-declaration zero-axiom gate for the fuel-bounded formation congruence gate inhabitant
(`UnionFormationCongruenceClosesBounded`, the formation third of `congruenceClosesGenericAuxBounded`).  Must be free
of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.unionFormationCongruenceClosesBoundedGate

end FX1PolyAudit
