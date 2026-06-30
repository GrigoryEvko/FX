import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.WellFormedCongruenceClosesGeneric

/-! # FX1PolyAudit.Typed.Metatheory.SubjectReduction.WellFormedCongruenceClosesGeneric — zero-axiom gate

Per-declaration zero-axiom gate for the well-formed-context fuel-bounded congruence master (SR-WF-TIEOFF #1784):
the three well-formed congruence gates, the six-arm master from those gates, and the residual closer it inhabits.
Each must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.UnionFormationCongruenceClosesBoundedWf
#assert_no_axioms FX1Poly.Typed.UnionIntroCongruenceClosesBoundedWf
#assert_no_axioms FX1Poly.Typed.UnionElimCongruenceClosesBoundedWf
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.congruenceClosesGenericAuxBoundedWf
#assert_no_axioms FX1Poly.Typed.unionCongruenceClosesBoundedWfOfGates

end FX1PolyAudit
