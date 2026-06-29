import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimGateDispatchBounded

/-! # FX1PolyAudit/.../ElimGateDispatchBounded — zero-axiom gate for the bounded elim-congruence gate

Per-declaration zero-axiom gate for the fuel-bounded eliminator-congruence gate inhabitant
(`HasTypeUnion.unionElimCongruenceClosesBoundedGate`, the elim third of the SR-WF-TIEOFF bounded congruence master,
modulo the before-usability / dimensional / not-yet-drift-shipped row residuals).  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  (The residual Props are data, no proof content.) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.unionElimCongruenceClosesBoundedGate

end FX1PolyAudit
