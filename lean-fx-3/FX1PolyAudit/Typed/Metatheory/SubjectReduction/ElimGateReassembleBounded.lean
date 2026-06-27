import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimGateReassembleBounded

/-! # FX1PolyAudit/.../ElimGateReassembleBounded — zero-axiom gate for the bounded elim reassembly

Per-declaration zero-axiom gate for the fuel-bounded eliminator-congruence reassembly
(`elimGateRowReassembleBounded`).  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.elimGateRowReassembleBounded

end FX1PolyAudit
