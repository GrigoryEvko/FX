import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimGateReassemble

/-! # FX1PolyAudit/.../ElimGateReassemble — zero-axiom gate

Per-declaration zero-axiom gate for the generic eliminator-congruence reassembly core `elimGateRowReassemble`
(the SR-DSL-5 gate's shared rebuild: drive obligations forward, rebuild via native `elim`, post-compose output
drift).  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.elimGateRowReassemble

end FX1PolyAudit
