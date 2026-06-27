import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.IntroGateReassembleBounded

/-! # FX1PolyAudit/.../IntroGateReassembleBounded — zero-axiom gate for the bounded intro reassembly

Per-declaration zero-axiom gate for the fuel-bounded introducer-congruence reassembly
(`introGateRowReassembleBounded`).  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.introGateRowReassembleBounded

end FX1PolyAudit
