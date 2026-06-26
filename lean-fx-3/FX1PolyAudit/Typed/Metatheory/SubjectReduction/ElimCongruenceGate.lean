import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimCongruenceGate

/-! # FX1PolyAudit/.../ElimCongruenceGate — zero-axiom gate

Per-declaration zero-axiom gate for `elimCongruenceClosesFromBranches` — the inhabitation of the SR-DSL-5 ELIM
congruence gate `UnionElimCongruenceCloses` by dispatch over the eleven per-generator branch lemmas (the
`elimRuleOf_cases` table hit selects the row).  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.elimCongruenceClosesFromBranches

end FX1PolyAudit
