import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.ComprehensionSigma

/-! # FX1PolyAudit/AuditTier0ContextComprehension — zero-axiom gate for context-1's comprehension + Σ

Per-declaration zero-axiom gate for `context-1`'s comprehension + Frobenius-Σ
deliverable (`FX1Poly/Tier0/Context/ComprehensionSigma.lean`): the new
Beck–Chevalley substitution-stability square `SubstVec.cons_compose` and the
gathered comprehension witness `fxContextComprehension` (which transitively wires
the shipped SUBSTVEC-4 v-law / p-law / universal property plus the new square).
Every declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.SubstVec.cons_compose
#assert_no_axioms FX1Poly.Tier0.fxContextComprehension

end FX1PolyAudit
