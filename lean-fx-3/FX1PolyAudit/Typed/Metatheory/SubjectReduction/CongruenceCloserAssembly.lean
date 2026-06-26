import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.CongruenceCloserAssembly

/-! # FX1PolyAudit.Typed.Metatheory.SubjectReduction.CongruenceCloserAssembly — zero-axiom gate (SR-DSL-5)

Per-declaration zero-axiom gate for the assembled single-step congruence closer: the whole native congruence
mountain reduced to the two honest premises (the `pathLam` intro branch + the single-step-SR self-reference),
via `unionCongruenceCloserOfGates` applied to the three shipped gate inhabitants. Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.unionCongruenceCloserOfPathLam

end FX1PolyAudit
