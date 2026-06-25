import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.DependentBranchTypeFormedFromMotive

/-! # FX1PolyAudit/.../DependentBranchTypeFormedFromMotive — the zero-axiom gate for the SR-DSL-2 type-SR content

Per-declaration zero-axiom gate for the dependent branch-type FORMEDNESS lemmas (the type-SR content the
congruence-SR motive arm reclassifies stepped branches through): the succ-branch re-basing's substitution-typing
and the `natElim` / `natRec` succ-branch type formedness from the motive's universe typing.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.succBranchRebasing_isSubstUnionTyped
#assert_no_axioms FX1Poly.Typed.natElimDependentSuccBranchType_formed_ofMotive

end FX1PolyAudit
