import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Term.Action.FoldUniqueness

/-! # FX1PolyAudit/AuditAxisTermFoldUniqueness — zero-axiom gate for term-1 (uniqueness leg)

Per-declaration zero-axiom gate for `FX1Poly/Axis/Term/Action/FoldUniqueness.lean`: the recursor
universal property for the RawTerm-valued action-fold — the `IsFoldHomomorphism` bundle, the mutual
`unique_term`/`unique_children` (any fold-homomorphism agrees with `fold`/`foldChildren`), the existence
witness `foldHomomorphism` (`fold` is a fold-homomorphism), and the packaged corollaries
(`eq_fold`, `foldHomomorphism_unique`, `fold_hom_ext`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.IsFoldHomomorphism
#assert_no_axioms FX1Poly.Core.IsFoldHomomorphism.unique_term
#assert_no_axioms FX1Poly.Core.IsFoldHomomorphism.unique_children
#assert_no_axioms FX1Poly.Core.foldHomomorphism
#assert_no_axioms FX1Poly.Core.IsFoldHomomorphism.eq_fold
#assert_no_axioms FX1Poly.Core.foldHomomorphism_unique
#assert_no_axioms FX1Poly.Core.fold_hom_ext

end FX1PolyAudit
