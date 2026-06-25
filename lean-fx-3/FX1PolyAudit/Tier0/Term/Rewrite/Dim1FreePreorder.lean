import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Rewrite.Dim1FreePreorder

/-! # FX1PolyAudit/AuditTier0TermDim1Rewrite — zero-axiom gate for term-2 (dim-1 rewrite preorder)

Per-declaration zero-axiom gate for `FX1Poly/Tier0/Term/Rewrite/Dim1FreePreorder.lean`: the free
reflexive-transitive closure as the dim-1 rewrite preorder — the cocone model `ReflTransCocone`, the
free-preorder universal property `ReflTransClosure.mediate` with its homomorphism / universal-triangle
laws (`mediate_refl` / `mediate_single` / `mediate_head`) + `mediate_unique`, the initial cocone
`selfCocone` + `mediate_selfCocone`, the thin-category laws
(`leftIdentity` / `rightIdentity` / `assoc`), the bundle instance `StepOver.freelyGenerated` +
`toFreelyGenerated`, and the kernel reduction relation's own UP `StepStar.mediateOverFxIotaBundle`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The cocone model + the free-preorder universal property (existence + homomorphism + triangle + uniqueness)
#assert_no_axioms FX1Poly.Core.ReflTransCocone
#assert_no_axioms FX1Poly.Core.ReflTransClosure.mediate
#assert_no_axioms FX1Poly.Core.ReflTransClosure.mediate_refl
#assert_no_axioms FX1Poly.Core.ReflTransClosure.mediate_single
#assert_no_axioms FX1Poly.Core.ReflTransClosure.mediate_head
#assert_no_axioms FX1Poly.Core.ReflTransClosure.mediate_unique

-- The initial cocone (the closure mediates into itself as the identity)
#assert_no_axioms FX1Poly.Core.ReflTransClosure.selfCocone
#assert_no_axioms FX1Poly.Core.ReflTransClosure.mediate_selfCocone

-- The (thin) category laws on composition
#assert_no_axioms FX1Poly.Core.ReflTransClosure.leftIdentity
#assert_no_axioms FX1Poly.Core.ReflTransClosure.rightIdentity
#assert_no_axioms FX1Poly.Core.ReflTransClosure.assoc

-- The bundle instance: StepOver as the 1-cell generators + the kernel reduction relation's own UP
#assert_no_axioms FX1Poly.Core.StepOver.freelyGenerated
#assert_no_axioms FX1Poly.Core.StepOver.toFreelyGenerated
#assert_no_axioms FX1Poly.Core.StepStar.mediateOverFxIotaBundle

end FX1PolyAudit
