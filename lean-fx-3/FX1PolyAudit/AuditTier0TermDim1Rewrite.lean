import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Rewrite.Dim1FreePreorder

/-! # FX1PolyAudit/AuditTier0TermDim1Rewrite — zero-axiom gate for term-2 (dim-1 rewrite preorder)

Per-declaration zero-axiom gate for `FX1Poly/Tier0/Term/Rewrite/Dim1FreePreorder.lean`: the free
reflexive-transitive closure as the dim-1 rewrite preorder — the cocone model `ReflTransCocone`, the
free-preorder universal property `ReflTransClosure.mediate` + `mediate_unique`, the initial cocone
`selfCocone` + `mediate_selfCocone`, the thin-category laws
(`leftIdentity` / `rightIdentity` / `assoc`), and the bundle instance `StepOver.freelyGenerated` +
`toFreelyGenerated`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The cocone model + the free-preorder universal property
#assert_no_axioms FX1Poly.Core.ReflTransCocone
#assert_no_axioms FX1Poly.Core.ReflTransClosure.mediate
#assert_no_axioms FX1Poly.Core.ReflTransClosure.mediate_unique

-- The initial cocone (the closure mediates into itself as the identity)
#assert_no_axioms FX1Poly.Core.ReflTransClosure.selfCocone
#assert_no_axioms FX1Poly.Core.ReflTransClosure.mediate_selfCocone

-- The (thin) category laws on composition
#assert_no_axioms FX1Poly.Core.ReflTransClosure.leftIdentity
#assert_no_axioms FX1Poly.Core.ReflTransClosure.rightIdentity
#assert_no_axioms FX1Poly.Core.ReflTransClosure.assoc

-- The bundle instance: StepOver as the 1-cell generators
#assert_no_axioms FX1Poly.Core.StepOver.freelyGenerated
#assert_no_axioms FX1Poly.Core.StepOver.toFreelyGenerated

end FX1PolyAudit
