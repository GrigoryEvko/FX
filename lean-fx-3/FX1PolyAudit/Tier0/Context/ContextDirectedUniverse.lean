import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.ContextDirectedUniverse

/-! # FX1PolyAudit/.../ContextDirectedUniverse — zero-axiom gate for context-34 (apparatus)

Per-declaration zero-axiom gate for `context-34`'s directed-univalence APPARATUS
(`FX1Poly/Tier0/Context/ContextDirectedUniverse.lean`): the context category's universe object as a
DIRECTED-UNIVALENT WILD CATEGORY, the directed analog of `context-30`.  Directed homs (`DirectedCategoryHom`,
a bare forward morphism — NO inverse, the directed weakening of `CategoryIso`), their identity / composition /
underlying-morphism projection, the comparison map `homToFun` (path induction, no funext), the directed
univalence datum `IsDirectedUnivalentUniverseObject` (`homToFun` a two-sided equivalence), and the zero-axiom
witness that the set-level (discrete) universe object IS directed-univalent.  The full Segal / Rezk-complete
directed univalence axiom (which entails funext) is the honest `×type` deferral (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Directed categorical homs (the directed, non-invertible `A ⟶ B`)
#assert_no_axioms FX1Poly.Tier0.DirectedCategoryHom
#assert_no_axioms FX1Poly.Tier0.DirectedCategoryHom.identityHom
#assert_no_axioms FX1Poly.Tier0.DirectedCategoryHom.composeHom
#assert_no_axioms FX1Poly.Tier0.DirectedCategoryHom.toMorphism

-- The comparison map + the directed-univalence datum
#assert_no_axioms FX1Poly.Tier0.homToFun
#assert_no_axioms FX1Poly.Tier0.homToFun_refl
#assert_no_axioms FX1Poly.Tier0.IsDirectedUnivalentUniverseObject

-- The zero-axiom witness: the set-level universe object is directed-univalent
#assert_no_axioms FX1Poly.Tier0.discreteUniverseObject_isDirectedUnivalent

-- Honesty markers + smoke
#assert_no_axioms FX1Poly.Tier0.fxContextDirectedUniverse_hasDirectedUnivalence
#assert_no_axioms FX1Poly.Tier0.fxContextDirectedUniverse_hasFullSegalDirectedUA
#assert_no_axioms FX1Poly.Tier0.discreteUniverseObject_funToId_homToFun_smoke

end FX1PolyAudit
