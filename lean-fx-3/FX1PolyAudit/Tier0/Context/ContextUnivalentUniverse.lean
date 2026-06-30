import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.ContextUnivalentUniverse

/-! # FX1PolyAudit/.../ContextUnivalentUniverse — zero-axiom gate for context-30

Per-declaration zero-axiom gate for `context-30`'s deliverable
(`FX1Poly/Tier0/Context/ContextUnivalentUniverse.lean`): the context category's universe object as a
UNIVALENT WILD CATEGORY in the funext-free CATEGORICAL sense (Cavallo–Höfer `CUA`).  Categorical isos
(`CategoryIso`, inverses up to EQUALITY), the comparison map `idToIso` (path induction, no funext), the
univalence datum `IsUnivalentUniverseObject` (`idToIso` a two-sided equivalence), and the zero-axiom witness
that the set-level (discrete) universe object IS univalent.  The full univalence axiom `UA` (which entails
funext) is the honest `×type` deferral (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Categorical isomorphisms (the funext-free `A ≅ B`)
#assert_no_axioms FX1Poly.Tier0.CategoryIso
#assert_no_axioms FX1Poly.Tier0.CategoryIso.identityIso
#assert_no_axioms FX1Poly.Tier0.CategoryIso.symm
#assert_no_axioms FX1Poly.Tier0.CategoryIso.toIsIsomorphism

-- The comparison map + the univalence datum
#assert_no_axioms FX1Poly.Tier0.idToIso
#assert_no_axioms FX1Poly.Tier0.idToIso_refl
#assert_no_axioms FX1Poly.Tier0.IsUnivalentUniverseObject

-- The zero-axiom witness: the set-level universe object is univalent
#assert_no_axioms FX1Poly.Tier0.discreteUniverseObject
#assert_no_axioms FX1Poly.Tier0.discreteUniverseObject_isUnivalent

-- Honesty markers + smoke
#assert_no_axioms FX1Poly.Tier0.fxContextUniverse_hasCategoricalUnivalence
#assert_no_axioms FX1Poly.Tier0.fxContextUniverse_hasUnivalenceAxiom
#assert_no_axioms FX1Poly.Tier0.discreteUniverseObject_isoToId_idToIso_smoke

end FX1PolyAudit
