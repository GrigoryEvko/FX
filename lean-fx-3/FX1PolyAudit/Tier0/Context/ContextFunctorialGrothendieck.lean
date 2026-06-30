import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.ContextFunctorialGrothendieck

/-! # FX1PolyAudit/.../ContextFunctorialGrothendieck — zero-axiom gate for context-37

Per-declaration zero-axiom gate for `context-37`'s deliverable
(`FX1Poly/Tier0/Context/ContextFunctorialGrothendieck.lean`): the FUNCTORIAL directed Grothendieck
classification — `straighten` / `unstraighten` upgraded to mutually-inverse FUNCTORS between the category
`CovFib(C)` of covariant fibrations and the functor category `[C, U]` into the directed universe, a STRICT
ISOMORPHISM OF CATEGORIES.  Natural transformations of functors into `U` + the functor category `[C, U]`,
morphisms of covariant fibrations + the category `CovFib(C)` (both `RawCategory`s, laws `rfl` via β/η on
components + proof-irrelevant naturality), straightening / unstraightening on morphisms with their `rfl`
round-trips, the two classification functors, and the two composite-identity theorems exhibiting the
isomorphism (BY `rfl`).  The full ∞-cosmos / homotopy-coherent equivalence (which needs funext) is the honest
`×type` deferral (`= false`); the Core table-native row is the honest cross-axis sibling (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Natural transformations of functors into U + the functor category [C, U]
#assert_no_axioms FX1Poly.Tier0.DirectedUniverseNatTrans
#assert_no_axioms FX1Poly.Tier0.DirectedUniverseNatTrans.identityTrans
#assert_no_axioms FX1Poly.Tier0.DirectedUniverseNatTrans.vcomp
#assert_no_axioms FX1Poly.Tier0.directedUniverseFunctorCategory

-- Morphisms of covariant fibrations + the category CovFib(C)
#assert_no_axioms FX1Poly.Tier0.CovariantFibrationMorphism
#assert_no_axioms FX1Poly.Tier0.CovariantFibrationMorphism.identityMorphism
#assert_no_axioms FX1Poly.Tier0.CovariantFibrationMorphism.composeMorphism
#assert_no_axioms FX1Poly.Tier0.covariantFibrationCategory

-- Straightening / unstraightening on morphisms + the round-trips
#assert_no_axioms FX1Poly.Tier0.CovariantFibration.straightenMorphism
#assert_no_axioms FX1Poly.Tier0.CovariantFibration.unstraightenMorphism
#assert_no_axioms FX1Poly.Tier0.CovariantFibration.unstraightenMorphism_straightenMorphism
#assert_no_axioms FX1Poly.Tier0.CovariantFibration.straightenMorphism_unstraightenMorphism

-- The classification functors + the strict isomorphism of categories
#assert_no_axioms FX1Poly.Tier0.CovariantFibration.straightenFunctor
#assert_no_axioms FX1Poly.Tier0.CovariantFibration.unstraightenFunctor
#assert_no_axioms FX1Poly.Tier0.CovariantFibration.straightenFunctor_unstraightenFunctor_id
#assert_no_axioms FX1Poly.Tier0.CovariantFibration.unstraightenFunctor_straightenFunctor_id

-- Honesty markers + smokes
#assert_no_axioms FX1Poly.Tier0.fxFunctorialGrothendieck_hasStrictCategoryIsomorphism
#assert_no_axioms FX1Poly.Tier0.fxFunctorialGrothendieck_hasFunctorialClassification
#assert_no_axioms FX1Poly.Tier0.fxFunctorialGrothendieck_hasFullInfinityCosmosEquivalence
#assert_no_axioms FX1Poly.Tier0.fxFunctorialGrothendieck_isOverCoreIotaTable
#assert_no_axioms FX1Poly.Tier0.directedUniverseFunctorCategory_identityLeft_smoke
#assert_no_axioms FX1Poly.Tier0.straightenMorphism_identity_smoke

end FX1PolyAudit
