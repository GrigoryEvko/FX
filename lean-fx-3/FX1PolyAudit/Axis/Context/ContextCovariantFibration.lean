import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.ContextCovariantFibration

/-! # FX1PolyAudit/.../ContextCovariantFibration — zero-axiom gate for context-35

Per-declaration zero-axiom gate for `context-35`'s deliverable
(`FX1Poly/Axis/Context/ContextCovariantFibration.lean`): the DIRECTED Grothendieck classification — covariant
(cocartesian / opcartesian) fibrations over a base context category ≃ functors into the directed universe, the
directed mirror of "families ≃ display maps" and the covariant analog of "fibrations ≃ families".  The small
directed universe (codes + forward functions), the `CovariantFibration` structure (fiber + functorial
cocartesian lift), `straighten` / `unstraighten` with their `rfl` round-trips (the classification equivalence at
the strict level), the Grothendieck total category `∫F` + projection opfibration + chosen cocartesian lift, the
cocartesian universal property (initial among lifts: existence + uniqueness, via proof-irrelevant lies-over
witnesses), the decidable-classification witness, the bridge to `context-34`'s `DirectedCategoryHom`, and the
canonical constant-fibration inhabitant.  The full ∞-cosmos / homotopy-coherent straightening (which needs
funext) is the honest `×type` deferral (`= false`); the Core table-native row is the honest cross-axis sibling
(`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The small directed universe + the functor-into-universe abbreviation
#assert_no_axioms FX1Poly.Axis.DirectedUniverseData
#assert_no_axioms FX1Poly.Axis.DirectedUniverseData.category
#assert_no_axioms FX1Poly.Axis.DirectedUniverseFunctor

-- The covariant fibration structure
#assert_no_axioms FX1Poly.Axis.CovariantFibration

-- Straightening / unstraightening + the classification round-trips
#assert_no_axioms FX1Poly.Axis.CovariantFibration.straighten
#assert_no_axioms FX1Poly.Axis.CovariantFibration.unstraighten
#assert_no_axioms FX1Poly.Axis.CovariantFibration.unstraighten_straighten
#assert_no_axioms FX1Poly.Axis.CovariantFibration.straighten_unstraighten

-- The Grothendieck total category + projection
#assert_no_axioms FX1Poly.Axis.CovariantFibration.TotalObject
#assert_no_axioms FX1Poly.Axis.CovariantFibration.TotalMorphism
#assert_no_axioms FX1Poly.Axis.CovariantFibration.TotalMorphism.ext
#assert_no_axioms FX1Poly.Axis.CovariantFibration.TotalMorphism.identity
#assert_no_axioms FX1Poly.Axis.CovariantFibration.TotalMorphism.compose
#assert_no_axioms FX1Poly.Axis.CovariantFibration.totalCategory
#assert_no_axioms FX1Poly.Axis.CovariantFibration.projection

-- The cocartesian lift + its universal property (existence + uniqueness)
#assert_no_axioms FX1Poly.Axis.CovariantFibration.cocartesianMorphism
#assert_no_axioms FX1Poly.Axis.CovariantFibration.cocartesianLift_isWeaklyInitial
#assert_no_axioms FX1Poly.Axis.CovariantFibration.cocartesianLift_mediatorUnique

-- Bridge to context-34 + canonical / decidable witnesses
#assert_no_axioms FX1Poly.Axis.CovariantFibration.liftAsDirectedHom
#assert_no_axioms FX1Poly.Axis.CovariantFibration.constant
#assert_no_axioms FX1Poly.Axis.CovariantFibration.TotalMorphism.instDecidableEq

-- Honesty markers + smokes
#assert_no_axioms FX1Poly.Axis.fxCovariantFibration_hasStrictGrothendieckClassification
#assert_no_axioms FX1Poly.Axis.fxCovariantFibration_hasCocartesianUniversalProperty
#assert_no_axioms FX1Poly.Axis.fxCovariantFibration_hasFullInfinityCosmosStraightening
#assert_no_axioms FX1Poly.Axis.fxCovariantFibration_isOverCoreIotaTable
#assert_no_axioms FX1Poly.Axis.CovariantFibration.constant_classifies_smoke
#assert_no_axioms FX1Poly.Axis.CovariantFibration.cocartesianMorphism_projects_smoke

end FX1PolyAudit
