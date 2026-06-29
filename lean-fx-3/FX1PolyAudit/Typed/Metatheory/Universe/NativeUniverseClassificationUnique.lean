import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Universe.NativeUniverseClassificationUnique

/-! # FX1PolyAudit/NativeUniverseClassificationUnique — native universe-flag-uniqueness audit shard

Per-declaration zero-axiom gate for the native universe-flag-uniqueness leaves (the consistency-leg keystone
#1697/#1740): the variable and universe-code leaves (built on the head inversions) plus the lam-arm refutation
and the NEUTRAL-spine classifier uniqueness (and its universe specialization) — the application/eliminator arm
of the structural budget assembly. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.variableUniverseClassificationUnique
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtUniverseCodeHeadGeneric
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.universeCodeUniverseClassificationUnique
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.lamNotTypedAtUniverseCode
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.idStrictRecHeadUntyped
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.neutralClassifierUnique
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.neutralUniverseClassificationUnique
#assert_no_axioms FX1Poly.Typed.Conv.unitTypeCell_not_universeCode
#assert_no_axioms FX1Poly.Typed.Conv.intervalTypeCell_not_universeCode
#assert_no_axioms FX1Poly.Typed.Conv.bridgeTypeCell_not_universeCode
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtIntroHeadOutput
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.introMemberNotTypedAtUniverseCode

end FX1PolyAudit
