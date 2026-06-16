import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.GroupoidModel

/-! # FX1PolyAudit/AuditTier0ContextGroupoidModel — zero-axiom gate for context-23's groupoid/setoid model

Per-declaration zero-axiom gate for `context-23`'s context-side deliverable
(`FX1Poly/Tier0/Context/GroupoidModel.lean`): the Hofmann–Streicher groupoid model's BASE + the UIP-refuting
witness — a groupoid (`RawGroupoid`) with the forgetful `Grpd ⟶ Cat`, the category of groupoids `Grpd`
(`groupoidCategory`) as a `RawCategory` (laws by `rfl`, no `funext`), the Set ↪ Grpd embedding
(`discreteGroupoid` + functoriality) with `discreteGroupoid_isSetoid` (UIP HOLDS for sets, by proof
irrelevance), and ★ the delooping `B(ℤ/2)` (`deloopZmod2`) whose hom-set is NOT a subsingleton
(`deloopZmod2_hom_not_subsingleton`, `deloopZmod2_not_setoid`) — the semantic core of the UIP refutation.
The identity-type-as-hom CwF, the groupoid universe, and the SYNTACTIC underivability of K are the honest
`×type` / full-model deferrals (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Groupoids + the forgetful Grpd ⟶ Cat
#assert_no_axioms FX1Poly.Tier0.RawGroupoid
#assert_no_axioms FX1Poly.Tier0.RawGroupoid.toRawCategory

-- The category of groupoids Grpd
#assert_no_axioms FX1Poly.Tier0.GroupoidFunctor
#assert_no_axioms FX1Poly.Tier0.GroupoidFunctor.identityFunctor
#assert_no_axioms FX1Poly.Tier0.GroupoidFunctor.composeFunctor
#assert_no_axioms FX1Poly.Tier0.groupoidCategory

-- Setoids vs groupoids — the Set ↪ Grpd embedding + UIP holds for sets
#assert_no_axioms FX1Poly.Tier0.IsSetoidGroupoid
#assert_no_axioms FX1Poly.Tier0.discreteGroupoid
#assert_no_axioms FX1Poly.Tier0.discreteGroupoidMap
#assert_no_axioms FX1Poly.Tier0.discreteGroupoid_isSetoid

-- ★ The UIP-refuting witness — the delooping of ℤ/2
#assert_no_axioms FX1Poly.Tier0.deloopZmod2
#assert_no_axioms FX1Poly.Tier0.deloopZmod2_hom_not_subsingleton
#assert_no_axioms FX1Poly.Tier0.deloopZmod2_not_setoid

-- The model datum + honesty markers + smoke
#assert_no_axioms FX1Poly.Tier0.GroupoidModelData
#assert_no_axioms FX1Poly.Tier0.fxGroupoidModel
#assert_no_axioms FX1Poly.Tier0.fxGroupoidModel_hasIdentityTypeAsHom
#assert_no_axioms FX1Poly.Tier0.fxGroupoidModel_hasGroupoidUniverse
#assert_no_axioms FX1Poly.Tier0.fxGroupoidModel_hasUipRefutationTheorem
#assert_no_axioms FX1Poly.Tier0.discreteGroupoid_isSetoid_smoke

end FX1PolyAudit
