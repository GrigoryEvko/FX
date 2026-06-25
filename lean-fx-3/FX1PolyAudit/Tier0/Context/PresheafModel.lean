import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.PresheafModel

/-! # FX1PolyAudit/AuditTier0ContextPresheafModel — zero-axiom gate for context-25's presheaf model

Per-declaration zero-axiom gate for `context-25`'s context-side deliverable
(`FX1Poly/Tier0/Context/PresheafModel.lean`): the general Hofmann–Streicher presheaf model's BASE — presheaves
on an arbitrary small site (`Presheaf`), the presheaf category `[Cᵒᵖ, Set]` (`presheafCategory`) as a
`RawCategory` (laws by `rfl` for ANY site, no `funext`), the representable `よ(c)` + the Yoneda embedding
(functoriality stated POINTWISE — the morphism-equality form is funext-blocked for a generic site), the
terminal presheaf + its unit, and the SUBSUMPTION witnesses (`fxSimplicialPresheafCategory`,
`fxCubicalPresheafCategory` — `context-13` / `context-22` as instances).  The Hofmann–Streicher universe, the
presheaf `Id`/`Π`/`Σ` CwF structure, and the presheaf local cartesian closure are the honest `×type`
deferrals (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Presheaves on a small site + the presheaf category
#assert_no_axioms FX1Poly.Tier0.Presheaf
#assert_no_axioms FX1Poly.Tier0.PresheafMorphism
#assert_no_axioms FX1Poly.Tier0.PresheafMorphism.identityMorphism
#assert_no_axioms FX1Poly.Tier0.PresheafMorphism.composeMorphism
#assert_no_axioms FX1Poly.Tier0.presheafCategory

-- The representable + the Yoneda embedding (pointwise functoriality)
#assert_no_axioms FX1Poly.Tier0.representablePresheaf
#assert_no_axioms FX1Poly.Tier0.presheafYonedaObject
#assert_no_axioms FX1Poly.Tier0.presheafYonedaMorphism
#assert_no_axioms FX1Poly.Tier0.presheafYonedaMorphism_identity_component
#assert_no_axioms FX1Poly.Tier0.presheafYonedaMorphism_compose_component

-- A concrete object + the unit
#assert_no_axioms FX1Poly.Tier0.terminalPresheaf
#assert_no_axioms FX1Poly.Tier0.terminalPresheafMorphism

-- Subsumption: simplicial / cubical models as instances
#assert_no_axioms FX1Poly.Tier0.fxSimplicialPresheafCategory
#assert_no_axioms FX1Poly.Tier0.fxCubicalPresheafCategory

-- The model datum + honesty markers + smoke
#assert_no_axioms FX1Poly.Tier0.PresheafModelData
#assert_no_axioms FX1Poly.Tier0.fxPresheafModel
#assert_no_axioms FX1Poly.Tier0.fxPresheafModel_hasHofmannStreicherUniverse
#assert_no_axioms FX1Poly.Tier0.fxPresheafModel_hasPresheafTypeStructure
#assert_no_axioms FX1Poly.Tier0.fxPresheafModel_hasPresheafLocalCartesianClosure
#assert_no_axioms FX1Poly.Tier0.representablePresheaf_restrictIdentity_smoke

end FX1PolyAudit
