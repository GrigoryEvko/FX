import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.PresheafModel

/-! # FX1PolyAudit/AuditAxisContextPresheafModel — zero-axiom gate for context-25's presheaf model

Per-declaration zero-axiom gate for `context-25`'s context-side deliverable
(`FX1Poly/Axis/Context/PresheafModel.lean`): the general Hofmann–Streicher presheaf model's BASE — presheaves
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
#assert_no_axioms FX1Poly.Axis.Presheaf
#assert_no_axioms FX1Poly.Axis.PresheafMorphism
#assert_no_axioms FX1Poly.Axis.PresheafMorphism.identityMorphism
#assert_no_axioms FX1Poly.Axis.PresheafMorphism.composeMorphism
#assert_no_axioms FX1Poly.Axis.presheafCategory

-- The representable + the Yoneda embedding (pointwise functoriality)
#assert_no_axioms FX1Poly.Axis.representablePresheaf
#assert_no_axioms FX1Poly.Axis.presheafYonedaObject
#assert_no_axioms FX1Poly.Axis.presheafYonedaMorphism
#assert_no_axioms FX1Poly.Axis.presheafYonedaMorphism_identity_component
#assert_no_axioms FX1Poly.Axis.presheafYonedaMorphism_compose_component

-- A concrete object + the unit
#assert_no_axioms FX1Poly.Axis.terminalPresheaf
#assert_no_axioms FX1Poly.Axis.terminalPresheafMorphism

-- Subsumption: simplicial / cubical models as instances
#assert_no_axioms FX1Poly.Axis.fxSimplicialPresheafCategory
#assert_no_axioms FX1Poly.Axis.fxCubicalPresheafCategory

-- The model datum + honesty markers + smoke
#assert_no_axioms FX1Poly.Axis.PresheafModelData
#assert_no_axioms FX1Poly.Axis.fxPresheafModel
#assert_no_axioms FX1Poly.Axis.fxPresheafModel_hasHofmannStreicherUniverse
#assert_no_axioms FX1Poly.Axis.fxPresheafModel_hasPresheafTypeStructure
#assert_no_axioms FX1Poly.Axis.fxPresheafModel_hasPresheafLocalCartesianClosure
#assert_no_axioms FX1Poly.Axis.representablePresheaf_restrictIdentity_smoke

end FX1PolyAudit
