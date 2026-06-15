import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.SimplicialModel

/-! # FX1PolyAudit/AuditTier0ContextSimplicialModel — zero-axiom gate for context-13's simplicial model

Per-declaration zero-axiom gate for `context-13`'s context-side deliverable
(`FX1Poly/Tier0/Context/SimplicialModel.lean`): the Kapulkin–Lumsdaine simplicial model's SITE + presheaf
residue — the simplex category Δ as a `RawCategory` (laws by `rfl`, no `funext`), the simplicial generators
+ a cosimplicial identity, simplicial sets (presheaves) + the representable Yoneda witness, and the model
datum.  Kan fibrancy + the univalent universe are the honest `×type` / full-model deferral (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The simplex category Δ
#assert_no_axioms FX1Poly.Tier0.SimplexMap
#assert_no_axioms FX1Poly.Tier0.SimplexMap.identityMap
#assert_no_axioms FX1Poly.Tier0.SimplexMap.composeMap
#assert_no_axioms FX1Poly.Tier0.simplexCategory

-- The simplicial generators + a cosimplicial identity
#assert_no_axioms FX1Poly.Tier0.SimplexMap.coface0
#assert_no_axioms FX1Poly.Tier0.SimplexMap.cofaceLast
#assert_no_axioms FX1Poly.Tier0.SimplexMap.codegeneracy0
#assert_no_axioms FX1Poly.Tier0.SimplexMap.codegeneracy0_coface0

-- Simplicial sets (presheaves) + the representable witness
#assert_no_axioms FX1Poly.Tier0.SimplicialSet
#assert_no_axioms FX1Poly.Tier0.representableSimplicialSet

-- The category of simplicial sets (sSet) + the Yoneda embedding
#assert_no_axioms FX1Poly.Tier0.SimplicialMap
#assert_no_axioms FX1Poly.Tier0.SimplicialMap.identityMap
#assert_no_axioms FX1Poly.Tier0.SimplicialMap.composeMap
#assert_no_axioms FX1Poly.Tier0.simplicialSetCategory
#assert_no_axioms FX1Poly.Tier0.yonedaObject
#assert_no_axioms FX1Poly.Tier0.yonedaMorphism
#assert_no_axioms FX1Poly.Tier0.yonedaMorphism_identity
#assert_no_axioms FX1Poly.Tier0.yonedaMorphism_compose

-- The model datum + honesty markers + smoke
#assert_no_axioms FX1Poly.Tier0.SimplicialModelData
#assert_no_axioms FX1Poly.Tier0.fxSimplicialModel
#assert_no_axioms FX1Poly.Tier0.fxSimplicialModel_hasKanFibrancy
#assert_no_axioms FX1Poly.Tier0.fxSimplicialModel_hasUnivalentUniverse
#assert_no_axioms FX1Poly.Tier0.representableSimplicialSet_restrictIdentity_smoke

end FX1PolyAudit
