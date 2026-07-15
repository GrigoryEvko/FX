import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.SimplicialModel

/-! # FX1PolyAudit/AuditAxisContextSimplicialModel — zero-axiom gate for context-13's simplicial model

Per-declaration zero-axiom gate for `context-13`'s context-side deliverable
(`FX1Poly/Axis/Context/SimplicialModel.lean`): the Kapulkin–Lumsdaine simplicial model's SITE + presheaf
residue — the simplex category Δ as a `RawCategory` (laws by `rfl`, no `funext`), the simplicial generators
+ a cosimplicial identity, simplicial sets (presheaves) + the representable Yoneda witness, and the model
datum.  Kan fibrancy + the univalent universe are the honest `×type` / full-model deferral (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The simplex category Δ
#assert_no_axioms FX1Poly.Axis.SimplexMap
#assert_no_axioms FX1Poly.Axis.SimplexMap.identityMap
#assert_no_axioms FX1Poly.Axis.SimplexMap.composeMap
#assert_no_axioms FX1Poly.Axis.simplexCategory

-- The simplicial generators + a cosimplicial identity
#assert_no_axioms FX1Poly.Axis.SimplexMap.coface0
#assert_no_axioms FX1Poly.Axis.SimplexMap.cofaceLast
#assert_no_axioms FX1Poly.Axis.SimplexMap.codegeneracy0
#assert_no_axioms FX1Poly.Axis.SimplexMap.codegeneracy0_coface0

-- Simplicial sets (presheaves) + the representable witness
#assert_no_axioms FX1Poly.Axis.SimplicialSet
#assert_no_axioms FX1Poly.Axis.representableSimplicialSet

-- The category of simplicial sets (sSet) + the Yoneda embedding
#assert_no_axioms FX1Poly.Axis.SimplicialMap
#assert_no_axioms FX1Poly.Axis.SimplicialMap.identityMap
#assert_no_axioms FX1Poly.Axis.SimplicialMap.composeMap
#assert_no_axioms FX1Poly.Axis.simplicialSetCategory
#assert_no_axioms FX1Poly.Axis.yonedaObject
#assert_no_axioms FX1Poly.Axis.yonedaMorphism
#assert_no_axioms FX1Poly.Axis.yonedaMorphism_identity
#assert_no_axioms FX1Poly.Axis.yonedaMorphism_compose

-- The model datum + honesty markers + smoke
#assert_no_axioms FX1Poly.Axis.SimplicialModelData
#assert_no_axioms FX1Poly.Axis.fxSimplicialModel
#assert_no_axioms FX1Poly.Axis.fxSimplicialModel_hasKanFibrancy
#assert_no_axioms FX1Poly.Axis.fxSimplicialModel_hasUnivalentUniverse
#assert_no_axioms FX1Poly.Axis.representableSimplicialSet_restrictIdentity_smoke

end FX1PolyAudit
