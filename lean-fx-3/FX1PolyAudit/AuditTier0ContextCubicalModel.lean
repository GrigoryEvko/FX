import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.CubicalModel

/-! # FX1PolyAudit/AuditTier0ContextCubicalModel — zero-axiom gate for context-22's cubical model

Per-declaration zero-axiom gate for `context-22`'s context-side deliverable
(`FX1Poly/Tier0/Context/CubicalModel.lean`): the CCHM/cartesian cubical model's SITE + presheaf residue —
the cube category `□` (monotone / Dedekind presentation) as a `RawCategory` (laws by `rfl`, no `funext`),
the interval endpoints / degeneracy / diagonal / `∧`-connection generators + the connection-idempotence
cubical identity, cubical sets (presheaves) + the representable Yoneda witness, the category of cubical sets
+ the Yoneda embedding, and the model datum.  Kan fibrancy, the Glue type, and the univalent universe are the
honest `×type` / full-model deferrals (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The cube category □
#assert_no_axioms FX1Poly.Tier0.CubeMap
#assert_no_axioms FX1Poly.Tier0.CubeMap.identityMap
#assert_no_axioms FX1Poly.Tier0.CubeMap.composeMap
#assert_no_axioms FX1Poly.Tier0.cubeCategory

-- The cube generators + a cubical identity
#assert_no_axioms FX1Poly.Tier0.CubeMap.pointFalse
#assert_no_axioms FX1Poly.Tier0.CubeMap.pointTrue
#assert_no_axioms FX1Poly.Tier0.CubeMap.intervalDegeneracy
#assert_no_axioms FX1Poly.Tier0.CubeMap.diagonal
#assert_no_axioms FX1Poly.Tier0.CubeMap.connectionMin
#assert_no_axioms FX1Poly.Tier0.CubeMap.connectionMin_diagonal_idempotent

-- Cubical sets (presheaves) + the representable witness
#assert_no_axioms FX1Poly.Tier0.CubicalSet
#assert_no_axioms FX1Poly.Tier0.representableCubicalSet

-- The category of cubical sets (cSet) + the Yoneda embedding
#assert_no_axioms FX1Poly.Tier0.CubicalMap
#assert_no_axioms FX1Poly.Tier0.CubicalMap.identityMap
#assert_no_axioms FX1Poly.Tier0.CubicalMap.composeMap
#assert_no_axioms FX1Poly.Tier0.cubicalSetCategory
#assert_no_axioms FX1Poly.Tier0.cubicalYonedaObject
#assert_no_axioms FX1Poly.Tier0.cubicalYonedaMorphism
#assert_no_axioms FX1Poly.Tier0.cubicalYonedaMorphism_identity
#assert_no_axioms FX1Poly.Tier0.cubicalYonedaMorphism_compose

-- The model datum + honesty markers + smoke
#assert_no_axioms FX1Poly.Tier0.CubicalModelData
#assert_no_axioms FX1Poly.Tier0.fxCubicalModel
#assert_no_axioms FX1Poly.Tier0.fxCubicalModel_hasKanFibrancy
#assert_no_axioms FX1Poly.Tier0.fxCubicalModel_hasGlueTypes
#assert_no_axioms FX1Poly.Tier0.fxCubicalModel_hasUnivalentUniverse
#assert_no_axioms FX1Poly.Tier0.representableCubicalSet_restrictIdentity_smoke

end FX1PolyAudit
