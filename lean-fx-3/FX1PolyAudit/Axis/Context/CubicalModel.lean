import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.CubicalModel

/-! # FX1PolyAudit/AuditAxisContextCubicalModel — zero-axiom gate for context-22's cubical model

Per-declaration zero-axiom gate for `context-22`'s context-side deliverable
(`FX1Poly/Axis/Context/CubicalModel.lean`): the cubical model's SITE + presheaf residue, in the DEDEKIND
(monotone / distributive-lattice) presentation of the cube category `□` — NOT the CCHM (De Morgan, with the
non-monotone reversal `¬`) nor the strict Cartesian (connection-free) site; those distinctions + univalence
are the deferred `×type` core.  `□` as a `RawCategory` (laws by `rfl`, no `funext`),
the interval endpoints / degeneracy / diagonal / `∧`-connection generators + the connection-idempotence
cubical identity, cubical sets (presheaves) + the representable Yoneda witness, the category of cubical sets
+ the Yoneda embedding, and the model datum.  Kan fibrancy, the Glue type, and the univalent universe are the
honest `×type` / full-model deferrals (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The cube category □
#assert_no_axioms FX1Poly.Axis.CubeMap
#assert_no_axioms FX1Poly.Axis.CubeMap.identityMap
#assert_no_axioms FX1Poly.Axis.CubeMap.composeMap
#assert_no_axioms FX1Poly.Axis.cubeCategory

-- The cube generators + a cubical identity
#assert_no_axioms FX1Poly.Axis.CubeMap.pointFalse
#assert_no_axioms FX1Poly.Axis.CubeMap.pointTrue
#assert_no_axioms FX1Poly.Axis.CubeMap.intervalDegeneracy
#assert_no_axioms FX1Poly.Axis.CubeMap.diagonal
#assert_no_axioms FX1Poly.Axis.CubeMap.connectionMin
#assert_no_axioms FX1Poly.Axis.CubeMap.connectionMin_diagonal_idempotent

-- Cubical sets (presheaves) + the representable witness
#assert_no_axioms FX1Poly.Axis.CubicalSet
#assert_no_axioms FX1Poly.Axis.representableCubicalSet

-- The category of cubical sets (cSet) + the Yoneda embedding
#assert_no_axioms FX1Poly.Axis.CubicalMap
#assert_no_axioms FX1Poly.Axis.CubicalMap.identityMap
#assert_no_axioms FX1Poly.Axis.CubicalMap.composeMap
#assert_no_axioms FX1Poly.Axis.cubicalSetCategory
#assert_no_axioms FX1Poly.Axis.cubicalYonedaObject
#assert_no_axioms FX1Poly.Axis.cubicalYonedaMorphism
#assert_no_axioms FX1Poly.Axis.cubicalYonedaMorphism_identity
#assert_no_axioms FX1Poly.Axis.cubicalYonedaMorphism_compose

-- The model datum + honesty markers + smoke
#assert_no_axioms FX1Poly.Axis.CubicalModelData
#assert_no_axioms FX1Poly.Axis.fxCubicalModel
#assert_no_axioms FX1Poly.Axis.fxCubicalModel_hasKanFibrancy
#assert_no_axioms FX1Poly.Axis.fxCubicalModel_hasGlueTypes
#assert_no_axioms FX1Poly.Axis.fxCubicalModel_hasUnivalentUniverse
#assert_no_axioms FX1Poly.Axis.representableCubicalSet_restrictIdentity_smoke

end FX1PolyAudit
