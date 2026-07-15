import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.CubicalModal

/-! # FX1PolyAudit/AuditAxisModeCubicalModal — zero-axiom gate for mode-16

Per-declaration zero-axiom gate for `mode-16` (`FX1Poly/Axis/Mode/CubicalModal.lean`): the path functor + face
map, the modal operators (identity / reader / cube), the orthogonality exchange + its derived faithfulness, the
witnesses (identity / reader / cube-cube), the cube-endpoint face coherence + the path tie, and the honesty
markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The path functor + face map
#assert_no_axioms FX1Poly.Axis.PathSpace
#assert_no_axioms FX1Poly.Axis.faceAt

-- The modal operators
#assert_no_axioms FX1Poly.Axis.ModalOperator
#assert_no_axioms FX1Poly.Axis.identityModalOperator
#assert_no_axioms FX1Poly.Axis.readerModalOperator
#assert_no_axioms FX1Poly.Axis.cubeModality

-- The orthogonality exchange + derived faithfulness
#assert_no_axioms FX1Poly.Axis.OrthogonalExchange
#assert_no_axioms FX1Poly.Axis.OrthogonalExchange.push_injective

-- The witnesses
#assert_no_axioms FX1Poly.Axis.identityExchange
#assert_no_axioms FX1Poly.Axis.readerExchange
#assert_no_axioms FX1Poly.Axis.cubeCubeExchange
#assert_no_axioms FX1Poly.Axis.readerExchange_cube_faces
#assert_no_axioms FX1Poly.Axis.cubeModality_Apply

-- Face-lattice orthogonality (the modality commutes with dimension substitution)
#assert_no_axioms FX1Poly.Axis.substDim
#assert_no_axioms FX1Poly.Axis.readerExchange_commutes_substDim
#assert_no_axioms FX1Poly.Axis.readerExchange_commutes_reversal

-- Honesty markers
#assert_no_axioms FX1Poly.Axis.fxMode_hasModalKanOperations
#assert_no_axioms FX1Poly.Axis.fxMode_hasFaceLatticeOrthogonality
#assert_no_axioms FX1Poly.Axis.fxMode_hasModalLockDimensionExchange
#assert_no_axioms FX1Poly.Axis.fxMode_hasKernelCubicalModalConnection

end FX1PolyAudit
