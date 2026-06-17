import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.CubicalModal

/-! # FX1PolyAudit/AuditTier0ModeCubicalModal — zero-axiom gate for mode-16

Per-declaration zero-axiom gate for `mode-16` (`FX1Poly/Tier0/Mode/CubicalModal.lean`): the path functor + face
map, the modal operators (identity / reader / cube), the orthogonality exchange + its derived faithfulness, the
witnesses (identity / reader / cube-cube), the cube-endpoint face coherence + the path tie, and the honesty
markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The path functor + face map
#assert_no_axioms FX1Poly.Tier0.PathSpace
#assert_no_axioms FX1Poly.Tier0.faceAt

-- The modal operators
#assert_no_axioms FX1Poly.Tier0.ModalOperator
#assert_no_axioms FX1Poly.Tier0.identityModalOperator
#assert_no_axioms FX1Poly.Tier0.readerModalOperator
#assert_no_axioms FX1Poly.Tier0.cubeModality

-- The orthogonality exchange + derived faithfulness
#assert_no_axioms FX1Poly.Tier0.OrthogonalExchange
#assert_no_axioms FX1Poly.Tier0.OrthogonalExchange.push_injective

-- The witnesses
#assert_no_axioms FX1Poly.Tier0.identityExchange
#assert_no_axioms FX1Poly.Tier0.readerExchange
#assert_no_axioms FX1Poly.Tier0.cubeCubeExchange
#assert_no_axioms FX1Poly.Tier0.readerExchange_cube_faces
#assert_no_axioms FX1Poly.Tier0.cubeModality_Apply

-- Face-lattice orthogonality (the modality commutes with dimension substitution)
#assert_no_axioms FX1Poly.Tier0.substDim
#assert_no_axioms FX1Poly.Tier0.readerExchange_commutes_substDim
#assert_no_axioms FX1Poly.Tier0.readerExchange_commutes_reversal

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasModalKanOperations
#assert_no_axioms FX1Poly.Tier0.fxMode_hasFaceLatticeOrthogonality
#assert_no_axioms FX1Poly.Tier0.fxMode_hasModalLockDimensionExchange
#assert_no_axioms FX1Poly.Tier0.fxMode_hasKernelCubicalModalConnection

end FX1PolyAudit
