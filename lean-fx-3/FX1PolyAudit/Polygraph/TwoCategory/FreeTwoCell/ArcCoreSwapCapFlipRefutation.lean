import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCoreSwapCapFlipRefutation

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/ArcCoreSwapCapFlipRefutation — zero-axiom gate

Per-declaration zero-axiom gate for the machine-checked refutation of the CORRECTED count-field core
block-swap residual `ArcGodementCoreSwapSimCount`: the counit / cap join-order ROOT FLIP at a fresh forest
state kills the root-level `ArcStepSimCount.rootComm`, the positive-control confirms the `SameArcPartition`
target survives, and the honesty marker + residual-(2) pin record the sharpening.  The `#assert_no_axioms` on
`not_arcGodementCoreSwapSimCount_adjunction` transitively covers the private cores / openWires / root facts.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.not_arcGodementCoreSwapSimCount_adjunction
#assert_no_axioms FX1Poly.Polygraph.arcRootFlip_partitionAgrees
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCoreSwapSimCountRefuted
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcGodementSwapRenameableProof2_eq_false

end FX1PolyAudit
