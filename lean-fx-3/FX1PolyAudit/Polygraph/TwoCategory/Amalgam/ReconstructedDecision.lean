import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.ReconstructedDecision

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.ReconstructedDecision — zero-axiom gate for the CELL round-trip,
the reconstructed-signature REFLECTION, and the UNCONDITIONAL reseated decider (MODE-ADMIT-INV-N3)

Per-declaration zero-axiom gate for the cell round-trip (`reseatCellInv_reseatCell` via the size-fuel recursion and
the two whisker steps), the reflection (`reseatReflect`), the unconditional decider (`monadReconstructedDecision`),
and both live verdicts on real reconstructed cells.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- B1: the cell round-trip — the size helper, the cast helpers, the two whisker steps, the fuel recursion, the node
#assert_no_axioms FX1Poly.Polygraph.Amalgam.oneLeRawCellSize
#assert_no_axioms FX1Poly.Polygraph.Amalgam.genTransportCast
#assert_no_axioms FX1Poly.Polygraph.Amalgam.castBoundarySymmCancel
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCellInvReseatCellWhiskerLeftStep
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCellInvReseatCellWhiskerRightStep
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCellInvReseatCellFueled
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCellInv_reseatCell

-- B2: the reconstructed-signature reflection
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatReflect

-- B3: the unconditional decider + both live verdicts on real reconstructed cells
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadReconstructedDecision
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconAssocReflectsTrue
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconLeftUnitReflectsTrue
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconFacesReflectFalse
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCellInv_reseatCell_reconMu

-- The honesty markers
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxRecon_hasCellRoundTrip
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxRecon_hasReflection
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxRecon_hasUnconditionalReconstructionDecider

end FX1PolyAudit
