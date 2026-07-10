import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.MonadReseatInverse

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.MonadReseatInverse — zero-axiom gate for the INVERSE reseat
functor + the reseated reconstructed-signature decider (MODE-ADMIT-INV r1)

Per-declaration zero-axiom gate for the inverse (bespoke ==> reconstructed) reseat: the inverse 1-cell functor
(`reseatPathInv` + reduction smokes + the homomorphism law + the bespoke-start round-trip), the DIRECT inverse
generator map (`reseatGenInv`), the inverse free 2-cell functor (`reseatCellInv`) with its per-constructor
reduction lemmas, the thirteen-constructor conv functoriality (`reseatCellInv_preservesConv`), the backward law
rows and the BACKWARD conv transport (`reseatConvBackward`), and the reseated decider assembly with both live
verdicts on real reconstructed cells.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- B2: the inverse 1-cell functor + reduction smokes + the homomorphism law + the bespoke-start round-trip
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatPathInv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatPathInv_nil
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatPathInv_monadT
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatPathInv_monadTThenT
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatPathInv_composePath
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatPathInv_length

-- B3: the DIRECT inverse generator map + the inverse free 2-cell functor
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatGenInv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatGenInv_eta
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatGenInv_mu
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCellInv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCellInv_gen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCellInv_monadUnit
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCellInv_monadMul
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCellInv_monadIdT

-- B3: the reseatCellInv per-constructor reduction lemmas
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCellInv_id
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCellInv_vcomp
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCellInv_whiskerLeft
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCellInv_whiskerRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCellInv_castBoundary
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCellInv_hcomp
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCellInv_whiskerLeft_whiskerLeft
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCellInv_whiskerRight_whiskerRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCellInv_whiskerLeft_whiskerRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCellInv_whiskerRight_whiskerLeft

-- B4: the inverse conv functoriality (the linchpin `reseatCellInv_preservesConv`)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatTwoCellStepInv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatTwoCellConvInv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCellInv_preservesConv

-- B4: the three backward law rows + the congruence + the BACKWARD conv transport
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconLeftUnitConvBackward
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconRightUnitConvBackward
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconAssocConvBackward
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCongruenceBackward
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatConvBackward

-- B5: the reseated decider + both live verdicts on real recon cells
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconFaceDeltaOne
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconFaceDeltaZero
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCell_reconFaceDeltaOne
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCell_reconFaceDeltaZero
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconFacesDecideFalse
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconAssocDecidesTrue
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconLeftUnitDecidesTrue
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadReconstructedDecisionViaReflection

-- B6: the round-trip nodes — the PATH leg (fixed-index generalization via length fuel)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconModalityTargetZero
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconModalityUnique
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatPathInv_reseatPath_fueled
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatPathInv_reseatPath

-- The honesty markers
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalgInverse_hasBackwardReseatTransport
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalgInverse_hasReseatedDeciderBothVerdicts
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalgInverse_hasReseatedReconstructionDecider

end FX1PolyAudit
