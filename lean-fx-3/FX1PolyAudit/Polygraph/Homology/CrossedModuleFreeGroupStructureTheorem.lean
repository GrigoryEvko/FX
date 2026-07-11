import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.CrossedModuleFreeGroupStructureTheorem

/-! # FX1PolyAudit/Polygraph/Homology/CrossedModuleFreeGroupStructureTheorem — zero-axiom gate (the
    free-group residual R1, the R1-unlocked crossed-module sub-moves, and the well-formed structure-
    theorem / instance-iso adjudication for `⟨s | s³⟩`)

Per-declaration zero-axiom gate for WP-2GROUP r5 (#2199).  Every declaration must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## B1 — the single-generator normal form + R1 -/

#assert_no_axioms FX1Poly.Polygraph.Homology.signPowerPos
#assert_no_axioms FX1Poly.Polygraph.Homology.signPowerNeg
#assert_no_axioms FX1Poly.Polygraph.Homology.signPower
#assert_no_axioms FX1Poly.Polygraph.Homology.consReducedPosSignPowerPos
#assert_no_axioms FX1Poly.Polygraph.Homology.consReducedNegSignPowerNeg
#assert_no_axioms FX1Poly.Polygraph.Homology.consReducedPosSignPowerNeg
#assert_no_axioms FX1Poly.Polygraph.Homology.consReducedNegSignPowerPos
#assert_no_axioms FX1Poly.Polygraph.Homology.consReducedPosSignPower
#assert_no_axioms FX1Poly.Polygraph.Homology.consReducedNegSignPower
#assert_no_axioms FX1Poly.Polygraph.Homology.AllLettersOverGenZero
#assert_no_axioms FX1Poly.Polygraph.Homology.allLettersSignPowerPos
#assert_no_axioms FX1Poly.Polygraph.Homology.allLettersSignPowerNeg
#assert_no_axioms FX1Poly.Polygraph.Homology.allLettersSignPower
#assert_no_axioms FX1Poly.Polygraph.Homology.allLettersAppend
#assert_no_axioms FX1Poly.Polygraph.Homology.allLettersReverseAux
#assert_no_axioms FX1Poly.Polygraph.Homology.allLettersReverse
#assert_no_axioms FX1Poly.Polygraph.Homology.allLettersMapInverse
#assert_no_axioms FX1Poly.Polygraph.Homology.allLettersInvWord
#assert_no_axioms FX1Poly.Polygraph.Homology.allLettersRelatorWordZero
#assert_no_axioms FX1Poly.Polygraph.Homology.reduceWordIsSignPowerOverGenZero
#assert_no_axioms FX1Poly.Polygraph.Homology.allLettersReduceWord
#assert_no_axioms FX1Poly.Polygraph.Homology.mulWordInvRightOverGenZero
#assert_no_axioms FX1Poly.Polygraph.Homology.mulWordAssocOverGenZero
#assert_no_axioms FX1Poly.Polygraph.Homology.conjugatedRelatorBoundaryIsRelatorOverGenZero
#assert_no_axioms FX1Poly.Polygraph.Homology.signPowerThreeProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.signPowerNegTwoProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.reduceWordSignPowerProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.mulWordInvRightProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.conjugationCollapseProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.freeGroupResidualR1IsComplete

/-! ## B2 — the R1-unlocked sub-moves + the shuffled-commutator attack -/

#assert_no_axioms FX1Poly.Polygraph.Homology.signPowerPosAppend
#assert_no_axioms FX1Poly.Polygraph.Homology.reduceWordSignPowerPos
#assert_no_axioms FX1Poly.Polygraph.Homology.freeCrossedAdjacentSwap
#assert_no_axioms FX1Poly.Polygraph.Homology.freeCrossedSignPowerStrip
#assert_no_axioms FX1Poly.Polygraph.Homology.conjugatorStripS3ToGenE0
#assert_no_axioms FX1Poly.Polygraph.Homology.shuffledCommutatorBoundaryVanishes
#assert_no_axioms FX1Poly.Polygraph.Homology.shuffledCommutatorImageIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.shuffledCommutatorReduces
#assert_no_axioms FX1Poly.Polygraph.Homology.freeCrossedSubMovesAreComplete

end FX1PolyAudit
