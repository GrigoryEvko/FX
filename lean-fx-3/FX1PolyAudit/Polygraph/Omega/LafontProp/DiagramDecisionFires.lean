import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.LafontProp.DiagramDecisionFires

/-! # FX1PolyAudit.Polygraph.Omega.LafontProp.DiagramDecisionFires — zero-axiom gate
(LAFONT-PROP r2, brick C: THE DECISION FIRES)

Per-declaration zero-axiom gate for the word-problem decision: the matrix-comparison decision
procedure with its three-way logical status (unconditional refutation / soundness /
completeness modulo the named canonical-reduction residual), the six fire packages (the two
old-killer pairs, the copy/add spider, the swap-heavy pairs, the bialgebra square through the
normal-form machine, and the Z2 negative control with the machine-checked NON-convertibility).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`,
`WellFounded.fix`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.decideEqualMatricesOfDiagrams
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.decisionRefutesConvertibility
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.decisionIsImpliedByConvertibility
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.decisionAffirmsConvertibilityGivenCanonicalReduction
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.unitPairDecisionFires
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.unitPairNormalFormsCoincide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.unitPairDecisionAgreesWithConversion
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.associativityPairDecisionFires
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.associativityPairNormalFormsCoincide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.spiderCopyStage
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.spiderFoldedLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.spiderFoldedRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.spiderDenotesTripling
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.spiderPairDecisionFires
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.spiderPairIsConvertible
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.spiderPairNormalFormsCoincide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.tripleSwapDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.tripleSwapDecisionFires
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.tripleSwapIsConvertibleToSwap
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.tripleSwapNormalFormsCoincide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.yangBaxterDecisionFires
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.yangBaxterNormalFormsCoincide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.bimonoidSquareDecisionFires
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.bimonoidSquareNormalFormsCoincide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.doublingDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.resetDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.zSpecificPairDecisionRefutes
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.zSpecificPairIsNotConvertible

end FX1PolyAudit
