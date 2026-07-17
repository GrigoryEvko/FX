import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.WordProblemCostLedger

/-! # FX1PolyAudit/.../WordProblemCostLedger — zero-axiom gate

Per-declaration zero-axiom gate for the per-rung decision COST ledger (WP-CEIL-COST #2046): the cost-class /
cost-evidence taxonomies, the two total maps over the live decided-13 enum, the kernel-checked class/evidence
rows, the per-evidence and per-class counts (including the honest proved-count ZERO), the class-union
exhaustiveness, and the honest markers.

Full-enumeration matches over the walker enum with `List.Mem` constructors; must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `decide`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Table.wordProblemCostClass
#assert_no_axioms FX1Poly.Polygraph.Table.wordProblemCostEvidence
#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemDecidedWalkersCostClassRow
#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemDecidedWalkersCostEvidenceRow
#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemDecidedWalkersCostEvidenceCited
#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemCostCitedWalkers
#assert_no_axioms FX1Poly.Polygraph.Table.wordProblemCostCitedWalkerCountIsFifteen
#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemCostProvedWalkers
#assert_no_axioms FX1Poly.Polygraph.Table.wordProblemCostProvedWalkerCountIsZero
#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemCostMeasuredWalkers
#assert_no_axioms FX1Poly.Polygraph.Table.wordProblemCostMeasuredWalkerCountIsZero
#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemConstantTimeCostWalkers
#assert_no_axioms FX1Poly.Polygraph.Table.wordProblemConstantTimeCostWalkerCountIsOne
#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemLinearCostWalkers
#assert_no_axioms FX1Poly.Polygraph.Table.wordProblemLinearCostWalkerCountIsSeven
#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemQuadraticCostWalkers
#assert_no_axioms FX1Poly.Polygraph.Table.wordProblemQuadraticCostWalkerCountIsTwo
#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemPolynomialCostWalkers
#assert_no_axioms FX1Poly.Polygraph.Table.wordProblemPolynomialCostWalkerCountIsFive
#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemExponentialBoundedCostWalkers
#assert_no_axioms FX1Poly.Polygraph.Table.wordProblemExponentialBoundedCostWalkerCountIsZero
#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemCostClassifiedWalkers
#assert_no_axioms FX1Poly.Polygraph.Table.wordProblemCostClassifiedWalkerCountIsFifteen
#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemCostClassifiedWalkersIsClassUnion
#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemCostClassifiedWalkersClassRow
#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemCostClassifiedWalkersExhaustive
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpCost_allRungsTagged
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpCost_allTagsProved
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpCost_kzRowCoversBothDeciders

end FX1PolyAudit
