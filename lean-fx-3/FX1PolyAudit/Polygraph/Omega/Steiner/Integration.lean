import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Steiner.Integration

/-! # FX1PolyAudit/Polygraph/Omega/Steiner/Integration — zero-axiom gate (OMEGA-2 r2, B1)

Per-declaration `#assert_no_axioms` on the integration: the boundary-column-from-linearize formula,
the column-indexed matrix builder + its rectangularity, `FinitePresentation` / `adcOfComputad`, the
walking-parallel-pair signature + decidable-equality data, the one-hot faithful valuation, the battery
ADC + its `isStrongSteiner` admission, the linearize-difference column identity, and the
admission-to-decision integration theorem.  Every declaration must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.boundaryColumnFromLinearize
#assert_no_axioms FX1Poly.Polygraph.Omega.buildFromIndices
#assert_no_axioms FX1Poly.Polygraph.Omega.buildFromIndices_length
#assert_no_axioms FX1Poly.Polygraph.Omega.rowFromColumns
#assert_no_axioms FX1Poly.Polygraph.Omega.rowFromColumns_length
#assert_no_axioms FX1Poly.Polygraph.Omega.buildColumnMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.buildFromIndices_rowsAllHaveWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.buildColumnMatrix_isRectangular
#assert_no_axioms FX1Poly.Polygraph.Omega.adcOfComputad
#assert_no_axioms FX1Poly.Polygraph.Omega.PairModality
#assert_no_axioms FX1Poly.Polygraph.Omega.pairGraph
#assert_no_axioms FX1Poly.Polygraph.Omega.pathEdgeF
#assert_no_axioms FX1Poly.Polygraph.Omega.pathEdgeG
#assert_no_axioms FX1Poly.Polygraph.Omega.PairTwoCell
#assert_no_axioms FX1Poly.Polygraph.Omega.pairSignature
#assert_no_axioms FX1Poly.Polygraph.Omega.pairModeDecEq
#assert_no_axioms FX1Poly.Polygraph.Omega.pairModalityDecEq
#assert_no_axioms FX1Poly.Polygraph.Omega.pairTwoCellDecEq
#assert_no_axioms FX1Poly.Polygraph.Omega.pairGenValue
#assert_no_axioms FX1Poly.Polygraph.Omega.pairGenValueLength
#assert_no_axioms FX1Poly.Polygraph.Omega.pairValuation
#assert_no_axioms FX1Poly.Polygraph.Omega.parallelPairPresentation
#assert_no_axioms FX1Poly.Polygraph.Omega.parallelPairComplex
#assert_no_axioms FX1Poly.Polygraph.Omega.parallelPairComplex_isStrongSteiner
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicComplex_not_isStrongSteiner
#assert_no_axioms FX1Poly.Polygraph.Omega.parallelPairColumn_isLinearizeDifference
#assert_no_axioms FX1Poly.Polygraph.Omega.parallelPairIntegration

end FX1PolyAudit
