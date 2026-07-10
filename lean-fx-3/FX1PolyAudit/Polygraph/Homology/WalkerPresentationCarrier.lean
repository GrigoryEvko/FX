import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.WalkerPresentationCarrier

/-! # FX1PolyAudit/Polygraph/Homology/WalkerPresentationCarrier — zero-axiom gate (the GENERIC
    first-order presentation carrier: computed boundaries, the generic dimension-0 loop lemma, the
    well-formedness-gated `d d = 0`, and the two shipped walkers recovered as EVALUATIONS)

Per-declaration zero-axiom gate for the H2-WALKERS r2 generic carrier: the presentation record's
compute functions (`computeBasisCount`, `computeBoundaryDim{Zero,One,Two}`, `computeBoundaryMatrix`),
the structural helpers (`countGeneratorOccurrences`, the four row builders), the generic loop-boundary
lemma and its supporting `sumOverIndicesOfAllZero` / `listGet…` facts, the well-formedness predicate
and the gated `d d = 0` assembly, the two presentation values, all agreement theorems (monad /
involution boundaries recovered as evaluations), and the two well-formedness discharges.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.countGeneratorOccurrences
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerPresentationDimOneRow
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerPresentationDimOneRows
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerPresentationDimTwoRow
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerPresentationDimTwoRows
#assert_no_axioms FX1Poly.Polygraph.Homology.WalkerPresentation.computeBasisCount
#assert_no_axioms FX1Poly.Polygraph.Homology.WalkerPresentation.computeBoundaryDimZero
#assert_no_axioms FX1Poly.Polygraph.Homology.WalkerPresentation.computeBoundaryDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.WalkerPresentation.computeBoundaryDimTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.WalkerPresentation.computeBoundaryMatrix
#assert_no_axioms FX1Poly.Polygraph.Homology.sumOverIndicesOfAllZero
#assert_no_axioms FX1Poly.Polygraph.Homology.listGetWithDefaultNilIsDefault
#assert_no_axioms FX1Poly.Polygraph.Homology.listGetReplicateZeroIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerPresentationDimZeroEntryIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerPresentationLoopBoundaryIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.WellFormedWalkerPresentation
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerPresentationBoundaryComposesToZeroOfWellFormed
#assert_no_axioms FX1Poly.Polygraph.Homology.monadWalkerPresentation
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionWalkerPresentation
#assert_no_axioms FX1Poly.Polygraph.Homology.monadPresentationComputesBasisCount
#assert_no_axioms FX1Poly.Polygraph.Homology.monadPresentationComputesBoundaryDimZero
#assert_no_axioms FX1Poly.Polygraph.Homology.monadPresentationComputesBoundaryDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.monadPresentationComputesBoundaryDimTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.monadPresentationComputesBoundaryMatrix
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionPresentationComputesBasisCount
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionPresentationComputesBoundaryDimZero
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionPresentationComputesBoundaryDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionPresentationComputesBoundaryDimTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionPresentationComputesBoundaryMatrix
#assert_no_axioms FX1Poly.Polygraph.Homology.monadPresentationIsWellFormed
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionPresentationIsWellFormed

end FX1PolyAudit
