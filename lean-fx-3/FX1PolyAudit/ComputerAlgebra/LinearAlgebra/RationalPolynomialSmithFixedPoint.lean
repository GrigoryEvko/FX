import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalPolynomialSmithFixedPoint

/-! # FX1PolyAudit/.../RationalPolynomialSmithFixedPoint — zero-axiom gate

Per-declaration zero-axiom gate for the ℚ[x] Smith cross fixed point: the cross measure (T1), the
reduced-cross predicate and driver with the Euclidean-residue stability lemmas (T2), and the submatrix
extractor (T3), plus the fires and content markers.

Every definition is structural on the list, the positional index, or the `Nat` fuel; every specification
routes through the committed measure/reconstruction lemmas and the calibrated-clean `Nat` order lemmas.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `funext`,
`WellFounded.fix`. -/

namespace FX1PolyAudit

-- T1 the cross measure
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfEntryWeight
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfRowWeight
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfRowWeightExcept
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfColumnWeight
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfColumnWeightExcept
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfCrossDegreeSum

-- T2 the reduced-cross predicate and driver
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfIsBelowPivot
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfCrossIsReduced
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfClearCross
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfClearCrossIterate

-- T2 the Euclidean-residue stability lemmas
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfDivModSmallRemainder
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfClearAgainstStableBelowPivot
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfDivModZeroDividend
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfClearZeroTrimsZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfClearAgainstPreservesBelow

-- T2 reaching the reduced cross
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfClearCrossReachesReducedCross
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfClearCrossIterateReduced

-- T3 the submatrix extractor
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfDropEntry
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfDropRow
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfDropColumn
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfSubmatrix

-- Fires
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfFireCrossMeasureValue
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfFireCrossMeasureAfterClearIsZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfFireIterateMeasureZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfFireClearStableConstant
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfFireClearStableTheorem
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfFireDriverReachesReduced
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfFireIterateReachesReduced
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfFireSubmatrix

-- Content marker
#assert_no_axioms FX1Poly.ComputerAlgebra.rsfHasReducedCrossFixedPoint

end FX1PolyAudit
