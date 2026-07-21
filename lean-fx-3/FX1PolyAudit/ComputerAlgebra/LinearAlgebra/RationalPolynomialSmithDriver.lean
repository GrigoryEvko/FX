import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalPolynomialSmithDriver

/-! # FX1PolyAudit/.../RationalPolynomialSmithDriver — zero-axiom gate

Per-declaration zero-axiom gate for the ℚ[x] Smith re-pivot DRIVER and the all-zero cross.  Covers T1 (the
re-pivot step `rseRepivotStep` with its column/row strict-drop lemmas and the moved-pivot reconstruction),
T2a (the cross search `rseCrossSearch` with the four structural soundness lemmas and the combined
none/some soundness), and T2b (the driver `rseRepivotDriver`, the constant-pivot base case, and the
all-zero-cross termination `rseRepivotDriverReachesAllZeroCross`), plus the fires and content markers.

Every definition is structural on the list, the positional index, or the `Nat` fuel; every specification
routes through the committed cross-clear measure/reconstruction lemmas and the calibrated-clean `Nat` order
lemmas.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `funext`,
`WellFounded.fix`. -/

namespace FX1PolyAudit

-- The measure and the all-zero cross predicate
#assert_no_axioms FX1Poly.ComputerAlgebra.rsePivotDegree
#assert_no_axioms FX1Poly.ComputerAlgebra.rseCrossIsAllZero

-- T1 the re-pivot step and its strict-drop / reconstruction lemmas
#assert_no_axioms FX1Poly.ComputerAlgebra.rseRepivotStep
#assert_no_axioms FX1Poly.ComputerAlgebra.rseClearedColumnEntry
#assert_no_axioms FX1Poly.ComputerAlgebra.rseClearedRowEntry
#assert_no_axioms FX1Poly.ComputerAlgebra.rseStepColumnStrictDrop
#assert_no_axioms FX1Poly.ComputerAlgebra.rseStepRowStrictDrop
#assert_no_axioms FX1Poly.ComputerAlgebra.rseStepColumnReconstructs

-- T2a the cross search definitions
#assert_no_axioms FX1Poly.ComputerAlgebra.rseRowSearchAll
#assert_no_axioms FX1Poly.ComputerAlgebra.rseRowSearchExcept
#assert_no_axioms FX1Poly.ComputerAlgebra.rseColumnSearchAll
#assert_no_axioms FX1Poly.ComputerAlgebra.rseColumnSearchExcept
#assert_no_axioms FX1Poly.ComputerAlgebra.rseCrossSearch

-- T2a search step equations
#assert_no_axioms FX1Poly.ComputerAlgebra.rseRowSearchAllConsZeroNone
#assert_no_axioms FX1Poly.ComputerAlgebra.rseRowSearchAllConsZeroSome
#assert_no_axioms FX1Poly.ComputerAlgebra.rseRowSearchAllConsNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.rseColumnSearchAllConsZeroNone
#assert_no_axioms FX1Poly.ComputerAlgebra.rseColumnSearchAllConsZeroSome
#assert_no_axioms FX1Poly.ComputerAlgebra.rseColumnSearchAllConsNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.rseRowSearchExceptConsSkipNone
#assert_no_axioms FX1Poly.ComputerAlgebra.rseRowSearchExceptConsSkipSome
#assert_no_axioms FX1Poly.ComputerAlgebra.rseRowSearchExceptConsZeroNone
#assert_no_axioms FX1Poly.ComputerAlgebra.rseRowSearchExceptConsZeroSome
#assert_no_axioms FX1Poly.ComputerAlgebra.rseRowSearchExceptConsNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.rseColumnSearchExceptConsSkipNone
#assert_no_axioms FX1Poly.ComputerAlgebra.rseColumnSearchExceptConsSkipSome
#assert_no_axioms FX1Poly.ComputerAlgebra.rseColumnSearchExceptConsZeroNone
#assert_no_axioms FX1Poly.ComputerAlgebra.rseColumnSearchExceptConsZeroSome
#assert_no_axioms FX1Poly.ComputerAlgebra.rseColumnSearchExceptConsNonzero

-- T2a search soundness
#assert_no_axioms FX1Poly.ComputerAlgebra.rseRowSearchAllSound
#assert_no_axioms FX1Poly.ComputerAlgebra.rseRowSearchAllSoundHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.rseRowSearchExceptSound
#assert_no_axioms FX1Poly.ComputerAlgebra.rseRowSearchExceptSoundHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.rseColumnSearchAllSound
#assert_no_axioms FX1Poly.ComputerAlgebra.rseColumnSearchAllSoundHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.rseColumnSearchExceptSound
#assert_no_axioms FX1Poly.ComputerAlgebra.rseColumnSearchExceptSoundHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.rseCrossSearchNoneAllZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rseCrossSearchSomeCross

-- T2b the driver, its step equations, base case, and termination
#assert_no_axioms FX1Poly.ComputerAlgebra.rseRepivotDriver
#assert_no_axioms FX1Poly.ComputerAlgebra.rseRepivotDriverZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rseRepivotDriverSuccNone
#assert_no_axioms FX1Poly.ComputerAlgebra.rseRepivotDriverSuccSome
#assert_no_axioms FX1Poly.ComputerAlgebra.rseConstantPivotClearsCross
#assert_no_axioms FX1Poly.ComputerAlgebra.rseRepivotDriverReachesAllZeroCross

-- Fires
#assert_no_axioms FX1Poly.ComputerAlgebra.rseFireMatrix
#assert_no_axioms FX1Poly.ComputerAlgebra.rseFirePivotDegreeTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.rseFirePivotSearch
#assert_no_axioms FX1Poly.ComputerAlgebra.rseFireFirstClearLeavesResidue
#assert_no_axioms FX1Poly.ComputerAlgebra.rseFireStepNewPivotDegree
#assert_no_axioms FX1Poly.ComputerAlgebra.rseFireStepStrictDrop
#assert_no_axioms FX1Poly.ComputerAlgebra.rseFireDriverFinalPosition
#assert_no_axioms FX1Poly.ComputerAlgebra.rseFireDriverCrossZeroRow
#assert_no_axioms FX1Poly.ComputerAlgebra.rseFireDriverCrossZeroCol
#assert_no_axioms FX1Poly.ComputerAlgebra.rseFireDriverReachesAllZeroCross

-- Content marker
#assert_no_axioms FX1Poly.ComputerAlgebra.rseHasAllZeroCrossViaRepivot

end FX1PolyAudit
