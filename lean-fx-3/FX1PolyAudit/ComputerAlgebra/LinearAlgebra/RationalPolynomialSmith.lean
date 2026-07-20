import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalPolynomialSmith

/-! # FX1PolyAudit/.../RationalPolynomialSmith — zero-axiom gate

Per-declaration zero-axiom gate for the ℚ[x] Smith pivot search (T1) and cross clear (T2): the
min-by-degree pickers and the recursive search functions, the min-by-degree picking laws, the
`rsmRowMin`/`rsmMatrixMin` step equations, the bundled soundness predicates and proofs, the top-level
pivot-search corollaries, the per-entry cross-clear maps with accessor/measure/reconstruction lemmas,
the fires, and the content markers.

Every definition is structural on the list and the positional index; every specification routes through
the shipped `qnf*` field laws, the committed pivot-clear lemmas, and the calibrated-clean `Nat` order
lemmas.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`,
`funext`, `WellFounded.fix`. -/

namespace FX1PolyAudit

-- T1 pivot search: min-by-degree helpers and the search functions
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmMinByDegree
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmMinByDegreeTriple
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmRowMin
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmMatrixMin
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmPivotSearch

-- T1 min-by-degree picking laws
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmMinByDegreeEq
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmMinByDegreeLeA
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmMinByDegreeLeB
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmMinByDegreeTripleEq
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmMinByDegreeTripleLeA
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmMinByDegreeTripleLeB

-- T1 rsmRowMin / rsmMatrixMin step equations
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmRowMinConsZeroNone
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmRowMinConsZeroSome
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmRowMinConsNonzeroNone
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmRowMinConsNonzeroSome
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmMatrixMinConsZeroNone
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmMatrixMinConsZeroSome
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmMatrixMinConsNonzeroNone
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmMatrixMinConsNonzeroSome

-- T1 bundled soundness predicates and proofs
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmRowMinSound
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmRowMinSoundHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmMatrixMinSound
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmMatrixMinSoundHolds

-- T1 top-level pivot-search corollaries
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmPivotSearchEqNone
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmPivotSearchEqSome
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmPivotSearchSomeSound
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmPivotSearchNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmPivotSearchMinimal
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmPivotSearchNoneAllZero

-- T2 cross-clear definitions
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmClearAgainst
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmColumnClearAll
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmRowClearExcept
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmClearRowAtCol
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmColumnClearBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmCrossClear

-- T2 accessor lemmas
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmColumnClearAllGet
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmColumnClearAllMeasure
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmColumnClearAllReconstructs
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmRowClearExceptGetSkip
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmRowClearExceptGetOther
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmClearRowAtColGetAt
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmColumnClearBelowGet
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmCrossClearRowGetPivot
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmCrossClearRowGetOther

-- T2 cross-clear specification
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmCrossClearPivotPreserved
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmCrossClearRowMeasure
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmCrossClearColMeasure
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmCrossClearRowReconstructs
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmCrossClearColReconstructs

-- Fires
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmFireMatrix
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmFireZeroMatrix
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmFirePivotSearchFindsConstant
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmFirePivotEntry
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmFirePivotSearchNoneOnZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmFirePivotSearchZeroIsSomeFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmFirePivotSearchNonzeroIsSomeTrue
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmFirePivotSearchNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmFirePivotSearchMinimalAtCorner
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmFirePivotSearchNoneAllZeroAt
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmFireCrossClearRowAnnihilates
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmFireCrossClearColAnnihilates
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmFireCrossClearPivotPreserved
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmFireCrossClearOffCrossUntouched
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmFireCrossClearColMeasure
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmFireCrossClearDegreeDrops
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmFireCrossClearReconstructs

-- Content markers
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmHasPivotSearch
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmHasCrossClear
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmHasCrossFixedPoint
#assert_no_axioms FX1Poly.ComputerAlgebra.rsmHasSmithNormalForm

end FX1PolyAudit
