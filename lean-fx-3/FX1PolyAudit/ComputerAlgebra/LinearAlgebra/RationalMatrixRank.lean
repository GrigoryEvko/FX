import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalMatrixRank

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/RationalMatrixRank — zero-axiom
    gate (WP-PROP-3 keystone: rank / pivot-column apparatus over QnfRat)

Per-declaration zero-axiom gate for the rank apparatus: the structural `ihqNatLe`
kit (add-monotone, antisymmetry, strict-comparator transitivity), the rank
function `rmrRank` with its lead-length helper, echelon length bound and the
width bound `rmrRankLeWidth`; the pivot-preservation nucleus
`rmrReduceCoeffMissingPivot` with `rmrElimStepCoeffWhereZero` and
`rmrNatCompareSelf`; the pivot-column predicate `rmrHasLead` with its unfoldings
and true/false specs, the pivot-column determination theorem
`rmrAchievableLeadIsPivot` and pivot-SET span invariance
`rmrPivotSetSpanInvariant`; the comparator flip, the echelon-above-false lemma,
the drop-head lemma, the dimension inequality `rmrLeadDominationLe` and the
dimension theorem `rmrRankSpanInvariant`; the owner-false RREF-row-uniqueness
wall; the kernel-`rfl` fires and the DECIDED markers.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.rmrNatLeAddMonoRight
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrNatLeAntisymm
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrNatCompareLtTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrRank
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrLeadLtLength
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrEchelonLengthBound
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrRankLeWidth
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrNatCompareSelf
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrElimStepCoeffWhereZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrReduceCoeffMissingPivot
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrHasLead
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrHasLeadConsShape
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrHasLeadConsNone
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrHasLeadConsSome
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrHasLeadFalseNoPivot
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrHasLeadTrueMember
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrAchievableLeadIsPivot
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrPivotSetSpanInvariant
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrNatCompareGtOfLtFlip
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrHasLeadFalseOfEchelonAbove
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrHasLeadDropHead
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrLeadDominationLe
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrRankSpanInvariant
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrHasRrefRowUniqueness
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrFireRankDependentIsOne
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrFireRankIdentityIsTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrFireRankSingleRow
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrFireRankNilIsZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrFirePivotSingleRowAtZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrFirePivotSpanEqualAgree
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrFirePivotYaxisMissesZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrFirePivotYaxisAtOne
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrFireRankPivotControlPresent
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrFireRankPivotControlAbsent
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrHasRankApparatus
#assert_no_axioms FX1Poly.ComputerAlgebra.rmrHasPivotSetInvariance

end FX1PolyAudit
