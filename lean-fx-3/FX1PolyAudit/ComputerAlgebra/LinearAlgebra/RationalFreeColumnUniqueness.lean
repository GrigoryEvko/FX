import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalFreeColumnUniqueness

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/RationalFreeColumnUniqueness —
    zero-axiom gate (WP-PROP-3 last brick: free-column coordinate uniqueness →
    RREF uniqueness over QnfRat)

Per-declaration zero-axiom gate for the reduced-basis support characterization
(`rfcZeroAtEveryPivotIsZeroRow`, `rfcReducedSupportUnique`) with its negated-
coefficient helper; the structural helpers for the abstract induction
(`rfcLeadZeroRowNone`, `rfcHasLeadConsMonotone`, `rfcPivotGeHeadLead`,
`rfcTailSpanOfHeadZero`); the reduction-engine lemmas
(`rfcReduceCoeffWhereRowsZero`, `rfcLeadOfBelowZeroNonzero`,
`rfcReduceZeroAtEveryLead`, `rfcEchelonRowsCoeffZeroLe`); the back-reduce
structural theorem `rfcBackReduceEchelonReduced`; the abstract reduced-echelon
uniqueness (`RfcIsReducedEchelonFrom`, `rfcReducedEchelonUniqueFrom`,
`rfcReducedEchelonUnique`); the concrete `rreRref` closure
(`rfcMapNormalizeHasLead`, `rfcNormalizeCoeffZero`, `rfcRreRrefIsReducedEchelon`,
`rfcRreRrefUnique`, `rfcRreRrefUniqueOfSpanEqB`); the un-normalized refutation
(`rfcHeadRowCoeff`, `rfcIhqRrefUniquenessRefuted`); the kernel-`rfl` fires and the
DECIDED markers.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`.  Both the fuel-based `#assert_no_axioms` AND
the independent (non-fuel) `#print axioms` are run on every declaration. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.rfcGetCoeffNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcZeroAtEveryPivotIsZeroRow
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcReducedSupportUnique
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcLeadZeroRowNone
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcHasLeadConsMonotone
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcPivotGeHeadLead
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcTailSpanOfHeadZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcReduceCoeffWhereRowsZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcLeadOfBelowZeroNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcReduceZeroAtEveryLead
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcEchelonRowsCoeffZeroLe
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcBackReduceEchelonReduced
#assert_no_axioms FX1Poly.ComputerAlgebra.RfcIsReducedEchelonFrom
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcReducedEchelonUniqueFrom
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcReducedEchelonUnique
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcMapNormalizeHasLead
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcNormalizeCoeffZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcRreRrefIsReducedEchelon
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcRreRrefUnique
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcRreRrefUniqueOfSpanEqB
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcHeadRowCoeff
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcIhqRrefUniquenessRefuted
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcFireSpanEqualSingleRow
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcFireSpanEqualTwoByTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcFireIdentityReduced
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcFireDistinctNonSpanEqual
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcFireIhqRrefNotCanonical
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcHasReducedSupportUniqueness
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcHasBackReduceReducedSupport
#assert_no_axioms FX1Poly.ComputerAlgebra.rfcHasRreRrefUniqueness

end FX1PolyAudit
