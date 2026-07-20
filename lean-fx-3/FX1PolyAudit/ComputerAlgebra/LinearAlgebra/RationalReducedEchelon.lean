import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalReducedEchelon

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/RationalReducedEchelon — zero-axiom
    gate (WP-PROP-3 canonicity leg: leading-1 RREF normalization)

Per-declaration zero-axiom gate for the QnfRat leading-1 normalization pass: the
scalar telescopes (nonzero-product, nonzero-inverse, scale zero-comparison,
right cancellation), lead preservation under nonzero scaling, the row
normalizer `rreNormalizeRow` with its unfoldings/length/lead-preservation/unit-
lead and the rank-1 scale-invariance nucleus, the normalize-map span invariance
and echelon preservation, the canonicalizers `rreRef`/`rreRref` with width, the
`RreIsUnitEchelon` predicate and its certification, the reduced-form unit-lead
certificate, both span iffs and their Bool pins, the owner-false RREF-uniqueness
wall marker, the kernel-`rfl` fires (single-row normalization, 2×2 to identity,
concrete span-equal convergence, axis FALSE controls), and the DECIDED markers.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.rreQnfMulNeZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rreQnfInvNeZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rreQnfMulBeqZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rreQnfMulRightCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.rreLeadScaleEq
#assert_no_axioms FX1Poly.ComputerAlgebra.rreNormalizeRow
#assert_no_axioms FX1Poly.ComputerAlgebra.rreNormalizeRowNone
#assert_no_axioms FX1Poly.ComputerAlgebra.rreNormalizeRowSome
#assert_no_axioms FX1Poly.ComputerAlgebra.rreNormalizeRowLength
#assert_no_axioms FX1Poly.ComputerAlgebra.rreNormalizeRowLeadEq
#assert_no_axioms FX1Poly.ComputerAlgebra.rreNormalizeRowUnitLead
#assert_no_axioms FX1Poly.ComputerAlgebra.rreScaleAllZeroRow
#assert_no_axioms FX1Poly.ComputerAlgebra.rreNormalizeRowScaleInvariant
#assert_no_axioms FX1Poly.ComputerAlgebra.rreNormalizeRowInSpan
#assert_no_axioms FX1Poly.ComputerAlgebra.rreNormMapSpanIff
#assert_no_axioms FX1Poly.ComputerAlgebra.rreMapEchelonFrom
#assert_no_axioms FX1Poly.ComputerAlgebra.rreRef
#assert_no_axioms FX1Poly.ComputerAlgebra.rreRref
#assert_no_axioms FX1Poly.ComputerAlgebra.rreRefWidth
#assert_no_axioms FX1Poly.ComputerAlgebra.rreRrefWidth
#assert_no_axioms FX1Poly.ComputerAlgebra.RreIsUnitEchelon
#assert_no_axioms FX1Poly.ComputerAlgebra.rreRefIsUnitEchelon
#assert_no_axioms FX1Poly.ComputerAlgebra.rreRrefAllUnitLead
#assert_no_axioms FX1Poly.ComputerAlgebra.rreRefSpanIff
#assert_no_axioms FX1Poly.ComputerAlgebra.rreRrefSpanIff
#assert_no_axioms FX1Poly.ComputerAlgebra.rreRefSpanEqB
#assert_no_axioms FX1Poly.ComputerAlgebra.rreRrefSpanEqB
#assert_no_axioms FX1Poly.ComputerAlgebra.rreHasRrefUniqueness
#assert_no_axioms FX1Poly.ComputerAlgebra.rreFireNormalizeSingleRow
#assert_no_axioms FX1Poly.ComputerAlgebra.rreFireIdentityTwoByTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.rreFireSpanEqualConverge
#assert_no_axioms FX1Poly.ComputerAlgebra.rreFireFalseControlFirst
#assert_no_axioms FX1Poly.ComputerAlgebra.rreFireFalseControlSecond
#assert_no_axioms FX1Poly.ComputerAlgebra.rreFireDistinctRrefNonSpanEqual
#assert_no_axioms FX1Poly.ComputerAlgebra.rreHasUnitLeadCanonicalizer
#assert_no_axioms FX1Poly.ComputerAlgebra.rreHasSpanInvariance

end FX1PolyAudit
