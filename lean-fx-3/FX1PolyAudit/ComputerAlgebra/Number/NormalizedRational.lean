import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.NormalizedRational

/-! # FX1PolyAudit/ComputerAlgebra/Number/NormalizedRational — zero-axiom gate
    (NUM-Q-7)

Per-declaration zero-axiom gate for the canonical-NF ℚ carrier: the reduced-pair
bundle `QnfRat` (equality of the bundle IS equality of the pair, by structure eta
plus definitional proof irrelevance), THE HEADLINE normalization uniqueness
(`qnfNormalizeUnique` / `qnfNormalizeEqIffDenotesSame`) with fixed-point and
round-trip laws, the ring operations as raw-op-then-normalize with negation and
inversion staying canonical directly, the FULL field-law suite in plain `Eq`
(transported through uniqueness from the setoid laws, never re-proved), the
zero-numerator collapse chain feeding the `value ≠ qnfZero` field witness
(`qnfMulInvCancels`), the structural Boolean comparator with `qnfBeqIffEq` and
the manual `DecidableEq`, the kernel-`rfl` closed-value fires, and the DECIDED
markers `qnfHasCanonicalNormalForm` / `qnfHasFieldLaws`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.QnfRat
#assert_no_axioms FX1Poly.ComputerAlgebra.QnfRat.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.QnfRat.reducedPair
#assert_no_axioms FX1Poly.ComputerAlgebra.QnfRat.hasReducedShape
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfToRawPair
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfEqOfPairEq
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfPairEqOfComponentsEq
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfEqOfPairsDenoteSame
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfPairsDenoteSameOfEq
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfEqIffPairsDenoteSame
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfNormalize
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfNormalizeUnique
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfDenotesSameOfNormalizeEq
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfNormalizeEqIffDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfNormalizeFixesCanonical
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfZero
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfOne
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfIntPairIsReduced
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfOfInt
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfZeroNeOne
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfMul
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfSub
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfIntNegPreservesNatAbs
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfNegExactKeepsReducedShape
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfSubEqAddNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfAddComm
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfAddAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfAddZeroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfAddZeroLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfAddNegRight
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfAddNegLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfMulComm
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfMulAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfMulOneRight
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfMulOneLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfMulLeftDistrib
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfMulRightDistrib
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfReducedWithZeroNumeratorIsZeroRational
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfEqZeroOfNumeratorZero
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfNumeratorNonzeroOfNeZero
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfIsApartFromZeroOfNumeratorNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfInvExactKeepsReducedShape
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfInv
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfMulInvCancels
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfInvMulCancels
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfNatBeqSelfIsTrue
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfNatEqOfBeqIsTrue
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfIntBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfIntBeqSelfIsTrue
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfIntEqOfBeqIsTrue
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfBoolAndTrueGivesLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfBoolAndTrueGivesRight
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfBeqSelfIsTrue
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfBeqIffEq
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfDecEq
#assert_no_axioms FX1Poly.ComputerAlgebra.instBEqQnfRat
#assert_no_axioms FX1Poly.ComputerAlgebra.instDecidableEqQnfRat
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfFireNormalizeTwoFourths
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfFireNormalizeTwoFourthsPair
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfFireNormalizeNegative
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfFireZeroCollapse
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfFireAddHalfThird
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfFireSubHalfThird
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfFireMulHalfTwoThirds
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfFireInvCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfFireBeqComputes
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfHasCanonicalNormalForm
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfHasFieldLaws

end FX1PolyAudit
