import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalPolynomialBezout

/-! # FX1PolyAudit/.../RationalPolynomialBezout — zero-axiom gate

Per-declaration zero-axiom gate for the trim-level `rpxMul` commutativity (convolution symmetry), the Bezout
identity over ℚ[x], and the Smith pivot-clear seed: the negation/multiplication interaction laws, the
convolution coefficient laws (right-nil, right-cons decomposition, symmetry), `rbzMulCommTrim` with its
left-trim-congruence and divisibility transitivity, the additive-cancellation trim lemma, the
Euclidean-step cofactor rewrite, the fuel-structural Bezout invariant and identity, the ℚ[x]-matrix carrier
with pivot-clear (first pivot lemma + reconstruction) and column clear, the fires, and the content markers.

Every convolution/negation law is structural on the coefficient list; every trim-level law routes through the
coefficient bridge and the shipped `qnf*` field laws; the Bezout recursion is structural on `fuel`.  Must be
free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `funext`,
`WellFounded.fix`. -/

namespace FX1PolyAudit

-- Derived QnfRat and additive-rearrangement helpers
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzQnfMulNegLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzQnfAddSwap
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzQnfCombineCancel

-- T1a: the negation/multiplication interaction laws (plain Eq)
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzNegScale
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzNegAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzMulNegLeft

-- T1b: the convolution coefficient laws
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzMulNilRightCoeff
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzMulRightConsCoeff
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzMulCommCoeff
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzMulCommTrim
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzMulRespectsTrimLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzDividesTrans

-- T2: the Bezout identity
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzCombineCancelTrim
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzComboRewrite
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzBezoutInvariant
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzBezoutIdentity

-- T3: the Smith pivot-clear seed
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzPolyMatrix
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzRowGet
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzEntryGet
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzMatrixEntry
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzClearEntry
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzColumnClear
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzClearEntryReducesDegree
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzClearEntryReconstructs

-- Fires
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzFireMulCommTrimClosed
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzFireMulCommTrimTheorem
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzFireBezoutExplicitCofactors
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzFireBezoutIdentityDifferenceOfSquares
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzFireDividesTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzFireClearEntryReducesDegree
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzFireColumnClearAnnihilatesFirst
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzFireMatrixEntry
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzFireClearReconstructs

-- Content marker
#assert_no_axioms FX1Poly.ComputerAlgebra.rbzHasBezoutIdentity

end FX1PolyAudit
