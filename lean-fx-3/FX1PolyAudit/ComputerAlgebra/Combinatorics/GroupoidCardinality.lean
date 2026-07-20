import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Combinatorics.GroupoidCardinality

/-! # FX1PolyAudit/ComputerAlgebra/Combinatorics/GroupoidCardinality —
    zero-axiom gate (CSHD)

Per-declaration zero-axiom gate for finite-groupoid cardinality as
decategorification: the scalar `QnfRat` bricks (multiplicative zero,
middle-four, inverse uniqueness, product-nonzero, inverse distributivity, the
ℤ/ℕ multiplicative homomorphisms), the reciprocal-multiplicativity `1/(a·b) =
(1/a)·(1/b)`, the carrier `FgcGroupoid` with its cardinality, the disjoint-union
= addition law with unit laws, the product = multiplication law with point-unit
laws, the non-injectivity witness, the three WALLED markers, the content
markers, and the closed-value fires.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.fgcMulZeroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcMulZeroLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcMulMiddleFour
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcInverseUnique
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcMulNeZero
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcInvMulDistrib
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcRatOfIntMul
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcNatToRat
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcNatToRatMul
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcNatToRatSuccNeZero
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcNatMulZeroLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.FgcGroupoid
#assert_no_axioms FX1Poly.ComputerAlgebra.FgcGroupoid.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.FgcGroupoid.autOrders
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcReciprocal
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcReciprocalSum
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcCardinality
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcOrderIsPositive
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcAllOrdersPositive
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcIsWellFormed
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcEmpty
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcPoint
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcTwoAut
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcThreeAut
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcTwoPoints
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcTwoHalves
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcListCat
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcDisjointUnion
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcReciprocalSumCat
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcCardinalityUnion
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcCardinalityUnionEmptyRight
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcCardinalityUnionEmptyLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcReciprocalMul
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcProductRow
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcProductOrders
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcProduct
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcProductRowSum
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcProductOrdersSum
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcCardinalityProduct
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcCardinalityPoint
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcCardinalityProductPointRight
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcCardinalityProductPointLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcHasInverseCategorification
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcHasInfiniteGroupoidCardinality
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcHasGroupoidEquivalenceDecision
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcInverseAmbiguityWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcHasGroupoidCardinality
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcHasDecategorificationLaws
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcFireEmptyCardinality
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcFireTwoAutCardinality
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcFireTwoPointsCardinality
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcFireUnionAddition
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcFireProductOrdersSixth
#assert_no_axioms FX1Poly.ComputerAlgebra.fgcFireProductSixthValue

end FX1PolyAudit
