import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.NatEuclideanDivision

/-! # FX1PolyAudit/ComputerAlgebra/Number/NatEuclideanDivision — zero-axiom gate
    (FLOAT-1 brick 9)

Per-declaration zero-axiom gate for the structural counting divider: the step function,
the counter, the strictness upgrade, and the reconstruction / remainder-bound /
existence certificates.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.natDivModStep
#assert_no_axioms FX1Poly.ComputerAlgebra.natDivModCounting
#assert_no_axioms FX1Poly.ComputerAlgebra.natLtOfLeOfNe
#assert_no_axioms FX1Poly.ComputerAlgebra.natDivModStepReconstructs
#assert_no_axioms FX1Poly.ComputerAlgebra.natDivModStepRemainderIsBounded
#assert_no_axioms FX1Poly.ComputerAlgebra.natDivModCountingReconstructs
#assert_no_axioms FX1Poly.ComputerAlgebra.natDivModCountingRemainderIsBounded
#assert_no_axioms FX1Poly.ComputerAlgebra.natEuclideanDivisionExists
#assert_no_axioms FX1Poly.ComputerAlgebra.natDivModCountingByOne
#assert_no_axioms FX1Poly.ComputerAlgebra.natLeTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.natLeOfSuccLeSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.natEqZeroOfLeZero
#assert_no_axioms FX1Poly.ComputerAlgebra.natExactQuotientSuccBound
#assert_no_axioms FX1Poly.ComputerAlgebra.natExactQuotientWithinFuel
#assert_no_axioms FX1Poly.ComputerAlgebra.natDivModStepQuotientGrows
#assert_no_axioms FX1Poly.ComputerAlgebra.natDivModCountingQuotientIsMonotone

end FX1PolyAudit
