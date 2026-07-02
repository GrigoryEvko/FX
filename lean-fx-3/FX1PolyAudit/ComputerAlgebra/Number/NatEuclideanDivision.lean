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

end FX1PolyAudit
