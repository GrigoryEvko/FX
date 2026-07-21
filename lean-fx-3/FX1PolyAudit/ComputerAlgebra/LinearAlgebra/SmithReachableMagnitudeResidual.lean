import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithReachableMagnitudeResidual

/-! # SmithReachableMagnitudeResidual — zero-axiom gate

Per-declaration axiom audit for the magnitude-residual assembly: the forward bridge, the antisymmetry
converse, their equivalence, and the driver collapse onto the residual.  Each declaration must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`; both the fuel-based
`#assert_no_axioms` and the independent `#print axioms` are run on every one. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.landedDividesMinorGcdReachableOfAbsEq
#assert_no_axioms FX1Poly.ComputerAlgebra.landedAbsEqMinorGcdReachableOfDivides
#assert_no_axioms FX1Poly.ComputerAlgebra.landedDividesMinorGcdReachableIffAbsEq
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceCompleteDriverOfLandedAbsEqMinorGcdReachable

#print axioms FX1Poly.ComputerAlgebra.landedDividesMinorGcdReachableOfAbsEq
#print axioms FX1Poly.ComputerAlgebra.landedAbsEqMinorGcdReachableOfDivides
#print axioms FX1Poly.ComputerAlgebra.landedDividesMinorGcdReachableIffAbsEq
#print axioms FX1Poly.ComputerAlgebra.smithReduceCompleteDriverOfLandedAbsEqMinorGcdReachable

end FX1PolyAudit
