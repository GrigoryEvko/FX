import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.NatModularReduction

/-! # FX1PolyAudit/ComputerAlgebra/Number/NatModularReduction — zero-axiom gate

Per-declaration zero-axiom gate for the propext-clean `mod 2^n` reasoning layer:
the structural remainder/quotient, the reconstruction/bound lifts, the
uniqueness crux, the two base identities, the add/mul homomorphism steps, and the
additive-inverse plumbing.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.natRemainder
#assert_no_axioms FX1Poly.ComputerAlgebra.natQuotient
#assert_no_axioms FX1Poly.ComputerAlgebra.natRemainderReconstructs
#assert_no_axioms FX1Poly.ComputerAlgebra.natRemainderIsBounded
#assert_no_axioms FX1Poly.ComputerAlgebra.natRemainderUnique
#assert_no_axioms FX1Poly.ComputerAlgebra.natRemainderOfLt
#assert_no_axioms FX1Poly.ComputerAlgebra.natRemainderSelf
#assert_no_axioms FX1Poly.ComputerAlgebra.natRemainderAddMultiple
#assert_no_axioms FX1Poly.ComputerAlgebra.natRemainderAddPush
#assert_no_axioms FX1Poly.ComputerAlgebra.natRemainderMulPush
#assert_no_axioms FX1Poly.ComputerAlgebra.natAddSubCancelLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.natAddSubOfLe

end FX1PolyAudit
