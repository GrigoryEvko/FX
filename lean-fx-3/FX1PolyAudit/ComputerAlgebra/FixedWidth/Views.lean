import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.FixedWidth.Views

/-! # FX1PolyAudit/ComputerAlgebra/FixedWidth/Views — zero-axiom gate

Per-declaration zero-axiom gate for the `uN`/`iN` view facades: the two nominal
wrappers, their equality-of-bits lemmas, constructors, constants, the value
interpretations, the definitional unsigned range, the wrap-by-default
arithmetic, and the sign-sensitive ops.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.UIntN
#assert_no_axioms FX1Poly.ComputerAlgebra.SIntN
#assert_no_axioms FX1Poly.ComputerAlgebra.uIntNEqOfBitsEq
#assert_no_axioms FX1Poly.ComputerAlgebra.sIntNEqOfBitsEq
#assert_no_axioms FX1Poly.ComputerAlgebra.UIntN.ofNat
#assert_no_axioms FX1Poly.ComputerAlgebra.SIntN.ofNat
#assert_no_axioms FX1Poly.ComputerAlgebra.UIntN.zero
#assert_no_axioms FX1Poly.ComputerAlgebra.UIntN.one
#assert_no_axioms FX1Poly.ComputerAlgebra.SIntN.zero
#assert_no_axioms FX1Poly.ComputerAlgebra.SIntN.one
#assert_no_axioms FX1Poly.ComputerAlgebra.UIntN.unsignedValue
#assert_no_axioms FX1Poly.ComputerAlgebra.SIntN.signedValue
#assert_no_axioms FX1Poly.ComputerAlgebra.uIntNValueIsBounded
#assert_no_axioms FX1Poly.ComputerAlgebra.UIntN.add
#assert_no_axioms FX1Poly.ComputerAlgebra.UIntN.mul
#assert_no_axioms FX1Poly.ComputerAlgebra.UIntN.sub
#assert_no_axioms FX1Poly.ComputerAlgebra.SIntN.add
#assert_no_axioms FX1Poly.ComputerAlgebra.SIntN.mul
#assert_no_axioms FX1Poly.ComputerAlgebra.SIntN.sub
#assert_no_axioms FX1Poly.ComputerAlgebra.SIntN.neg
#assert_no_axioms FX1Poly.ComputerAlgebra.UIntN.shr
#assert_no_axioms FX1Poly.ComputerAlgebra.SIntN.ashr
#assert_no_axioms FX1Poly.ComputerAlgebra.SIntN.isNegative

end FX1PolyAudit
