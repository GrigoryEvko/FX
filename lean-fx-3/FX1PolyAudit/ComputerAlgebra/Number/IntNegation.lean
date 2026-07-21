import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.IntNegation

/-! # Zero-axiom gate for `IntNegation`

Per-declaration zero-axiom gate for the negation-versus-addition and
negation-versus-multiplication relations and their `negOfNat`/`subNatNat` helpers. Every
declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, and `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.intNegNegOfNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegSubNatNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegMul
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegSub

end FX1PolyAudit
