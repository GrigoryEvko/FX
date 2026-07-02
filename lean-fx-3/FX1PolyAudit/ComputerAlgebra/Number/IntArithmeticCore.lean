import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.IntArithmeticCore

/-! # FX1PolyAudit/ComputerAlgebra/Number/IntArithmeticCore — zero-axiom gate (FLOAT-1 brick 1)

Per-declaration zero-axiom gate for the hand-rolled Int commutative core and the re-exported
clean Init survivors.  The re-export gates double as TRIPWIRES: if a toolchain bump dirties
`Int.add_zero`/`Int.one_mul`/`Int.mul_zero`/`Int.neg_neg`/`Int.neg_zero`/`Int.sub_eq_add_neg`,
these fail and the kit hand-rolls the replacement.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.intAddZero
#assert_no_axioms FX1Poly.ComputerAlgebra.intOneMul
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulZero
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegZero
#assert_no_axioms FX1Poly.ComputerAlgebra.intSubEqAddNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.intZeroAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.intAddComm
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulComm
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulOne
#assert_no_axioms FX1Poly.ComputerAlgebra.intZeroMul

end FX1PolyAudit
