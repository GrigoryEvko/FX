import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.IntOrderCore

/-! # FX1PolyAudit/ComputerAlgebra/Number/IntOrderCore — zero-axiom gate (FLOAT-1 brick 7)

Per-declaration zero-axiom gate for the additive-witness order core: the `NonNeg`
destructor, the witness intro/dest interface, the `OfEq` rewriting helpers, and the
hand-rolled refl/trans/antisymm laws.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.intNonNegDest
#assert_no_axioms FX1Poly.ComputerAlgebra.intLessEqualOfEqRight
#assert_no_axioms FX1Poly.ComputerAlgebra.intLessEqualOfEqLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.intLessEqualIntro
#assert_no_axioms FX1Poly.ComputerAlgebra.intLessEqualDest
#assert_no_axioms FX1Poly.ComputerAlgebra.intLessThanAsSuccLessEqual
#assert_no_axioms FX1Poly.ComputerAlgebra.intLessEqualRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.intLessEqualTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.natAddEqZeroLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.intAddLeftCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.intLessEqualAntisymm
#assert_no_axioms FX1Poly.ComputerAlgebra.intLtOrEqOfLe

end FX1PolyAudit
