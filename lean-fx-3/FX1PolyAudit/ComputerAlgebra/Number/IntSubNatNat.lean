import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.IntSubNatNat

/-! # Zero-axiom gate for `IntSubNatNat`

Per-declaration zero-axiom gate for the `subNatNat` case-analysis kit: the bridge function,
the computation lemmas, and additive-inverse cancellation. Every declaration must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, and `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.subNatNatFromDifferences
#assert_no_axioms FX1Poly.ComputerAlgebra.subNatNatAsDifferences
#assert_no_axioms FX1Poly.ComputerAlgebra.intSubNatNatSuccSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.intSubNatNatZeroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.intSubNatNatZeroLeftSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.intSubNatNatShiftInvariant
#assert_no_axioms FX1Poly.ComputerAlgebra.intSubNatNatSelf
#assert_no_axioms FX1Poly.ComputerAlgebra.intSubNatNatLeftSurplus
#assert_no_axioms FX1Poly.ComputerAlgebra.intSubNatNatRightSurplus
#assert_no_axioms FX1Poly.ComputerAlgebra.intAddRightNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.intAddLeftNeg

end FX1PolyAudit
