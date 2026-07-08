import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntFractionFree

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/IntFractionFree — zero-axiom gate

Per-declaration zero-axiom gate for the concrete integer-matrix builders, the exact cofactor
determinant at ℤ with its identity theorem and concrete evaluations, and the fraction-free
Sasaki–Murao recurrence with its base case and machine-checked agreements.

Confirms the `decide`-discharged evaluations and agreements are free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.gridOfRows
#assert_no_axioms FX1Poly.ComputerAlgebra.setoidMatrixOfRows
#assert_no_axioms FX1Poly.ComputerAlgebra.intCofactorDet
#assert_no_axioms FX1Poly.ComputerAlgebra.intCofactorDetIdentity
#assert_no_axioms FX1Poly.ComputerAlgebra.intCofactorDetTwoByTwoExample
#assert_no_axioms FX1Poly.ComputerAlgebra.intCofactorDetDiagonalExample
#assert_no_axioms FX1Poly.ComputerAlgebra.intCofactorDetDenseExample
#assert_no_axioms FX1Poly.ComputerAlgebra.bareissReduceBlock
#assert_no_axioms FX1Poly.ComputerAlgebra.sasakiMurao
#assert_no_axioms FX1Poly.ComputerAlgebra.sasakiMuraoDet
#assert_no_axioms FX1Poly.ComputerAlgebra.sasakiMuraoDetOne
#assert_no_axioms FX1Poly.ComputerAlgebra.sasakiMuraoAgreesTwoByTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.sasakiMuraoAgreesDiagonal
#assert_no_axioms FX1Poly.ComputerAlgebra.sasakiMuraoAgreesDense

end FX1PolyAudit
