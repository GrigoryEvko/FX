import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialInvariantFactors

/-! # FX1PolyAudit/.../IntPolynomialInvariantFactors — zero-axiom gate

Per-declaration zero-axiom gate for the dimension-2 invariant factors and the rational-canonical-form block
count: `s_2 = d_2 / d_1` via monic division (exact for the derogatory scalar, whose invariant factors
`[x−2, x−2]` reconstruct `(x−2)²`) and the block count `1 + deg d_1`, a decidable similarity invariant
separating `2·I` (`2` blocks) from the Jordan block `[[2,1],[0,2]]` (`1` block), which share char poly
`(x−2)²`.  Monic division + `polyDegree` + `decide` groundings + a `Nat` inequality.  Free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.invariantFactorSecond
#assert_no_axioms FX1Poly.ComputerAlgebra.invariantFactorsTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.rationalFormBlockCountTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.invariantFactorsScalarAreRepeatedLinear
#assert_no_axioms FX1Poly.ComputerAlgebra.invariantFactorsScalarReconstructCharPoly
#assert_no_axioms FX1Poly.ComputerAlgebra.rationalFormBlockCountScalarIsTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.rationalFormBlockCountJordanIsOne
#assert_no_axioms FX1Poly.ComputerAlgebra.rationalFormBlockCountDiagDistinctIsOne
#assert_no_axioms FX1Poly.ComputerAlgebra.DissimilarByBlockCount
#assert_no_axioms FX1Poly.ComputerAlgebra.scalarNotSimilarToJordanByBlockCount

end FX1PolyAudit
