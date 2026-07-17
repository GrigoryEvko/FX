import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.EndomorphismCharPolyThree

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/EndomorphismCharPolyThree — zero-axiom gate

Per-declaration zero-axiom gate for the WP-ENDO r2 characteristic polynomial via principal minors (the
`charMatrixCarrier` wall): the three elementary-symmetric coefficients at dimension `3` (trace, sum of
principal `2×2` minors, determinant), the char-poly coefficient triple, the char-poly dissimilarity
predicate, the per-matrix groundings, the equal-trace/equal-det/equal-rank separation certificate, and
the marker.

The char poly is computed with NO polynomial ring: its coefficients are sums of principal minors, read
off the function-valued general minor selector ([[EndomorphismMinorSelector]]).  The dissimilarity
certificate refutes the coefficient-triple equality by projecting the middle component and closing with
`Int`/`Nat.noConfusion`, so the file stays free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The three elementary-symmetric coefficients at dimension `3`.
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismTraceThree
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismPrincipalTwoMinorSumThree
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismDeterminantThree

-- The char-poly coefficient triple + its dissimilarity predicate.
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismCharPolyThree
#assert_no_axioms FX1Poly.ComputerAlgebra.EndomorphismDissimilarByCharPolyThree

-- The per-matrix groundings + the equal-trace/equal-det/equal-rank separator.
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismCharPolyThreeIdentityExample
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismCharPolyThreeDiagOnePlusMinusExample
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismCharPolyThreeDiagTwoPlusMinusExample
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismCharPolyThreeSeparatesEqualTraceEqualDetEqualRank

-- The marker.
#assert_no_axioms FX1Poly.ComputerAlgebra.fxEndo_hasCharPolyViaPrincipalMinors

end FX1PolyAudit
