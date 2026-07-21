import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.EndomorphismCharPolyThree

/-! # EndomorphismCharPolyThree — zero-axiom gate

Per-declaration zero-axiom gate for the characteristic polynomial via principal minors: the three
elementary-symmetric coefficients at dimension `3`, the coefficient triple, the dissimilarity
predicate, the per-matrix groundings, and the equal-trace/equal-det/equal-rank separator.  Confirms
freedom from `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

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

end FX1PolyAudit
