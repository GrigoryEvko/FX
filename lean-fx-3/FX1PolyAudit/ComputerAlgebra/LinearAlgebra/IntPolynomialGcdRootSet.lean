import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialGcdRootSet

/-! # FX1PolyAudit/.../IntPolynomialGcdRootSet — zero-axiom gate

Per-declaration zero-axiom gate for the ℤ[x] GCD root-set identity (the thirteenth brick of
`invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255): the GCD's roots are exactly the common roots
(`polyGcdRootIffCommonRoot`), plus the eigenvalue-sharing shadow.

Pure `Iff.intro` / `And` packaging over the two directional theorems, no new recursion.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdRootIffCommonRoot
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdNoRootOfNoCommonRoot
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdSharedRootIsEigenvalueShadow
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdRootIffCommonRootGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasGcdRootSetIdentity

end FX1PolyAudit
