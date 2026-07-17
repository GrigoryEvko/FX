import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialGcd

/-! # FX1PolyAudit/.../IntPolynomialGcd — zero-axiom gate

Per-declaration zero-axiom gate for the ℤ[x] Euclidean GCD via pseudo-division (the fourth brick of
`invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255): the pseudo-remainder, the GCD algorithm, and the
theorems that the pseudo-remainder and the GCD vanish at every common root of their inputs.

The recursion is structural on `fuel`; the only case analysis is `polyTrim`'s full `nil`/`cons`
enumeration; the vanishing arithmetic routes through the corpus `Int` lemmas.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRem
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemVanishesAtCommonRoot
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdVanishesAtCommonRoot
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdSharesCommonRootAtMinusOne
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemSharesCommonRootAtMinusOne
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasEuclideanGcdCommonRoots

end FX1PolyAudit
