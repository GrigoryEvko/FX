import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialGcdConverse

/-! # FX1PolyAudit/.../IntPolynomialGcdConverse — zero-axiom gate

Per-declaration zero-axiom gate for the ℤ[x] GCD converse root-containment (the twelfth brick of
`invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255): the single Euclidean-step converse
(`polyPseudoRemBackwardRoot`, cancelling `leadDivisor^scalePower` off the r10 reconstruction via the r22
arbitrary-sign ℤ no-zero-divisor) carried through the Euclidean recursion under the `Bool`-valued
honest-termination flag `polyGcdReachesNil`, giving `polyGcdRootIsCommonRoot` — every root of an
honestly-terminated GCD is a root of both inputs.

Reconstruction identity + ℤ no-zero-divisor + structural fuel recursion; `Bool` adequacy flag (no
Prop-match), `Bool.noConfusion` / `List.cons_ne_nil` closing the `polyTrim` split.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemBackwardRoot
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEvalZeroOfTrimNil
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdReachesNil
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdRootIsCommonRoot
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemBackwardRootGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdRootIsCommonRootGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdReachesNilGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasGcdConverseRootContainment

end FX1PolyAudit
