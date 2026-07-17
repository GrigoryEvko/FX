import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialPseudoDegreeDecrease

/-! # FX1PolyAudit/.../IntPolynomialPseudoDegreeDecrease — zero-axiom gate

Per-declaration zero-axiom gate for the pseudo-division degree-decrease capstone (the tenth brick of
`invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255): the Nat/degree helpers, the far-above vanishing of a
monomial-times-polynomial product, and `polyPseudoStepDegreeLt` — the pseudo-division step strictly
decreases the degree for a non-constant divisor.

Assembles r17/r18/r19 through the corpus `natAddSubOfLe` and core Nat order lemmas plus the corpus `Int`
ring lemmas.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.natLeOfSubOneLt
#assert_no_axioms FX1Poly.ComputerAlgebra.natSubAddCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.polyTrimLengthEqDegreeSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.polyMonomialMulCoeffVanishesFarAbove
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoStepDegreeLt
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoStepDegreeLtGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasPseudoStepDegreeDecrease

end FX1PolyAudit
