import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialPseudoDegreeDecrease

/-! # FX1PolyAudit/.../IntPolynomialPseudoDegreeDecrease — zero-axiom gate

Per-declaration zero-axiom gate for the pseudo-division degree-decrease capstone: the Nat/degree helpers,
the far-above vanishing of a monomial-times-polynomial product, and `polyPseudoStepDegreeLt` — the step
strictly decreases the degree for a non-constant divisor.  Through `natAddSubOfLe`, core Nat order lemmas,
and the corpus `Int` ring lemmas.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.natLeOfSubOneLt
#assert_no_axioms FX1Poly.ComputerAlgebra.natSubAddCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.polyTrimLengthEqDegreeSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.polyMonomialMulCoeffVanishesFarAbove
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoStepDegreeLt
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoStepDegreeLtGrounding

end FX1PolyAudit
