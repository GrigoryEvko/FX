import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialPseudoStepDegreeGen

/-! # FX1PolyAudit/.../IntPolynomialPseudoStepDegreeGen — zero-axiom gate

Per-declaration zero-axiom gate for the generalized pseudo-division step degree decrease: the non-generalized
step with the divisor-nonconstant hypothesis relaxed to divisor-nonempty + dividend-nonconstant, covering the
constant-divisor Euclidean tail case (`polyPseudoStepDegreeLtGen` / `polyPseudoConstantStepDegreeLt`).  Free
of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoStepDegreeLtGen
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoConstantStepDegreeLt
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoStepDegreeLtGenGrounding

end FX1PolyAudit
