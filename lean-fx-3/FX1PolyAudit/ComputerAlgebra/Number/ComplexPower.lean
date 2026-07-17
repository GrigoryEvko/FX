import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.ComplexPower

/-! # FX1PolyAudit/ComputerAlgebra/Number/ComplexPower — zero-axiom gate

Per-declaration zero-axiom gate for the ℝ/ℂ natural-power folds and the
modulus-power law `|zⁿ| ~ |z|ⁿ` (the FTA-path polynomial-growth prerequisite).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.powReal
#assert_no_axioms FX1Poly.ComputerAlgebra.powComplex
#assert_no_axioms FX1Poly.ComputerAlgebra.powRealNonNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.modulusPowDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.fxComplexReal_hasPowerAndModulusPow

end FX1PolyAudit
