import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.RationalPair

/-! # FX1PolyAudit/ComputerAlgebra/Number/RationalPair — zero-axiom gate
    (NUM-Q-1)

Per-declaration zero-axiom gate for the ℚ carrier: the successor-shaped pair, the
positive denominator read-back, and the decidable cross-multiplication setoid with
its reflexivity/symmetry/transitivity laws.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.denominatorInt
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.denominatorIntIsPositive
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.DenotesSameAs
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.decideDenotesSameAs
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.denotesSameAsRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.denotesSameAsSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.denotesSameAsTrans

end FX1PolyAudit
