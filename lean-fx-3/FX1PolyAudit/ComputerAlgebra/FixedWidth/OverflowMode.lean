import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.FixedWidth.OverflowMode

/-! # FX1PolyAudit/ComputerAlgebra/FixedWidth/OverflowMode — zero-axiom gate

Per-declaration zero-axiom gate for the dim-16 overflow-mode preorder: the four
modes, the `Bool` order program, and the reflexive / bottom / transitive laws.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.OverflowMode
#assert_no_axioms FX1Poly.ComputerAlgebra.overflowLe
#assert_no_axioms FX1Poly.ComputerAlgebra.overflowLeRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.exactIsBottom
#assert_no_axioms FX1Poly.ComputerAlgebra.overflowLeTrans

end FX1PolyAudit
