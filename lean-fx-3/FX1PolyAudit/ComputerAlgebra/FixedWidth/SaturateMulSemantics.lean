import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.FixedWidth.SaturateMulSemantics

/-! # FX1PolyAudit/ComputerAlgebra/FixedWidth/SaturateMulSemantics — zero-axiom gate

Per-declaration zero-axiom gate for the saturating-multiplication semantics: the
in-range exactness, the overflow clamp, and the upper bound.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.saturateMulInRange
#assert_no_axioms FX1Poly.ComputerAlgebra.saturateMulClamps
#assert_no_axioms FX1Poly.ComputerAlgebra.saturateMulUpperBounded

end FX1PolyAudit
