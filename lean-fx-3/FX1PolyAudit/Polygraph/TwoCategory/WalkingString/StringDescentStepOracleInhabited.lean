import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDescentStepOracleInhabited

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringDescentStepOracleInhabited — zero-axiom gate (FC-3 r8, B3)

Per-declaration zero-axiom gate for PIECE I DONE: the hypothesis-free per-step descent oracle and the reduction of the
monolithic residual to Piece II alone.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringDescentStepOracle
#assert_no_axioms FX1Poly.Polygraph.stringMatchingReductsShareSpineTrace_of_valleyTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.fxString_hasStringCellDescentStepOracle

end FX1PolyAudit
