import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingValleyDescent

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringMatchingValleyDescent — zero-axiom gate

Per-declaration zero-axiom gate for the r4 valley-descent driver ported to the three-generator seed: the per-step /
whole-descent carriers, the fuel-structural `StringSaturatedTwoCellConv`-valued driver (accumulation + termination),
its normal-form read-offs, the two sub-producers (the per-step oracle `Type` and the cell-level Piece-II `Prop`),
the honest reduction of the monolithic `StringMatchingReductsShareSpineTrace` into those two sub-producers, and the
two markers (the ported-driver marker and the length-rigidity-failure wall record).
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.StringCellDescentResult
#assert_no_axioms FX1Poly.Polygraph.StringCellValleyResult
#assert_no_axioms FX1Poly.Polygraph.StringCellDescentStepOracle
#assert_no_axioms FX1Poly.Polygraph.stringValleyDescentDriverCell
#assert_no_axioms FX1Poly.Polygraph.stringValleyNFCell
#assert_no_axioms FX1Poly.Polygraph.stringCellDescentConv
#assert_no_axioms FX1Poly.Polygraph.stringValleyNFCell_isValley
#assert_no_axioms FX1Poly.Polygraph.StringCellValleyTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.stringMatchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.fxString_hasStringValleyDescentDriver
#assert_no_axioms FX1Poly.Polygraph.fxString_hasStringLengthRigidityFailure

end FX1PolyAudit
