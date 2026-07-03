import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTwoCellDecidable

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTwoCellDecidable — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for decidable 2-cell equality instantiated at the walking-adjunction seed: the
generator decision procedures, the specialized free-2-cell `DecidableEq` and interchange-free convertibility
decision, and the `rfl`-checked end-to-end smoke theorems.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.adjunctionModeDecEq
#assert_no_axioms FX1Poly.Polygraph.adjunctionModalityDecEq
#assert_no_axioms FX1Poly.Polygraph.adjunctionTwoCellDecEq
#assert_no_axioms FX1Poly.Polygraph.adjunctionRawTwoCellDecidableEq
#assert_no_axioms FX1Poly.Polygraph.adjunctionDecidableInterchangeFreeConv
#assert_no_axioms FX1Poly.Polygraph.adjunctionUnitThenId_ne_unit_decidably
#assert_no_axioms FX1Poly.Polygraph.adjunctionUnit_eq_unit_decidably
#assert_no_axioms FX1Poly.Polygraph.adjunctionUnitThenId_interchangeFreeConv_unit_decidably

end FX1PolyAudit
