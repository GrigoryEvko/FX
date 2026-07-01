import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTwoCellDecidable

/-! # FX1PolyAudit.Tier0.Mode.AdjunctionTwoCellDecidable — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for decidable 2-cell equality instantiated at the walking-adjunction seed: the
generator decision procedures, the specialized free-2-cell `DecidableEq` and interchange-free convertibility
decision, and the `rfl`-checked end-to-end smoke theorems.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.adjunctionModeDecEq
#assert_no_axioms FX1Poly.Tier0.adjunctionModalityDecEq
#assert_no_axioms FX1Poly.Tier0.adjunctionTwoCellDecEq
#assert_no_axioms FX1Poly.Tier0.adjunctionRawTwoCellDecidableEq
#assert_no_axioms FX1Poly.Tier0.adjunctionDecidableInterchangeFreeConv
#assert_no_axioms FX1Poly.Tier0.adjunctionUnitThenId_ne_unit_decidably
#assert_no_axioms FX1Poly.Tier0.adjunctionUnit_eq_unit_decidably
#assert_no_axioms FX1Poly.Tier0.adjunctionUnitThenId_interchangeFreeConv_unit_decidably

end FX1PolyAudit
