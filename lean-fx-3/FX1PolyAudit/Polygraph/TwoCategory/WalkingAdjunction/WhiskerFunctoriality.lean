import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.WhiskerFunctoriality

/-! # FX1PolyAudit.Tier0.Mode.FreeTwoCellWhiskerFunctoriality — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the COMPLETED free-strict-2-category convertibility `TwoCellConvFull`
(existing `TwoCellConv` + the four whisker-functoriality laws + congruences), its boundary-cast helpers
(`castBoundary` and the spine-invariance lemmas they ride on), and the headline spine SOUNDNESS
`TwoCellConvFull ⟹ trace-equivalent spines` — the NO-direction the keystone decision consumes.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.castBoundary
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.castBoundary_spineDiff
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.castBoundary_spine
#assert_no_axioms FX1Poly.Tier0.spineTraceEquiv_of_eq
#assert_no_axioms FX1Poly.Tier0.twoCellConv_spineTraceEquivDiff
#assert_no_axioms FX1Poly.Tier0.twoCellConvFull_spineTraceEquivDiff
#assert_no_axioms FX1Poly.Tier0.twoCellConvFull_spineTraceEquiv
#assert_no_axioms FX1Poly.Tier0.whiskerLeftUnit_convFull
#assert_no_axioms FX1Poly.Tier0.whiskerRightUnit_convFull
#assert_no_axioms FX1Poly.Tier0.adjunctionUnitThenId_convFull_unit
#assert_no_axioms FX1Poly.Tier0.adjunctionUnitWhiskerLeftEmpty_spine_eq_unit
#assert_no_axioms FX1Poly.Tier0.fxMode_hasWhiskerFunctorialityConvertibility

end FX1PolyAudit
