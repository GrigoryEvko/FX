import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutShiftedGapSplice

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutShiftedGapSplice — zero-axiom gate for the wire-changing
(shifted) forward splice (WP-AMALG-2 r6, B2)

Per-declaration zero-axiom gate for the two-sided horizontal congruence, the domain / codomain layouts, the source
/ target layout cells, the wire-changing forward splice, the two non-vacuity gap fills, the two-`s`-wall
wire-changing witness, and the honesty marker.  (The `ShiftedGapFill` structure carries no proof obligation; its
projections are covered by the consumers below.)

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.SaturatedConvOver.hcompCongr
#assert_no_axioms FX1Poly.Polygraph.Amalgam.shiftedGapDom
#assert_no_axioms FX1Poly.Polygraph.Amalgam.shiftedGapCod
#assert_no_axioms FX1Poly.Polygraph.Amalgam.shiftedGapSourceCell
#assert_no_axioms FX1Poly.Polygraph.Amalgam.shiftedGapTargetCell
#assert_no_axioms FX1Poly.Polygraph.Amalgam.multiGapShiftedSplice
#assert_no_axioms FX1Poly.Polygraph.Amalgam.shiftedAssocGapFill
#assert_no_axioms FX1Poly.Polygraph.Amalgam.shiftedLeftUnitGapFill
#assert_no_axioms FX1Poly.Polygraph.Amalgam.shiftedTwoGapSpliceWitness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasShiftedGapForwardSplice

end FX1PolyAudit
