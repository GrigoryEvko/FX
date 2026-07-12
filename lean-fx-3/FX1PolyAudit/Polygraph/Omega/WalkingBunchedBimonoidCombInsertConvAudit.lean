import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCombInsertConv

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidCombInsertConvAudit — zero-axiom gate for the
four-branch comb-insertion CONV step `combInsertConv` (F2) and its genuinely-new CARRY-branch atom
`carryPermConv` (WP-PROP r25).

Per-declaration `#assert_no_axioms` on the snoc CONV, the `permWord` target-boundary, the braid-with-tail
regrouping, the permutation-carry CONV atom, the four-branch comb-insertion step, the non-vacuity instances
(carry width-3, comb-insert CARRY + COMMUTE), the width-3 braid matrix pin, and the three delivery markers —
PLUS an independent (non-fuel) `#print axioms` on the same public declarations.  The project `#assert_no_axioms`
macro is fuel-based; the independent `#print axioms` closes the gate.  (The private arithmetic + list + descending
-run backbone `{PredSuccCombInsert, NatLePredCombInsert, SubTwoAddTwoCombInsert, NatAddSubCancelCombInsert,
NatEqSubOfAddEqCombInsert, NatLeOfAddLeAddRightCombInsert, NatLeOfAddLeAddLeftCombInsert, SubOneCommCombInsert,
AppendAssocCombInsert, DescendingPositionsSnocCombInsert, NatBleOfLeCombInsert, NatBltOfLtCombInsert,
DescendingPositionsMentionBelowCombInsert}` is checked transitively through the public `carryPermConv` /
`combInsertConv` that consume it.) -/

namespace FX1PolyAudit

-- A1 — the snoc CONV + the permWord target-boundary.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordSnocConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordBoundaryTarget

-- A2 — the braid-with-tail regrouping (the r24 braid atom threaded into the RIGHT-fold permWord).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBraidWithTailConv

-- A3 — the permutation-carry CONV atom (the ONE genuinely-new brick).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCarryPermConv

-- A4 — the four-branch comb-insertion CONV step (F2).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombInsertConv

-- The non-vacuity instances + the width-3 braid matrix pin.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCarryPermConvWidthThreeInstance
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCarryPermBraidMatrixShared
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombInsertConvCarryInstance
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombInsertConvCommuteInstance

-- The three delivery markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_carryPermConvShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_combInsertConvShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_combNormalizeFormFoldAndOwnerFlipStillOpen

-- Independent (non-fuel) axiom prints on the snoc CONV, the braid-with-tail, the carry atom, the headline step,
-- the instances, the matrix pin, and the markers.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordSnocConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordBoundaryTarget
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBraidWithTailConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCarryPermConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombInsertConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCarryPermConvWidthThreeInstance
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCarryPermBraidMatrixShared
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombInsertConvCarryInstance
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombInsertConvCommuteInstance
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_carryPermConvShipped
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_combInsertConvShipped
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_combNormalizeFormFoldAndOwnerFlipStillOpen

end FX1PolyAudit
