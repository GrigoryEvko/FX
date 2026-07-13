import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcGenPastGenCellSwapSimCount

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcGenPastGenCellSwapSimCount — zero-axiom gate (MODE-COMMUTE r27)

Per-declaration zero-axiom gate for the r27 gen-past-gen CELL-granularity base case (cap x cap
combo): the whole-cell-shaped `runArcCell` swap theorem with whisker-derived positions, the
shipped marker, and the four untouched-false honesty pins.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcGenPastGenSwapSimCount_capCap
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasGenPastGenCellSwapBaseCase
#assert_no_axioms FX1Poly.Polygraph.arcGenPastGenCellSwap_disjointWhiskerSupport_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcGenPastGenCellSwap_swapRenameableProof2_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcGenPastGenCellSwap_partitionCommute_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcGenPastGenCellSwap_samePartitionFresh_stays_false

end FX1PolyAudit
