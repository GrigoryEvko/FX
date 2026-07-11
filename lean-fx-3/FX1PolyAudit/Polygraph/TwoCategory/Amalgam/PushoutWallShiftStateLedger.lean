import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallShiftStateLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWallShiftStateLedger — zero-axiom gate for the r18 #2043 state
ledger (WP-AMALG-2 r18, B5)

Per-declaration zero-axiom gate for the r18 bricks-shipped conjunction, the two jam pins, the wall-shift-stays-walled
pin, the master checklist, the #2043 close criterion + its `false` verdict, and the state honesty marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR18BricksShipped
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR18BricksShipped_true
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR18JamA_perGapDescentOpen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR18JamB_narrowedButWalled
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR18WallShiftStaysWalled
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR18NoMasterFlips
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_pushoutDispatch2043ClosesAfterR18
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_pushoutDispatch2043ClosesAfterR18_false
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_canonicalReaderStateAfterR18

end FX1PolyAudit
