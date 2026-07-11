import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutInteriorProducerStateLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutInteriorProducerStateLedger — zero-axiom gate for the r19
#2043 state ledger (WP-AMALG-2 r19, B5)

Per-declaration zero-axiom gate for the r19 bricks-shipped conjunction, the two-jam pins, the wall-shift / producer
pins, the master checklist, the close criterion + its re-derivation, and the honesty marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR19BricksShipped
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR19BricksShipped_true
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR19JamA_perGapDescentOpen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR19JamB_narrowedButWalled
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR19WallShiftStaysWalled
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR19ProducerSupersedesResidual
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR19NoMasterFlips
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_pushoutDispatch2043ClosesAfterR19
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_pushoutDispatch2043ClosesAfterR19_false
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR19CloseCriterionMatchesR18
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_canonicalReaderStateAfterR19

end FX1PolyAudit
