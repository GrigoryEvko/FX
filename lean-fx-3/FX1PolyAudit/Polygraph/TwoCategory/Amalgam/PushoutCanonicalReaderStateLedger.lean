import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutCanonicalReaderStateLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutCanonicalReaderStateLedger — zero-axiom gate for the r17 #2043
state ledger (WP-AMALG-2 r17, B5)

Per-declaration zero-axiom gate for the r17 bricks-shipped conjunction, the two jam pins, the master checklist, the
strict #2043 close criterion + its `false` proof, and the state honesty marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR17BricksShipped
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR17BricksShipped_true
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR17JamA_perGapDescentOpen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR17JamB_factorizationNarrowedButWalled
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR17NoMasterFlips
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_pushoutDispatch2043ClosesAfterR17
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_pushoutDispatch2043ClosesAfterR17_false
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_canonicalReaderStateAfterR17

end FX1PolyAudit
