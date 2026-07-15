import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFlatWhiskerEngines

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFlatWhiskerEngines — zero-axiom gate (WP-AMALG)

Per-declaration zero-axiom gate for the four per-letter whisker engines and the fueled per-letter peels.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.emptyGapSlot
#assert_no_axioms FX1Poly.Polygraph.Amalgam.interleaveRuns_frontRun
#assert_no_axioms FX1Poly.Polygraph.Amalgam.readingConsSlot
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftSEngine
#assert_no_axioms FX1Poly.Polygraph.Amalgam.tFuseHeadSlot
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftTCore
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftTEngine
#assert_no_axioms FX1Poly.Polygraph.Amalgam.tFuseTailSlot
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightTCore
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightTEngine
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightSCore
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightSEngine
#assert_no_axioms FX1Poly.Polygraph.Amalgam.readingWhiskerLeftFueled
#assert_no_axioms FX1Poly.Polygraph.Amalgam.readingWhiskerRightFueled
#assert_no_axioms FX1Poly.Polygraph.Amalgam.readingWhiskerLeft
#assert_no_axioms FX1Poly.Polygraph.Amalgam.readingWhiskerRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasFlatWhiskerEngines

end FX1PolyAudit
