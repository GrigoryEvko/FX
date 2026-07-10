import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentSaturatedRightWhisker

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingIdempotent.IdempotentSaturatedRightWhisker — zero-axiom gate

Per-declaration zero-axiom gate for the GENERIC-NATIVE grow-half right-whisker + `whiskerRightCanonGen` (POLY-TAB r4).
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.castChainCollapseConvGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightPullMonadTConvGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.vcompCastMergeConvGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idempotentRightSectionCancelGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.growColumnFoldGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.growTowerRightWhiskerGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightCanonOneGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightCanonGen

end FX1PolyAudit
