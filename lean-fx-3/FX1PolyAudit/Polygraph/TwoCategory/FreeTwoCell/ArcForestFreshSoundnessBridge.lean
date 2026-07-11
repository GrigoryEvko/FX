import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcForestFreshSoundnessBridge

/-! # FX1PolyAudit … ArcForestFreshSoundnessBridge — zero-axiom gate (mode-3 floor, forest-fresh soundness bridge)

Per-declaration zero-axiom gate for the forest-freshness-gated arc-soundness bridge: the forest-gated
Godement-step invariance (`godementInvariantForestFresh_of_samePartitionFreshForest`), the forest+non-degeneracy
threaded trace closure (`arcTraceInvariantForestFresh`), the assembled soundness at a non-empty boundary
(`arcStructureOf_sound_of_forestFresh`), and the honesty marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  The project
`#assert_no_axioms` macro is fuel-based, so each declaration is ALSO checked by the exhaustive core `#print axioms`.
NOT registered in `AuditAll` here (the orchestrator does the unified registration in one breath). -/

namespace FX1PolyAudit

-- the freshness+forest-gated Godement-step invariant
#assert_no_axioms FX1Poly.Polygraph.godementInvariantForestFresh_of_samePartitionFreshForest
#print axioms FX1Poly.Polygraph.godementInvariantForestFresh_of_samePartitionFreshForest

-- the forest+non-degeneracy threaded trace closure
#assert_no_axioms FX1Poly.Polygraph.arcTraceInvariantForestFresh
#print axioms FX1Poly.Polygraph.arcTraceInvariantForestFresh

-- the assembled soundness at a non-empty boundary
#assert_no_axioms FX1Poly.Polygraph.arcStructureOf_sound_of_forestFresh
#print axioms FX1Poly.Polygraph.arcStructureOf_sound_of_forestFresh

-- the honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcForestFreshSoundnessBridge
#print axioms FX1Poly.Polygraph.fxMode_hasArcForestFreshSoundnessBridge

end FX1PolyAudit
