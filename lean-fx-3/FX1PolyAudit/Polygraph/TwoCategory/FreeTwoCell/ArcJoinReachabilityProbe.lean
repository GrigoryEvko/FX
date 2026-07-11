import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcJoinReachabilityProbe

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcJoinReachabilityProbe — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the reachability-characterization truth-probe: the concrete three-join fold
(`arcReachabilityTwoBlocks` / `arcReachabilityThreeBlocks`), its structural forest witness
(`arcReachabilityTwoBlocks_isForest`), the shipped one-step characterization fired on the concrete forest
(`arcReachabilityCharacterizationConcrete`), the raw reachability readings
(`arcReachabilityThreeEdge` / `arcReachabilityBridgeCloses`), and the honesty marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in
`AuditAll` (the orchestrator does the unified registration). -/

namespace FX1PolyAudit

-- the concrete three-join fold + its structural forest witness
#assert_no_axioms FX1Poly.Polygraph.arcReachabilityTwoBlocks
#assert_no_axioms FX1Poly.Polygraph.arcReachabilityThreeBlocks
#assert_no_axioms FX1Poly.Polygraph.arcReachabilityTwoBlocks_isForest

-- the characterization fired concretely + the raw reachability readings
#assert_no_axioms FX1Poly.Polygraph.arcReachabilityCharacterizationConcrete
#assert_no_axioms FX1Poly.Polygraph.arcReachabilityThreeEdge
#assert_no_axioms FX1Poly.Polygraph.arcReachabilityBridgeCloses

-- the honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcJoinReachabilityProbe

end FX1PolyAudit
