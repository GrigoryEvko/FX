import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapCapSwapObstruction

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapCapSwapObstruction — zero-axiom gate

Per-declaration zero-axiom gate for the CAP x CAP renaming obstruction: the non-degeneracy
certificate, the two universal renaming refutations (`ArcStepSimCount` / `ArcRenameRel` fail for
EVERY `sigma` at the overlapping-component fixture), and the surviving order-insensitive content
(`SameArcPartition` + equal extracts).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.capCapObstruction_meetsSwapSideConditions
#assert_no_axioms FX1Poly.Polygraph.not_arcStepSimCount_capCapOverlap
#assert_no_axioms FX1Poly.Polygraph.not_arcRenameRel_capCapOverlap
#assert_no_axioms FX1Poly.Polygraph.capCapObstruction_sameArcPartition
#assert_no_axioms FX1Poly.Polygraph.capCapObstruction_extract_eq

end FX1PolyAudit
