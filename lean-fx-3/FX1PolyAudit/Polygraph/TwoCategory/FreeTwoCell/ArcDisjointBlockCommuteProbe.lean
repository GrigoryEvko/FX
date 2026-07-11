import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcDisjointBlockCommuteProbe

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcDisjointBlockCommuteProbe — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the disjoint-block commutation + negative control: the disjoint positive
control (`arcDisjointBlockPartitionCommutes`), the non-disjoint re-adjudication
(`arcNonDisjointBlockPartitionCommutes` — the partition view commutes even for sharing blocks), and the root-flip
that shows join order is load-bearing only at the root level (`arcNonDisjointRootLevelDiffers` /
`arcNonDisjointRoots`), plus the honesty marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in
`AuditAll` (the orchestrator does the unified registration). -/

namespace FX1PolyAudit

-- the disjoint positive control + the non-disjoint re-adjudication (partition-level)
#assert_no_axioms FX1Poly.Polygraph.arcDisjointBlockPartitionCommutes
#assert_no_axioms FX1Poly.Polygraph.arcNonDisjointBlockPartitionCommutes

-- the root-flip (join order load-bearing only at the root level)
#assert_no_axioms FX1Poly.Polygraph.arcNonDisjointRootLevelDiffers
#assert_no_axioms FX1Poly.Polygraph.arcNonDisjointRoots

-- the honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcDisjointBlockCommuteProbe

end FX1PolyAudit
