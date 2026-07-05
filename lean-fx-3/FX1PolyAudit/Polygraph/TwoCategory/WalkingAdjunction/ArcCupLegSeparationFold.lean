import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLegSeparationFold

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupLegSeparationFold — zero-axiom gate

Per-declaration zero-axiom gate for the leg-separation payoff (peel campaign H): the
paired-fold invariant keeping the cup's legs fresh-separated along every chained tail, and
its cup-head seed corollary deriving the legsSeparate hypothesis — the legs-connected
("cup-cancel") world is empty on the reconstruction fragment.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcLegsStaySeparate_processArcSpine
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_legsSeparate

end FX1PolyAudit
