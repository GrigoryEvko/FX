import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupReconstruct

/-! # FX1PolyAudit/…/ValleyCupReconstruct — zero-axiom gate

Per-declaration zero-axiom gate for the cup-side `DiagramType.ext` (`cupRestrict_reconstructs`, Piece II tail):
the full three-field reconstruction assembled from the two shipped cup partner cases plus the single case-3
partner hypothesis (top-top cup-arc partner offset).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cupRestrict_reconstructs
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasCupReconstructAssembledToCase3

end FX1PolyAudit
