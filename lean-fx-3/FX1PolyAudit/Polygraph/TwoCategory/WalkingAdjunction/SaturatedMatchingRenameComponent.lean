import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingRenameComponent

/-! # FX1PolyAudit/…/SaturatedMatchingRenameComponent — zero-axiom gate

Per-declaration zero-axiom gate for the component-level Godement renaming relation: the corrected
`MatchingRenameRelComponent` (component-level `sameComponentComm` replacing the refuted root-level
`rootComm`) and its extract-invariance `extractDiagram_of_matchingRenameRelComponent` must be free
of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.extractDiagram_of_matchingRenameRelComponent
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingRenameRelComponent

end FX1PolyAudit
