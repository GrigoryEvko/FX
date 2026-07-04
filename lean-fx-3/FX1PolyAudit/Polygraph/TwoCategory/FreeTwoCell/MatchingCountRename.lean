import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCountRename

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingCountRename — zero-axiom gate

Per-declaration zero-axiom gate for the count rename invariance: the correspondence-transport
induction and the injective empty-base invariance (the private join-correspondence step is
covered transitively).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.countJoinEventLoops_ofRenameCorrespondence
#assert_no_axioms FX1Poly.Polygraph.countJoinEventLoops_ofRename
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasCountRenameInvariance

end FX1PolyAudit
