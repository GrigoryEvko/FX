import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFoldRename

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingFoldRename — zero-axiom gate

Per-declaration zero-axiom gate for the fold-rename equivariance engine: the forward path
map, the preimage-tracking walk, and the Bool-level equivariance (the private map/membership
plumbing is covered transitively).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.renamedJoinEventPath_ofCanonicalPath
#assert_no_axioms FX1Poly.Polygraph.renamedFoldConnected_ofCanonicalFold
#assert_no_axioms FX1Poly.Polygraph.canonicalFoldConnected_ofRenamedPath
#assert_no_axioms FX1Poly.Polygraph.canonicalFoldConnected_ofRenamedFold
#assert_no_axioms FX1Poly.Polygraph.componentView_applyJoinEvents_ofRename
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasFoldRenameEquivariance

end FX1PolyAudit
