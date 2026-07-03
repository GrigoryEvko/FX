import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRenameSupport

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingRenameSupport — zero-axiom gate

Per-declaration zero-axiom gate for the sigma-witness rename-support kit: the base
correspondence (a fresh rename is invisible to the component view), the trace value bounds
(per-atom, spine, cell), the pointwise event-map surgery (congr-on-members,
eq-self-on-members, compose), and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.componentView_ofFreshRename
#assert_no_axioms FX1Poly.Polygraph.stepAtomJoinEvents_valuesBounded
#assert_no_axioms FX1Poly.Polygraph.spineJoinEvents_valuesBounded
#assert_no_axioms FX1Poly.Polygraph.runMatchingCell_joinEvents_valuesBounded
#assert_no_axioms FX1Poly.Polygraph.listMapPairCongr_onMembers
#assert_no_axioms FX1Poly.Polygraph.listMapPairEqSelf_onMembers
#assert_no_axioms FX1Poly.Polygraph.listMapPairCompose
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingRenameSupportKit

end FX1PolyAudit
