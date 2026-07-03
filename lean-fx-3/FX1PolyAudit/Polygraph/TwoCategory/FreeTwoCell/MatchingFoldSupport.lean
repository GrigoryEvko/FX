import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFoldSupport

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingFoldSupport — zero-axiom gate

Per-declaration zero-axiom gate for the fold support closure and untouched-probe rigidity
(the private parent/root chase lemmas are covered transitively).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.unionFindRootOf_eq_self_or_parentValue
#assert_no_axioms FX1Poly.Polygraph.nodeSetHoldsAtRoot
#assert_no_axioms FX1Poly.Polygraph.unionFindJoin_preservesNodeClosure
#assert_no_axioms FX1Poly.Polygraph.applyJoinEvents_preservesNodeClosure
#assert_no_axioms FX1Poly.Polygraph.unionFindRootOf_eq_self_ofUntouched
#assert_no_axioms FX1Poly.Polygraph.nodesEqual_ofConnectedToUntouched
#assert_no_axioms FX1Poly.Polygraph.nodesEqual_ofFoldConnectedToUntouched
#assert_no_axioms FX1Poly.Polygraph.nodesEqual_ofUntouchedFoldConnected
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasFoldSupportRigidity

end FX1PolyAudit
