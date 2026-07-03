import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingInterfaceTransfer

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingInterfaceTransfer — zero-axiom gate

Per-declaration zero-axiom gate for the interface transfer engine: the empty-base plumbing,
the endpoint-pinning lemma, the pivot/pending walk, and the fold-level transfer.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.nodesEqual_ofEmptyBaseConnected
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_applyJoinEvents_ofEmptyBase
#assert_no_axioms FX1Poly.Polygraph.firstEndpointBelow_ofNontrivialBaseConnected
#assert_no_axioms FX1Poly.Polygraph.transferAlongJoinEventPath
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_applyJoinEvents_transferAcrossInterface
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasInterfaceChainTransfer

end FX1PolyAudit
