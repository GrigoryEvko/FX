import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRelativeJoinEvents

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingRelativeJoinEvents — zero-axiom gate

Per-declaration zero-axiom gate for the relative-run trace correspondence (MODE3-D brick
D3): the per-atom join-event rename, the disciplined fold, and the honesty marker (the
private map-append kit is covered transitively).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stepAtomJoinEvents_ofRelativeWireSim
#assert_no_axioms FX1Poly.Polygraph.spineJoinEvents_ofRelativeWireSim
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingRelativeJoinEventCorrespondence

end FX1PolyAudit
