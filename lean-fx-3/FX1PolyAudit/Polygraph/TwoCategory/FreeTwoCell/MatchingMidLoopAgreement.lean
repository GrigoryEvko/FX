import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingMidLoopAgreement

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingMidLoopAgreement — zero-axiom gate

Per-declaration zero-axiom gate for the LOOP-leg headline (the private left cancellation is
covered transitively).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.countJoinEventLoops_overMidLinks_agrees_ofViewSim
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMidLinksLoopAgreement

end FX1PolyAudit
