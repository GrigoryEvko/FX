import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEventCongruence

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingJoinEventCongruence — zero-axiom gate

Per-declaration zero-axiom gate for the fresh-shift equivariance of the join-event trace: the
spine plumbing (difference-list append normalization, trace concatenation, vertical-composite
split), the per-atom event equivariance, the two-position block-level trace congruence, and the
honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.spineDiff_append
#assert_no_axioms FX1Poly.Polygraph.spineJoinEvents_append
#assert_no_axioms FX1Poly.Polygraph.spineJoinEvents_vcompSplit
#assert_no_axioms FX1Poly.Polygraph.stepAtomPair_joinEvents_freshShift
#assert_no_axioms FX1Poly.Polygraph.runMatchingCell_joinEvents_freshShift
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingJoinEventFreshShiftCongruence

end FX1PolyAudit
