import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupDisjointCapWindowPin

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupDisjointCapWindowPin — zero-axiom gate

Per-declaration zero-axiom gate for the R1 head-cup window read-off lifted past one WINDOW-DISJOINT cap: for
`[cupHead, capTail]` with the cap a gap above the cup legs, the single cup event's `internalCupCounts` census
still reads `1` at the left leg and `0` below, so `internalCupCounts` PINS the head cup's window — the first
non-empty-tail step of the census inversion (FM Prop 4.2.4 window-disjoint peel).  The public assertions
transitively cover every private census/reduce/read lemma.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isSameComponent_unionFindJoin_offProbe
#assert_no_axioms FX1Poly.Polygraph.singleCupHeadWindowPinned_pastDisjointCap
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupDisjointCapWindowPin

end FX1PolyAudit
