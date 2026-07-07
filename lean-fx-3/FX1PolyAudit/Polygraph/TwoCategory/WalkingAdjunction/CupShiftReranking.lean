import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.CupShiftReranking

/-! # FX1PolyAudit/…/CupShiftReranking — zero-axiom gate

Per-declaration zero-axiom gate for brick (1) of the valley-append split (Piece II tail of the fib-3 gate): the
cup-shift re-ranking.  The survivor read-off with `openAllUnlinked` dropped
(`partnerIndexOf_survivorUnlinked_eq_rank`), the cup-block unlinked-preservation fold, and the whole-valley
survivor partner pinned to `bottomCount + phi rankCap`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_survivorUnlinked_eq_rank
#assert_no_axioms FX1Poly.Polygraph.stepCup_preservesArcNodeUnlinked
#assert_no_axioms FX1Poly.Polygraph.processSpine_preservesArcNodeUnlinked_ofAllCupArity
#assert_no_axioms FX1Poly.Polygraph.survivorPartner_throughCupBlock
#assert_no_axioms FX1Poly.Polygraph.survivorPartner_inWholeValley
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasCupShiftReranking

end FX1PolyAudit
