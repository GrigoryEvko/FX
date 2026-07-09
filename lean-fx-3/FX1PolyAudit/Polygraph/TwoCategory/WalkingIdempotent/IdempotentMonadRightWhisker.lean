import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadRightWhisker

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadRightWhisker — zero-axiom gate

Per-declaration zero-axiom gate for the walking-idempotent-monad GROW-half right-whisker + general-width
`whiskerRightCanon`: the CONV-level cast helpers, the column collapse, the grow-half right-whisker (the genuine
idempotence-using dual of `gadgetSplitRight`), and the single-`t` / general-width canonicalisation.  Must be free
of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, and any well-founded recursion (all
inductions STRUCTURAL). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.whiskerRight_whiskerEq
#assert_no_axioms FX1Poly.Polygraph.castChainCollapseConv
#assert_no_axioms FX1Poly.Polygraph.whiskerRightPullMonadTConv
#assert_no_axioms FX1Poly.Polygraph.vcompCastMergeConv
#assert_no_axioms FX1Poly.Polygraph.monadTPower_succ_add_right
#assert_no_axioms FX1Poly.Polygraph.idempotentRightSectionCancel
#assert_no_axioms FX1Poly.Polygraph.growColumnFold
#assert_no_axioms FX1Poly.Polygraph.growTowerRightWhisker
#assert_no_axioms FX1Poly.Polygraph.whiskerRightCanonOne
#assert_no_axioms FX1Poly.Polygraph.whiskerRightCanon
#assert_no_axioms FX1Poly.Polygraph.growTowerRightWhisker_two_smoke
#assert_no_axioms FX1Poly.Polygraph.whiskerRightCanon_width_two_smoke
#assert_no_axioms FX1Poly.Polygraph.fxIdempotentMonad_hasWhiskerRightCanonClosed

end FX1PolyAudit
