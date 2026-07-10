import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Steiner.WallHarvestWithId

/-! # FX1PolyAudit/Polygraph/Omega/Steiner/WallHarvestWithId — zero-axiom gate (OMEGA-3 r2, B3).

Per-declaration `#assert_no_axioms` on the wall harvest: the free strict congruence over the sibling,
conservativity on atom words (both directions), whiskered completeness on the chain table (fixed whisker),
and both whiskered decider verdicts. -/

namespace FX1PolyAudit

-- WallHarvestWithId.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.freeStrictCongruenceWithId
#assert_no_axioms FX1Poly.Polygraph.Omega.saturatedConvOverWithId_conservative_atomWord
#assert_no_axioms FX1Poly.Polygraph.Omega.atomWord_conv_iff_withId
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskeredAtomWord_conv_of_linearizeFull_eq
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskeredAtomWord_conv_iff_linearizeFull_eq
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskered_word_conv_withId
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskered_word_not_conv_withId

end FX1PolyAudit
