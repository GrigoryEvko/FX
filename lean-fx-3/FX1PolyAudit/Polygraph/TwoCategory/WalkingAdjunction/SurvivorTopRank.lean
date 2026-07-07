import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SurvivorTopRank

/-! # FX1PolyAudit/…/SurvivorTopRank — zero-axiom gate

Per-declaration zero-axiom gate for brick 2 (order half) of the valley-append split (Piece II tail of the fib-3
gate): the survivor-top classification and count.  The Bool survivor-top predicate, the survivor-top count fold,
its monotonicity, and the strict order-preservation past a survivor-top.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isSurvivorTop
#assert_no_axioms FX1Poly.Polygraph.survivorTopCount
#assert_no_axioms FX1Poly.Polygraph.survivorTopRank
#assert_no_axioms FX1Poly.Polygraph.survivorTopCount_le_succ
#assert_no_axioms FX1Poly.Polygraph.survivorTopCount_le_add
#assert_no_axioms FX1Poly.Polygraph.survivorTopCount_mono
#assert_no_axioms FX1Poly.Polygraph.survivorTopRank_strictMono_atSurvivorTop
#assert_no_axioms FX1Poly.Polygraph.cond_true_one
#assert_no_axioms FX1Poly.Polygraph.cond_false_one
#assert_no_axioms FX1Poly.Polygraph.countBelow
#assert_no_axioms FX1Poly.Polygraph.survivorTopCount_eq_countBelow
#assert_no_axioms FX1Poly.Polygraph.countBelow_congr
#assert_no_axioms FX1Poly.Polygraph.countBelow_ltSelf_eq_bound
#assert_no_axioms FX1Poly.Polygraph.countBelow_ltSelf_eq_threshold
#assert_no_axioms FX1Poly.Polygraph.strictMono_decideLt_agree
#assert_no_axioms FX1Poly.Polygraph.strictMono_countBelow_image_eq_rank
#assert_no_axioms FX1Poly.Polygraph.countBelow_add_eq
#assert_no_axioms FX1Poly.Polygraph.countBelow_eq_zero_of_allFalse
#assert_no_axioms FX1Poly.Polygraph.countBelow_atStrictMonoImage_eq_rank
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSurvivorTopClassification

end FX1PolyAudit
