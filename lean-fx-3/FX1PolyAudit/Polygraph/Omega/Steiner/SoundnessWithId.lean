import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Steiner.SoundnessWithId

/-! # FX1PolyAudit/Polygraph/Omega/Steiner/SoundnessWithId — zero-axiom gate (OMEGA-3 r2, B2).

Per-declaration `#assert_no_axioms` on the soundness cascade re-closed over the idCongr sibling: the
single-vector and chain absorbing instances (with the three new fields — the degenerate-pole extension
included), the two soundness folds, the two sound refuters, and the non-vacuity witnesses. -/

namespace FX1PolyAudit

-- SoundnessWithId.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeAbsorbsWithId
#assert_no_axioms FX1Poly.Polygraph.Omega.linearize_eq_of_saturatedConvWithId
#assert_no_axioms FX1Poly.Polygraph.Omega.not_conv_of_linearize_ne_withId
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFullAbsorbsWithId
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFull_eq_of_saturatedConvWithId
#assert_no_axioms FX1Poly.Polygraph.Omega.not_conv_of_linearizeFull_ne_withId
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerFix_not_conv_withId
#assert_no_axioms FX1Poly.Polygraph.Omega.demo_idCongr_chain_tables_equal

end FX1PolyAudit
