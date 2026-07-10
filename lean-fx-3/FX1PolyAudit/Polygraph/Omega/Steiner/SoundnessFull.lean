import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Steiner.SoundnessFull

/-! # FX1PolyAudit/Polygraph/Omega/Steiner/SoundnessFull — zero-axiom gate (OMEGA-2.5 r1, B4)

Per-declaration `#assert_no_axioms` on the chain-granularity soundness fold: the per-row poles agreement,
the absorbing-congruence instance, the crown soundness, the strictly-stronger sound refuter and full
semi-decider, the whisker-fix promoted to non-convertibility, and the positive-direction non-vacuity.
Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- The soundness fold
#assert_no_axioms FX1Poly.Polygraph.Omega.polesOf_ofRelation_eq
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFull_ofRelation
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFullAbsorbs
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFullSoundness
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFull_eq_of_saturatedConv

-- The strictly-stronger sound refuter + semi-decider
#assert_no_axioms FX1Poly.Polygraph.Omega.not_conv_of_linearizeFull_ne
#assert_no_axioms FX1Poly.Polygraph.Omega.decideFullConvSound

-- Non-vacuity both ways
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerFix_not_conv
#assert_no_axioms FX1Poly.Polygraph.Omega.demo_conv_chain_tables_equal

end FX1PolyAudit
