import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Steiner.Soundness

/-! # FX1PolyAudit/Polygraph/Omega/Steiner/Soundness — zero-axiom gate (OMEGA-2 B4 CROWN fold)

Per-declaration `#assert_no_axioms` on the CROWN soundness: the absorbing-congruence instance
`linearizeAbsorbs` (all eight strict-axiom rows discharged unconditionally), the soundness theorem
`linearizeSoundness` inhabiting `OmegaTwoLinearizeSoundnessShape` via `SaturatedConvOver.recInto`, and
the direct-form corollary.  Every declaration must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeAbsorbs
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeSoundness
#assert_no_axioms FX1Poly.Polygraph.Omega.linearize_eq_of_saturatedConv

end FX1PolyAudit
