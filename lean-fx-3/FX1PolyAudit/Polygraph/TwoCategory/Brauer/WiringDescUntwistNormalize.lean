import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescUntwistNormalize

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescUntwistNormalize — zero-axiom gate (WP-BRAUER terminal T1)

Per-declaration zero-axiom gate for the untwist normalization assembly: the leftmost-redex scanner
(`findUntwistRedex`) with its propext-free scan-soundness reconstructions, the structural-on-fuel fold
(`untwistNormalize` / `untwistNF`), the HYPOTHESIS-FREE convertibility (`untwistNormalize_conv` / `untwistNF_conv`),
the output redex-freeness (`findUntwistRedex_untwistNormalize_none` / `findUntwistRedex_untwistNF_none`), the
non-vacuity witnesses, and the honesty marker.  The private length-drop helpers
(`lengthReductKeepFirst` / `lengthReductKeepSecond`) are covered transitively through the freeness theorems.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the redex kind + the scanner
#assert_no_axioms FX1Poly.Polygraph.UntwistKind
#assert_no_axioms FX1Poly.Polygraph.findUntwistRedex

-- scan soundness (the propext-free reconstruction, via the dependent-if)
#assert_no_axioms FX1Poly.Polygraph.findUntwistRedex_cup_sound
#assert_no_axioms FX1Poly.Polygraph.findUntwistRedex_cap_sound

-- the fold + its seeded entry
#assert_no_axioms FX1Poly.Polygraph.untwistNormalize
#assert_no_axioms FX1Poly.Polygraph.untwistNF

-- hypothesis-free convertibility
#assert_no_axioms FX1Poly.Polygraph.untwistNormalize_conv
#assert_no_axioms FX1Poly.Polygraph.untwistNF_conv

-- output redex-freeness (fuel induction on the length invariant; covers the private length helpers)
#assert_no_axioms FX1Poly.Polygraph.findUntwistRedex_untwistNormalize_none
#assert_no_axioms FX1Poly.Polygraph.findUntwistRedex_untwistNF_none

-- non-vacuity on real words
#assert_no_axioms FX1Poly.Polygraph.untwistNF_cup_single
#assert_no_axioms FX1Poly.Polygraph.untwistNF_cap_single
#assert_no_axioms FX1Poly.Polygraph.untwistNF_cup_cascade
#assert_no_axioms FX1Poly.Polygraph.untwistNF_fixed_points
#assert_no_axioms FX1Poly.Polygraph.findUntwistRedex_untwistNF_cascade_none

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasUntwistNormalization

end FX1PolyAudit
