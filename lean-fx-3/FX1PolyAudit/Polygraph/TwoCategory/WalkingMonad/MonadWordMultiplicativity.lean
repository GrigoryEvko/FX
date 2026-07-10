import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWordMultiplicativity

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadWordMultiplicativity — zero-axiom gate (LEFT-whisker word multiplicativity)

Per-declaration zero-axiom gate for the LEFT-whisker word multiplicativity toward the two whisker `normalizeCell`
cases: `t^k ◁ (canonical word) ≈ (canonical word of the ones-prefixed counts)`, plus its supporting `t`-power
ordinal-sum / ones-prefix path lemmas and the leading-`1`-gadget peel, and the two honesty markers.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.wordFromCounts_consOne_conv
#assert_no_axioms FX1Poly.Polygraph.monadTPower_length_consReplicate_one
#assert_no_axioms FX1Poly.Polygraph.wordMul_whiskerLeft
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasWordMulWhiskerLeft
-- The RIGHT-whisker APPEND skeleton (consAppend + its length / domain-path / boundary identities).
#assert_no_axioms FX1Poly.Polygraph.consAppend
#assert_no_axioms FX1Poly.Polygraph.consAppend_length
#assert_no_axioms FX1Poly.Polygraph.countsDomainPath_consAppend
#assert_no_axioms FX1Poly.Polygraph.countsDomainPath_consAppend_ones
#assert_no_axioms FX1Poly.Polygraph.monadTPower_length_consAppend_ones
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasWordMulWhiskerRightAndVcomp

end FX1PolyAudit
