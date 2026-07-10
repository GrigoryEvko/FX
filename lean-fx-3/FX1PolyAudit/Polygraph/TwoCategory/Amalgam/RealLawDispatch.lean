import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.RealLawDispatch

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.RealLawDispatch — zero-axiom gate for the REAL-law pushout dispatch
SOUNDNESS half (WP-AMALG-2 r2)

Per-declaration zero-axiom gate: the mono-component law soundness (B1, the reconstructed monad law preserves the
payload-blind arity fold), the law-redex locality lemma (B1, the REAL coprojected law row preserves
`arityFoldEqRel`), the real-law arity-fold congruence (B2, the completeness decomposition), the composed decision
(B3, the real-law separation `isFalse`, unconditional), the isTrue soundness whisker-lifts (B2, a real monad law
fired inside an `s`-interleaved word), and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- B1: the mono-component law soundness + the law-redex locality lemma
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadLawReconstructed_arityEq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairRealPushoutRel
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityFoldEqRel_of_realPushoutRow

-- B2: the completeness decomposition (the real-law arity-fold congruence)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityFoldRealPushoutCongruence

-- B3: the composed decision — the real-law separation, unconditional
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairRealPushoutNonConv

-- B2: the isTrue soundness whisker-lifts (a real monad law fired in an interleaved word)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.sInterleavedAssocLawConv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.sInterleavedLeftUnitLawConv

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasRealLawPushoutSoundness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_realLawCompletenessStaysWalled

end FX1PolyAudit
