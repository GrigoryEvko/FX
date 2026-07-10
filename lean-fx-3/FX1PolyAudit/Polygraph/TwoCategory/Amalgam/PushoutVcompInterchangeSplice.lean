import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutVcompInterchangeSplice

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutVcompInterchangeSplice — zero-axiom gate for the crux
vcomp-case splice of the whole-cell factorization induction (WP-AMALG-2 r7, B2)

Per-declaration zero-axiom gate for the free interchange package, THE CRUX `vcompGapInterchangeSplice`, the three
non-crux reduction lemmas (`id` / `whiskerLeft` / `whiskerRight`), the interleaved-firing non-vacuity witness at
the real pushout signature, and the three honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.SaturatedConvOver.vcompHcompSplit
#assert_no_axioms FX1Poly.Polygraph.Amalgam.vcompGapInterchangeSplice
#assert_no_axioms FX1Poly.Polygraph.Amalgam.hcompId_conv_idComposite
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeft_conv_hcompIdLeading
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRight_conv_hcompIdTrailing
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutRightCell
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutTrivialWall
#assert_no_axioms FX1Poly.Polygraph.Amalgam.interleavedAssocGapPair
#assert_no_axioms FX1Poly.Polygraph.Amalgam.interleavedLeftUnitGapPair
#assert_no_axioms FX1Poly.Polygraph.Amalgam.vcompTwoGapInterchangeWitness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasVcompGapInterchangeSplice
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_vcompRegroupCochainBounds
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_topFactorizationInductionStaysWalled

end FX1PolyAudit
