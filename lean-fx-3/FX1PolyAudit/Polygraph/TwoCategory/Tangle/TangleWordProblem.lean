import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Tangle.TangleWordProblem

/-! # FX1PolyAudit.Polygraph.TwoCategory.Tangle.TangleWordProblem — zero-axiom gate (WP-TANGLE)

Per-declaration zero-axiom gate for the tangle word-problem seed: the tangle signature (T1), the underlying-flat
combined invariant + soundness + the Reidemeister move lemmas (T2), the pure-flat / unsigned-pure-braid and signed
pure-braid-3 fragment decisions (T3), the ground fires (T5), and the honest full-tangle wall (T4).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- T1: the tangle signature
#assert_no_axioms FX1Poly.Polygraph.TngKind
#assert_no_axioms FX1Poly.Polygraph.instDecidableEqTngKind
#assert_no_axioms FX1Poly.Polygraph.TngTangleAtom
#assert_no_axioms FX1Poly.Polygraph.instDecidableEqTngTangleAtom
#assert_no_axioms FX1Poly.Polygraph.tngInputCount
#assert_no_axioms FX1Poly.Polygraph.tngOutputCount
#assert_no_axioms FX1Poly.Polygraph.tngWidthStep
#assert_no_axioms FX1Poly.Polygraph.tngWidthOf
#assert_no_axioms FX1Poly.Polygraph.tngWidthOf_append
#assert_no_axioms FX1Poly.Polygraph.tngBandAssoc
#assert_no_axioms FX1Poly.Polygraph.tngWordWellScoped
#assert_no_axioms FX1Poly.Polygraph.tngWordWellScoped_append
#assert_no_axioms FX1Poly.Polygraph.tngIdentity
#assert_no_axioms FX1Poly.Polygraph.tngCompose
#assert_no_axioms FX1Poly.Polygraph.tngCompose_width

-- T2: the combined invariant + soundness + move lemmas
#assert_no_axioms FX1Poly.Polygraph.tngForget
#assert_no_axioms FX1Poly.Polygraph.tngUnderlyingFlat
#assert_no_axioms FX1Poly.Polygraph.TngConv
#assert_no_axioms FX1Poly.Polygraph.tngConv_flatSound
#assert_no_axioms FX1Poly.Polygraph.tngConv_flatComplete
#assert_no_axioms FX1Poly.Polygraph.tngConv_iff_flatEq
#assert_no_axioms FX1Poly.Polygraph.decideTngConv
#assert_no_axioms FX1Poly.Polygraph.instDecidableTngConv
#assert_no_axioms FX1Poly.Polygraph.decideTngConvBool
#assert_no_axioms FX1Poly.Polygraph.tngConv_of_flatEq
#assert_no_axioms FX1Poly.Polygraph.tngConv_bridge
#assert_no_axioms FX1Poly.Polygraph.tngConv_signedR2_seed
#assert_no_axioms FX1Poly.Polygraph.tngConv_unsignedR2_seed
#assert_no_axioms FX1Poly.Polygraph.tngConv_r3_seed
#assert_no_axioms FX1Poly.Polygraph.tngConv_snake_seed
#assert_no_axioms FX1Poly.Polygraph.tngConv_snakeMirror_seed
#assert_no_axioms FX1Poly.Polygraph.tngConv_capSlide_seed
#assert_no_axioms FX1Poly.Polygraph.tngPositiveMark
#assert_no_axioms FX1Poly.Polygraph.tngNegativeMark
#assert_no_axioms FX1Poly.Polygraph.tngWrithePositive
#assert_no_axioms FX1Poly.Polygraph.tngWritheNegative

-- T3(a): the signed pure-braid-3 fragment decision
#assert_no_axioms FX1Poly.Polygraph.tngSignedPos
#assert_no_axioms FX1Poly.Polygraph.tngSignedNeg
#assert_no_axioms FX1Poly.Polygraph.tngSignedBraidAtoms
#assert_no_axioms FX1Poly.Polygraph.tngSignedBraidWord
#assert_no_axioms FX1Poly.Polygraph.TngBraidConv
#assert_no_axioms FX1Poly.Polygraph.decideTngBraidConv
#assert_no_axioms FX1Poly.Polygraph.instDecidableTngBraidConv
#assert_no_axioms FX1Poly.Polygraph.decideTngBraidConvBool
#assert_no_axioms FX1Poly.Polygraph.tngBraidConv_r3

-- T3(b): the pure-flat / unsigned-pure-braid fragment fires
#assert_no_axioms FX1Poly.Polygraph.tngPureFlat_snake_decided
#assert_no_axioms FX1Poly.Polygraph.tngPureBraid_doubleCrossing_decided

-- T5: the ground fires
#assert_no_axioms FX1Poly.Polygraph.tngFlat_cupCap_fire
#assert_no_axioms FX1Poly.Polygraph.tngBraid_yangBaxter_fire
#assert_no_axioms FX1Poly.Polygraph.tngFlat_snake_fire
#assert_no_axioms FX1Poly.Polygraph.tngFlat_crossing_ne_identity_fire
#assert_no_axioms FX1Poly.Polygraph.tngWrithe_fire
#assert_no_axioms FX1Poly.Polygraph.tngIdentity_fire

-- T4: the honest wall witnesses
#assert_no_axioms FX1Poly.Polygraph.tngConv_posX_negX_flatEqual
#assert_no_axioms FX1Poly.Polygraph.tngBraid_posNeg_distinct

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.tngHasTangleSignature
#assert_no_axioms FX1Poly.Polygraph.tngHasCombinedInvariantSoundness
#assert_no_axioms FX1Poly.Polygraph.tngHasPureBraidDecision
#assert_no_axioms FX1Poly.Polygraph.tngHasPureFlatDecision
#assert_no_axioms FX1Poly.Polygraph.tngHasFullTangleDecision

end FX1PolyAudit
