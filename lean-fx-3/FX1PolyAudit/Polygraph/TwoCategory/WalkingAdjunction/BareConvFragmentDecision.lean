import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.BareConvFragmentDecision

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.BareConvFragmentDecision — zero-axiom gate

Per-declaration zero-axiom gate for the bare-`TwoCellConv` FRAGMENT DECISION: the injective additive
whisker-pattern code `RawTwoCellExpr.wordCode` and its step / conv invariance (including the interchange critical
pair, an eight-atom `Nat` reassociation after distributing the `2 *`); the structural parity / halving helpers
(`isEvenBit`, `halve`, cancellation, even-≠-odd); the frame builder `frameWord` with `frameWord_generatorCount`,
the injective code `phi` (`frameWord_wordCode`, `phi_injective`); the fragment decision `frameWord_twoCellConv_iff`
and its total decider `decideFrameBareConv` (with the hand-rolled `listBoolDecEq` and the `frameBareConvBool`
witness); the r1 / r2 fixture tie-ins and their refutations; and the INFINITE tower (`falseWord`, `bubbleLeft`,
`bubbleRight`, `frameWord_bubble`, `bubbleLeft_ne_bubbleRight`, `frameWord_tower_separates`); plus the two honesty
markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.wordCode
#assert_no_axioms FX1Poly.Polygraph.TwoCellStep.wordCode_eq
#assert_no_axioms FX1Poly.Polygraph.TwoCellConv.wordCode_eq
#assert_no_axioms FX1Poly.Polygraph.isEvenBit
#assert_no_axioms FX1Poly.Polygraph.isEvenBit_two_mul
#assert_no_axioms FX1Poly.Polygraph.isEvenBit_two_mul_add_one
#assert_no_axioms FX1Poly.Polygraph.two_mul_ne_two_mul_add_one
#assert_no_axioms FX1Poly.Polygraph.halve
#assert_no_axioms FX1Poly.Polygraph.halve_two_mul
#assert_no_axioms FX1Poly.Polygraph.two_mul_cancel
#assert_no_axioms FX1Poly.Polygraph.frameWord
#assert_no_axioms FX1Poly.Polygraph.frameWord_generatorCount
#assert_no_axioms FX1Poly.Polygraph.phi
#assert_no_axioms FX1Poly.Polygraph.frameWord_wordCode
#assert_no_axioms FX1Poly.Polygraph.phi_cons_ne_zero
#assert_no_axioms FX1Poly.Polygraph.phi_injective
#assert_no_axioms FX1Poly.Polygraph.listBoolDecEq
#assert_no_axioms FX1Poly.Polygraph.frameWord_twoCellConv_iff
#assert_no_axioms FX1Poly.Polygraph.decideFrameBareConv
#assert_no_axioms FX1Poly.Polygraph.frameBareConvBool
#assert_no_axioms FX1Poly.Polygraph.frameWord_selfConv
#assert_no_axioms FX1Poly.Polygraph.whiskerExchangeLHS_eq_frameWord
#assert_no_axioms FX1Poly.Polygraph.whiskerExchangeRHS_eq_frameWord
#assert_no_axioms FX1Poly.Polygraph.cellLRRL_eq_frameWord
#assert_no_axioms FX1Poly.Polygraph.cellRLLR_eq_frameWord
#assert_no_axioms FX1Poly.Polygraph.frameWord_LR_not_twoCellConv_RL
#assert_no_axioms FX1Poly.Polygraph.frameWord_LRRL_not_twoCellConv_RLLR
#assert_no_axioms FX1Poly.Polygraph.falseWord
#assert_no_axioms FX1Poly.Polygraph.bubbleLeft
#assert_no_axioms FX1Poly.Polygraph.bubbleRight
#assert_no_axioms FX1Poly.Polygraph.frameWord_bubble
#assert_no_axioms FX1Poly.Polygraph.bubbleLeft_ne_bubbleRight
#assert_no_axioms FX1Poly.Polygraph.frameWord_tower_separates
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasBareConvDecidedOnSingleGeneratorFragment
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasBareConvMomentTowerInfiniteViaFragment

end FX1PolyAudit
