import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordStaircase

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordStaircaseAudit — zero-axiom gate for the
canonical reduced-word engine: the Coxeter–Moser comb (`combInsertData`), the one-level normal form, the recursive
staircase (`recComb`), the descending run, and the `mentionsOnlyBelow` certificate, with the r9 / r11 pins and the
permutation round-trip (WP-PROP r14, #2033).

Per-declaration `#assert_no_axioms` on every def / theorem / marker, PLUS independent (non-fuel) `#print axioms` on
the engine defs, the round-trip pin, and the marker.  The project `#assert_no_axioms` macro is fuel-based; the
independent `#print axioms` closes the gate. -/

namespace FX1PolyAudit

-- C0 — the canonical-word DATA engine.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDescendingPositions
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMentionsOnlyBelow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombInsertData
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombNormalizeForm
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecComb

-- C0 — the r9 / r11 pins + the round-trip.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecComb_r9_stuck_word
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecComb_r11_left
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecComb_r11_right
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombNormalizeForm_r11_left_fixed
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecComb_braidPairUnifies
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecComb_r9_roundTrip
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBraidPairPermShared

-- The C0 marker.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_canonicalWordStaircaseEngineShipped

-- C1 — the pure `applyAdjacentSwap` identities + the append/snoc laws (private helpers covered transitively).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermOfWordAppendSplit
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermOfWordSnoc
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidApplyAdjacentSwapInvolutive
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidApplyAdjacentSwapSwapDisjoint
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidApplyAdjacentSwapBraid
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidApplyAdjacentSwapCommuteOfLe

-- C1 — the run-commutation lemmas + the permutation-carry crux.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSwapCommutesRunAbove
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSwapCommutesRunBelow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCarryPerm

-- C1 — the KEYSTONE (each step = one adjacent swap) + the state-invariant preservation.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombInsertDataRealizesSwap
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMentionsOnlyBelowSnoc
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombInsertPreservesInvariants

-- C1 — the fold + the normal-form permutation preservation.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombFoldPreservesPerm
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombNormalizeFormPreservesPerm

-- The C1 marker + the r15 residual + the star-open marker + the round ledger.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_combInsertionRealizesSwapAndPreservesPermShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_combInsertStepConvGatedOnSpellingBridge
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterCanonicalWord
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_canonicalWordStaircaseRoundFourteenLedgerShipped

-- Independent (non-fuel) axiom prints on the engine defs, the KEYSTONE + preservesPerm, the round-trip pin, and the markers.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombInsertData
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecComb
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecComb_r9_stuck_word
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecComb_r9_roundTrip
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombInsertDataRealizesSwap
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCarryPerm
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombNormalizeFormPreservesPerm
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_canonicalWordStaircaseEngineShipped
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_combInsertionRealizesSwapAndPreservesPermShipped
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_canonicalWordStaircaseRoundFourteenLedgerShipped

end FX1PolyAudit
