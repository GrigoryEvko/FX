import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDistinctSeatCapExclusion

/-! # WalkingString/StringUnconditionalCapSortLedger — the unconditional pure-cap sort marker, held FALSE
(FC-3 r24, B3)

The r24 target beyond the shipped conditional sort (`stringPureCapSpine_sort`, which takes the residual
`StringCapHeadExtractionWordPin` as a hypothesis) is an UNCONDITIONAL pure-cap sort — the wrapper obtained
once that residual is genuinely inhabited.  This file records that state HONESTLY: the residual is NOT
inhabited this round, so the unconditional sort does NOT flip.

  * B1 (`StringCapWindowColourTruthProbe`) truth-probed the r23-planned discharge (`AllCapArity` ⟹
    `prefixSharesWindowMode`) and it came back FALSE — the colour route to the pin is dead.
  * B2 (`StringDistinctSeatCapExclusion`) shipped the genuine unblocking keystone — the COLOUR-FREE cap-step
    gap-closing exclusion `stringArcPairSeated_beforeCapStep_ofDistinctSeat` — refuting the recon's "blocked"
    verdict at the exclusion level.
  * What remains for the unconditional sort (the named residual): thread the toucher's consecutive untouched
    legs' pre-cap adjacency FORWARD through the whole pure-cap prefix, re-found
    `stringWordPairSeated_bubblesThroughPrefix` on the B2 exclusion in place of `prefixSharesWindowMode`,
    inhabit `StringCapHeadExtractionWordPin` by assembling its four conjuncts, and only THEN flip.

So this round flips NO unconditional-sort marker and re-touches NO shipped marker
(`fxString_hasMidZeroValleyCapSort` stays `true` byte-intact — its verbatim demand is the cap-sort machinery
assembled MODULO the discharge, which does not require pin inhabitation; the completeness flag
`fxString_hasAdjointTripleCompleteness` stays `false`).  It ships one FRESH-VALLEY example firing the B2
colour-free exclusion on the OTHER descent branch, and the honest `false` marker.

Raw Lean 4 + Init; the fresh-valley probe is `by decide` data fed to the B2 keystone.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Fresh-valley example — the colour-free exclusion fires on the PAST-window branch -/

/-- A concrete six-wire seed valley `[0, 1, 2, 3, 4, 5]` (fresh counter at `6`), a wider anchor than the B2
four-wire probe. -/
def stringFreshValleyProbeState : ArcWireState :=
  ArcWireState.mk (List.range 6) [] 6 0 [] []

/-- ★ **The colour-free exclusion fires on a fresh six-wire valley (PAST-window branch).**  A pair `(3, 4)`
seated adjacent at position `3` in the pre-cap seed, and at position `1` after a cap consumes the window
`(0, 1)` BELOW it (`stepCapArc … 0`), descends to having been seated at position `3` before the cap — the
PAST-window outcome (the other `beforeCapStep` branch from the B2 probe's below-window outcome), run
end-to-end through `stringArcPairSeated_beforeCapStep_ofDistinctSeat` with NO parity input.  A fresh,
larger, machine-checked witness that the colour-free descent step scales past the minimal probe. -/
theorem stringFreshValleyProbe_fires :
    (ArcPairSeated 3 4 1 stringFreshValleyProbeState ∧ 1 + 2 ≤ 0)
      ∨ (ArcPairSeated 3 4 (1 + 2) stringFreshValleyProbeState ∧ 0 ≤ 1) := by
  have seatedBefore : ArcPairSeated 3 4 3 stringFreshValleyProbeState :=
    ⟨by decide, by decide, by decide⟩
  have seatedAfter : ArcPairSeated 3 4 1 (stepCapArc stringFreshValleyProbeState 0) :=
    ⟨by decide, by decide, by decide⟩
  exact stringArcPairSeated_beforeCapStep_ofDistinctSeat stringFreshValleyProbeState 0
    (arcInitialState_wireListDistinct 6) seatedBefore (by decide) seatedAfter

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the UNCONDITIONAL pure-cap sort is ACHIEVED (flipped FC-3 r26).**  The r24 target beyond
the conditional sort is now reached: r25 shipped the AllCapArity-augmented pin-prime and the sort
`stringPureCapSpine_sort_ofPrime` consuming it, and r26 INHABITED the pin-prime as the closed axiom-free term
`stringCapHeadExtractionWordPinInhabited` (`StringCapHeadExtractionWordPinInhabited`) — LOCATE
(`stringArcPairCapWindow_ofCapHeadExtractEq`) + SEAT/DESCEND (the re-founded distinctness descent
`stringWordPairSeated_bubblesThroughPrefix_ofDistinct`) + IDENTIFY (the DOM word pin
`stringCapAtom_eq_of_sharedDom_sameWindow`) + REALIZE/CANCEL (the WORD-bubble consumers + the r21
`stringArcCapHeadFolded_extractArc_cancel` fed the pin-prime's `AllCapArity`), the located certificate's
swapped-read branch refuted by order-preservation of the pure-cap split open-wires.  Feeding that inhabitant to
`stringPureCapSpine_sort_ofPrime` yields the hypothesis-free `stringPureCapSpine_sort_unconditional`.  This
marker flips to `true`.  What this does NOT flip: `fxString_hasAdjointTripleCompleteness`
(`StringMatchingCompleteness`) stays `false` — the mid-zero valley wiring (the (ii) sub-producer
`StringMidZeroValleyTraceEquiv` + the mid-width telescope / floor-0 cup-block reconstruct) is separate, on top of
this cap sort.  `= true`. -/
def fxString_hasUnconditionalPureCapSort : Bool := true

end FX1Poly.Polygraph
