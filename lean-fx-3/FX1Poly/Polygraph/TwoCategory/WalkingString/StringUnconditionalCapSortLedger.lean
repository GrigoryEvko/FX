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

/-- **OPEN (honest) — the UNCONDITIONAL pure-cap sort is NOT achieved; NO flip (FC-3 r24, B3).**  The
shipped sort `stringPureCapSpine_sort` is conditional on the residual `StringCapHeadExtractionWordPin`.
Making it unconditional requires inhabiting that residual, which this round does NOT do: B1 refuted the
r23-planned colour discharge (`AllCapArity` ⟹ `prefixSharesWindowMode` is FALSE), and B2 shipped the genuine
colour-free replacement (`stringArcPairSeated_beforeCapStep_ofDistinctSeat`) but the FULL inhabitation still
needs the descent-master re-founding (forward adjacency thread of the toucher's consecutive untouched legs +
re-keying `stringWordPairSeated_bubblesThroughPrefix` on the B2 exclusion) plus the four-conjunct pin
assembly.  `stringFreshValleyProbe_fires` demonstrates the B2 exclusion on a fresh six-wire valley (the
past-window branch) — the colour-free descent step the re-founding iterates.  This marker stays `false`; no
shipped marker is re-touched (`fxString_hasMidZeroValleyCapSort` = `true` byte-intact, completeness = `false`).
`= false`. -/
def fxString_hasUnconditionalPureCapSort : Bool := false

end FX1Poly.Polygraph
