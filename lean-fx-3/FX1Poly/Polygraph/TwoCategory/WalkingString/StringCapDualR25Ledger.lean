import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCapHeadExtractionWordPinPrime
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCapDualR24Ledger

/-! # WalkingString/StringCapDualR25Ledger — the FC-3 r25 valley-program ledger (B4)

The honest scoreboard for the mid-zero valley's CAP arm after r25 — the descent RE-FOUNDING round.  No new
mathematics; a NAMED-node map of what shipped, what is now UNBLOCKED, and the r26 bill.

## The valley-program state

  * **(i) r17 — the CUP arm, SHIPPED** (`StringWidthZeroPureCupSort`).  Unchanged.

  * **(ii) THE CAP ARM — the descent RE-FOUNDED, the pin AUGMENTED, the wall B1/B2(r24) raised DISSOLVED.**
    r24 truth-probed the r23-planned colour discharge FALSE (`StringCapWindowColourTruthProbe`) and re-keyed the
    gap-closing exclusion off POSITION (`stringArcPairSeated_beforeCapStep_ofDistinctSeat`, colour-free), leaving
    the descent re-founding + the pin as the standing residual.  r25 (this round) discharges the re-founding:

      - **B1 `StringConsecutiveUntouchedSeat` — the FORWARD adjacency invariant substrate.**
        `stringArcPairSeated_stepCapArc_ofDisjointReads` pushes a seated pair FORWARD through any cap that misses
        it (the position-disjointness read straight off the four misses — no parity, no distinctness);
        `stringMemProcessArcSpine_belowFresh_imp` reflects a below-fresh open node from the fold's end back to its
        start — the reverse read-off the recon flagged as Risk R1, PROVED (cups mint only fresh ids, caps/boxes
        only remove).  The 3-cap maximally-shifting probe fires it end-to-end.  Zero-axiom.

      - **B2 `StringWordPairSeatedDescentOfDistinct` — the re-founded descent master.**
        `stringWordPairSeated_bubblesThroughPrefix_ofDistinct` re-founds r23's
        `stringWordPairSeated_bubblesThroughPrefix` on B2(r24)'s colour-free exclusion, DROPPING the FALSE
        `prefixSharesWindowMode` premise.  The `AllCapArity` prefix kills the cup arm (nothing splits the pair);
        each cap dispatches four-ways on its reads — MISSes push the B1 forward invariant plus
        distinctness/freshness/untouchedness to the stepped state and feed the r24 exclusion the current-state
        adjacency, and any HIT contradicts the located seat via the B1 membership monotonicity plus the
        removed-value read `stringNotMem_natListRemoveTwoAt_ofDistinctRead`.  The `WordBubblesToFront` assembly is
        byte-identical to r23.  Zero-axiom.  **This dissolves the recon's Risk R1 outright — the early-landing
        gate the r24 plan expected to defer to r26 is CLOSED.**

      - **B3 `StringCapHeadExtractionWordPinPrime` — the pin AUGMENTED + its conditional sort.**
        The shipped pin plus `AllCapArity` on BOTH spines (the r24-named conjunct-(4) cancel augmentation +
        the B2 descent's `AllCapArity secondList` cup-kill); `stringPureCapSpine_sort_ofPrime` re-wires the
        peel-first pure-cap sort to consume it (the shipped pin + conditional sort BYTE-INTACT).  Both `AllCapArity`
        witnesses are already in scope at the sort's peel site, so the augmentation costs the sort nothing.
        Zero-axiom.

  * **(iii) VERBATIM STILL OWED — the pin-prime INHABITANT (the four-conjunct assembly), now UNBLOCKED by B2.**
    The r24 ledger jammed the pin on the descent premise (the forward adjacency invariant) plus four conjunct
    seams.  r25 discharged the descent premise (B1 + B2) and augmented the pin (B3).  What remains for r26 is the
    pure-composition assembly — no longer gated on any un-proved mathematics:
      - run the located read-off (`StringArcPairCapWindow` / r19-r20) to seat the toucher's two consecutive
        untouched legs (`ArcPairUntouched` + the seed range read-off), producing the descent's `seatedEnd` and the
        `(∃ seatBefore, ArcPairSeated …)` premise;
      - feed the re-founded descent `stringWordPairSeated_bubblesThroughPrefix_ofDistinct` (B2) to bubble the
        toucher to the front (`WordBubblesToFront`);
      - close conjunct (1) via `spineTraceEquiv_of_wordBubblesToFront` + the identify seam
        `stringCapAtom_eq_of_sharedDom_sameWindow` (glue seam 1 = the window-equal read-off, R3);
      - close conjunct (2) via `spineBoundaryChained_ofWordChained` (r23, B3) + `composePath_length` (seam 2);
      - close conjunct (3) via `spineBoundaryWordChained_of_wordBubblesToFront` + `spineBoundaryWordChained_tail`
        + the identify rewrite (seam 3);
      - close conjunct (4) via the r21 cancel `stringArcCapHeadFolded_extractArc_cancel` fed the pin-prime's
        `AllCapArity tailList` / `matchedRemainder`.

## The r26 bill (named)

  * **r26 — inhabit + flip.**  Assemble the four conjuncts (above) ⟹ `StringCapHeadExtractionWordPinPrime`
    inhabited ⟹ `stringPureCapSpine_sort_ofPrime` unconditional ⟹ flip `fxString_hasUnconditionalPureCapSort`.
    Then the whole-valley wiring toward `fxString_hasAdjointTripleCompleteness` (the mid-width telescope + the
    floor-0 cup-block reconstruct, ~770 uncloned lines on top of BOTH arms) — completeness is NOT r25-reachable
    and stays `false`.  Nothing this round was a fabricated flip; no pin inhabitant was faked.

Raw Lean 4 + Init; a documentation node (one honesty marker).
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; `#assert_no_axioms` gated in the audit
twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **★ LEDGER — FC-3 r25 THE CAP-DUAL DESCENT RE-FOUNDING, the honest scoreboard (B4).**  r25 discharged the
r24-named descent premise (the forward adjacency invariant) and augmented the pin, dissolving Risk R1:

  * B1 `fxString_hasConsecutiveUntouchedSeatForward` — the FORWARD adjacency substrate: the disjoint-cap seat
    push (colour-free, no distinctness) + the below-fresh membership monotonicity (the Risk-R1 reverse read-off,
    PROVED), 3-cap probe fired.
  * B2 `fxString_hasWordPairSeatedDescentOfDistinct` — the re-founded descent master: r23's descent re-based on
    the r24 colour-free exclusion, the FALSE `prefixSharesWindowMode` premise DROPPED, cups killed by
    `AllCapArity`, hits contradicted via the B1 monotonicity + removed-value read.  Risk R1 CLOSED.
  * B3 `fxString_hasCapHeadExtractionWordPinPrime` — the pin AUGMENTED with `AllCapArity` on both spines + the
    conditional sort `stringPureCapSpine_sort_ofPrime` consuming it (shipped pin + sort byte-intact).

  THE STILL-OWED: the pin-prime INHABITANT (the four-conjunct assembly), now UNBLOCKED — the descent is shipped,
  the pin carries its `AllCapArity`; r26 is pure composition (located read-off + descent + three glue seams + r21
  cancel).  THE r26 BILL: inhabit ⟹ flip `fxString_hasUnconditionalPureCapSort` ⟹ the ~770-line whole-valley
  wiring toward completeness (`fxString_hasAdjointTripleCompleteness` stays `false`, not r25-reachable).  No flip
  fabricated; no pin inhabitant faked.  `= true`. -/
def fxString_hasCapDualR25Ledger : Bool := true

end FX1Poly.Polygraph
