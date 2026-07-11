import FX1Poly.Polygraph.TwoCategory.WalkingString.StringUnconditionalCapSortLedger

/-! # WalkingString/StringCapDualR24Ledger — the FC-3 r24 valley-program ledger (B4)

The honest scoreboard for the mid-zero valley's CAP arm after r24.  No new mathematics; a NAMED-node map of
what shipped, what is verbatim owed, and the r25-r26 wiring bill.

## The valley-program state

The mid-zero valley discharge (`StringMatchingCompleteness` ⟶ `fxString_hasAdjointTripleCompleteness`) has two
arms, one per turnback species:

  * **(i) r17 — the CUP arm, SHIPPED.**  `StringWidthZeroPureCupSort` inhabited
    `StringWidthZeroPureCupDeterminacyShared` by porting the walking-adjunction MATCHING-carrier width-0 cup sort
    onto the word machinery (peel-last / shared-COD / bottom-pinned-at-0).

  * **(ii) NOW — the CAP arm, ASSEMBLED MODULO ONE DISCHARGE, its wall RE-KEYED off colour.**  r18 shipped the
    cap-dual sort machinery `stringPureCapSpine_sort` conditional on the residual
    `StringCapHeadExtractionWordPin`.  r19/r20 shipped the located-window transport
    (`stringArcPairCapWindow_ofCapHeadExtractEq`).  r21 shipped the cancellation engine
    (`stringArcCapHeadFolded_extractArc_cancel`) and the loops leg (`stringArcCapHeadFolded_loops_zero`, via the
    parity-free `ArcOpenEndsDistinct`).  r22/r23 shipped the parity substrate + the WORD descent master
    `stringWordPairSeated_bubblesThroughPrefix`, taking the threaded `prefixSharesWindowMode` premise.  r24 (this
    round):
      - B1 `StringCapWindowColourTruthProbe` — the r23-planned discharge `AllCapArity ⟹ prefixSharesWindowMode`
        truth-probed on a concrete located-shaped spine and settled **FALSE** (`counitUpper@window0 = base`,
        `counitLower@window1 = tip`; route (a) refuted; route (b) dead — the r20 certificate is colour-free).
      - B2 `StringDistinctSeatCapExclusion` — the COLOUR-FREE gap-closing exclusion
        `stringArcPairSeated_beforeCapStep_ofDistinctSeat` (from `WireListDistinct` + pre-cap adjacency, via
        `natListGetAt_inj_ofWireListDistinct`).  This REFUTES the recon's "blocked" verdict at the exclusion
        level: the wall was the colour framing, not the mathematics.
      - B3 `StringUnconditionalCapSortLedger` — no unconditional-sort flip (pin uninhabited);
        `fxString_hasUnconditionalPureCapSort` held `false`; no shipped marker re-touched.

  * **(iii) VERBATIM STILL OWED — the `StringCapHeadExtractionWordPin` inhabitant, jams named per conjunct.**
    The pin returns `matchedRemainder` with FOUR conjuncts; each jam is a NAMED seam:
      - **Conjunct (1)** `SpineTraceEquiv secondList (headAtom :: matchedRemainder)`.  Suppliers SHIPPED:
        `spineTraceEquiv_of_wordBubblesToFront` (the descent's bubble → trace equiv) + the identify pin
        `stringCapAtom_eq_of_sharedDom_sameWindow`.  JAM = **the window-equal glue** (a NEW lemma:
        `movedToucher.leftContext.length = windowPosition`, read off the seat's `ArcPairSeated` at the fresh seed
        port — the recon's risk R3).
      - **Conjunct (2)** `SpineBoundaryChained headAtom.codBoundaryLength matchedRemainder`.  Supplier SHIPPED:
        B3-of-r23 `spineBoundaryChained_ofWordChained`.  JAM = **the codEq bridge** (`composePath_length` twice
        to rewrite the running cod word's length to `headAtom.codBoundaryLength`) — minor.
      - **Conjunct (3)** `SpineBoundaryWordChained (head cod word) matchedRemainder`.  Supplier SHIPPED:
        `spineBoundaryWordChained_of_wordBubblesToFront` + `spineBoundaryWordChained_tail`.  JAM = **the identify
        rewrite** (`movedToucher = headAtom`) — minor.
      - **Conjunct (4)** `arcStructureOfSpineList codBoundary tailList = arcStructureOfSpineList codBoundary
        matchedRemainder`.  Engine SHIPPED: r21 `stringArcCapHeadFolded_extractArc_cancel` +
        `extractArc_eq_of_stringAtomicTraceEquiv` (arc structure is trace-invariant).  JAM = **the AllCapArity pin
        augmentation** — the cancel needs `AllCapArity tailList` / `AllCapArity matchedRemainder`, which the
        SHIPPED pin does NOT carry; the pin must become pin-PRIME (add `AllCapArity firstList` / `secondList`) in a
        NEW additive file, re-wiring the sort's one `headExtract` call site (the shipped Prop + conditional sort
        stay byte-intact; the augmentation is a NEW `StringCapHeadExtractionWordPinPrime`).
      - **The descent premise** (the wall B1/B2 addressed).  JAM = **the forward adjacency invariant**: the
        toucher's two legs are CONSECUTIVE untouched seed ports (`StringArcPairCapWindow bottomCount
        windowPosition (windowPosition + 1)` + `ArcPairUntouched`), and a pure-cap prefix never inserts between
        them (only cups do — banned), so they stay adjacent through the whole prefix.  A NEW forward-preservation
        lemma feeding B2's `seatedBeforeInState` at each step, then re-founding
        `stringWordPairSeated_bubblesThroughPrefix` on `stringArcPairSeated_beforeCapStep_ofDistinctSeat` in place
        of `prefixSharesWindowMode`.

## The r25-r26 wiring bill (named)

  * **r25 — the descent re-founding + the conditional pin.**  (a) `stringConsecutiveUntouchedSeat` forward
    invariant (adjacency-preservation of the toucher's consecutive untouched legs through the pure-cap prefix);
    (b) `stringWordPairSeated_bubblesThroughPrefix_ofDistinct` — the re-founded master threading distinctness +
    (a) into B2's exclusion, dropping `prefixSharesWindowMode`; (c) the pin-prime
    `StringCapHeadExtractionWordPinPrime` + the four-conjunct assembly (the window-equal glue, codEq bridge,
    identify rewrite, the r21 cancel fed the AllCapArity augmentation) ⟹ a CONDITIONAL inhabitant reduced to (a).

  * **r26 — inhabit + flip.**  Discharge (a) fully ⟹ `StringCapHeadExtractionWordPinPrime` inhabited ⟹ the
    UNCONDITIONAL pure-cap sort ⟹ flip `fxString_hasUnconditionalPureCapSort`.  Then the whole-valley wiring
    toward `fxString_hasAdjointTripleCompleteness`: the mid-width telescope (`stringSurvivorTopTotal_eq_midWidth`
    analog) + the floor-0 cup-block reconstruct (`midZeroCupBlockReconstruct` analog), ~770 uncloned lines, on top
    of BOTH arms — completeness is NOT r24-reachable and stays `false`.

Raw Lean 4 + Init; a documentation node (one honesty marker).
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; `#assert_no_axioms` gated in the audit
twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **★ LEDGER — FC-3 r24 THE CAP-DUAL PIN INHABITATION, the honest scoreboard (B4).**  r24 truth-probed the
r23-planned pin discharge and CORRECTED the recon's verdict:

  * B1 `fxString_hasCapWindowColourTruthProbe` — the located-prefix colour read is **FALSE**: an `AllCapArity`
    prefix carries caps of OPPOSITE window colour, so `prefixSharesWindowMode` is not derivable (route (a) dead);
    the r20 certificate is colour-free (route (b) dead).
  * B2 `fxString_hasDistinctSeatCapExclusion` — the gap-closing exclusion is **COLOUR-FREE and machine-checked**
    (`stringArcPairSeated_beforeCapStep_ofDistinctSeat`, from `WireListDistinct` + pre-cap adjacency); the wall
    the recon called "blocked" is genuinely refutable — the block was the colour framing.
  * B3 `fxString_hasUnconditionalPureCapSort = false` — no sort flip (pin uninhabited); no shipped marker
    re-touched.

  THE JAMS, each a NAMED conjunct/glue seam: conjunct (1) = the window-equal glue (R3);
  conjunct (2) = the codEq bridge; conjunct (3) = the identify rewrite; conjunct (4) = the AllCapArity pin
  augmentation feeding the r21 cancel; the descent premise = the forward adjacency invariant of the toucher's
  consecutive untouched legs.  THE WIRING BILL: r25 = the descent re-founding on B2 + the conditional pin-prime;
  r26 = inhabit + flip `fxString_hasUnconditionalPureCapSort` + the ~770-line whole-valley wiring toward
  completeness (`fxString_hasAdjointTripleCompleteness` stays `false`, not r24-reachable).  Nothing this round was
  a fabricated flip; the pin was not faked.  `= true`. -/
def fxString_hasCapDualR24Ledger : Bool := true

end FX1Poly.Polygraph
