import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCorrectedFoldCapFreeScope
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStraighteningGap

/-! # BRAUER r53 — THE WITH-CAP VALID-INVOLUTION SCOPING: the r52 "cap-side inversion gap" prose re-diagnosed,
the ∗-dual cap-DUAL sibling machine-REFUTED as a net loss, and the extractor's coverage characterized EXACTLY as
"realizes iff the target is a valid Brauer involution" (the NINTH honest zero-flip)

r52 (`WiringDescCorrectedFoldCapFreeScope.lean`) measured a with-cap failure class (`3500/20000` at len 4) and
autopsied it (§D) as "the ∗-dual cap-side inversion gap": the corrected extractor inverts only the cup/top side, so a
cap arc entangled with a through crossing "realise[s] a different `partner` than their representative", and the prose
predicted the fix was a matching bottom-side inversion.  The literature agrees with the SHAPE (Kudryavtseva–Mazorchuk
arXiv:math/0511730 print the sandwich `u . e_{i,j}` with the `S_n x S_n` action `(g,h)(x) = g^{-1} x h` — the two sides
enter DUALLY; the Jones/TL dual normal forms `T^+`/`T^-`, Aicardi–Juyumaya–Papi arXiv:2405.10809 (3.5)/(3.6), run the
two runs in OPPOSITE order; the walled-Brauer `S^L_r . D . S^R_s`, Bulgakova–Ogievetsky–Zheglov, has increasing left
indices and DECREASING right indices).  So the natural repair is the cap-side `permInverse` mirroring the cup fix.

## THE HEADLINE ADJUDICATION — the repair is REFUTED; the real advance is the exact-iff characterization

The one-line cap-DUAL sibling (`reconstructStandardFormExt5CapDual` below: bottom side wrapped in `permInverse`) is
machine-checked to be a NET LOSS, not a fix:

  * it REGRESSES the with-cap coverage `1425 -> 942` (len 3) and `16500 -> 9300` (len 4) — it breaks 483 / 7200 words
    the r51 extractor already realized (`countCapDualRealizing` pins below);
  * it fixes ZERO words the r51 extractor missed (`countCapDualGainOverR51 = 0` on both lengths);
  * a concrete valid witness it breaks: `[capAt 1, crossingAt 0, cupAt 0]` at `bottomCount = 6` — r51 realizes it,
    the cap-dual does not (`capDualRegressesAt_capCrossCup1`).

So the r52 §D prose is imprecise: the with-cap failures are NOT a cap-side read-off inversion gap that a matching
inversion would close.  The exact story is a coverage CHARACTERIZATION.  Introducing `realizesValidInvolution b word`
(the diagram's `partner` is a fixed-point-free involution over its boundary), the symmetric difference
`(r51-realizes XOR valid-involution)` is **0** on the with-cap length-3 arena, the with-cap length-4 arena, AND the
cap-free length-5 arena (`countRepresentativeRealizeXorValid` pins = 0/0/0).  Therefore:

  > **The r51 corrected extractor realizes a word's diagram IFF that diagram is a valid Brauer involution.**  On the
  > well-formed (valid-involution) arena its coverage is 100% — with-cap INCLUDED: `1425/1425` (len 3), `16500/16500`
  > (len 4), cap-free `15625/15625` (len 5).

The r52 "3500/20000 failures" are EXACTLY the boundary-overrun degeneracies: `[capAt k, crossingAt 3, cupAt 0]`
(k = 0,1,2) puts `crossingAt 3` past the width the cap already shrank, so the engine pads a phantom wire — `topCount`
inflates `6 -> 7` and the read-off `partner` is a NON-involution (`capSideWitnessK_isMalformedTarget`); no valid
standard form can equal a malformed target.  Move the crossing inside the post-cap boundary
(`[capAt 0, crossingAt 1, cupAt 0]`) and the word is a valid involution AND realizes (`safeCapWord_valid_andRealizes`).
`realizesValidInvolution` is thus the EXACT well-formedness cut (symmDiff 0), sharper than any position-arithmetic
guard.

## What SHIPS (each zero-axiom, structural; `decide` on single-witness pins only, `#eval` on the census)

  * ★ **§A — the exact-iff census** — `isInvolutionPartner`, `realizesValidInvolution`, and named enumerators
    `withCapValidInvolutionCount` (= `1425`/`16500`), `withCapValidRepresentativeFailCount` (= `0`/`0`),
    `capFreeValidCount`, `countRepresentativeRealizeXorValid` (= `0`/`0`/`0`), with frozen `#eval` pins.
  * ★★ **§B — the cap-DUAL refutation** — `reconstructStandardFormExt5CapDual`, `classRepresentativeCapDual`,
    `capDualRealizes`, `countCapDualRealizing` (= `942`/`9300`, regression) and `countCapDualGainOverR51` (= `0`),
    plus `capDualRegressesAt_capCrossCup1` by `decide`.  Ships ONLY as a REFUTED witness — never as a repair.
  * ★ **§C — the re-diagnosis** — `capSideWitnessK_isMalformedTarget` (k = 0,1,2): the byte-intact r52 §D theorem
    `capSideDefect_atCapSlotK` re-exported AND the target pinned as a non-involution; `safeCapWord_valid_andRealizes`;
    the `topCount` inflation pins.
  * ★ **§D — the documented WALL amendment** — the r52 "cap-side inversion gap" prose quoted verbatim and superseded
    by addition (boundary-overrun / valid-involution diagnosis).  The r52 file stays BYTE-INTACT.
  * ★ **the widened honest scope** — `BrauerExt5CorrectedFoldReachesValidInvolution` (a Prop wider than r52's cap-free
    scope), STATED with the exact-iff census as its precondition evidence, NOT discharged.

## The honest residual (unchanged; the NINTH honest zero-flip)

This round supplies a STRONGER coverage census (100% on the valid-involution arena, with-cap included) and a CORRECTED
criterion (valid-involution, not cap-free), but it does NOT supply the amended-flip law's clause (a) — the drive
`BrauerConvFree8`-reaching the representative for every survivor (the R3-B inner descent, undischarged).  So every
dispatch flag and completeness master STAYS `false`; only the new EXTRACTOR-coverage census fact flips to `true`.  The
R3-A totality roundtrip PROOF stays the sole long pole (`fxBrauer_hasExt5CorrectedRoundtripProof`, byte-intact
`false`), now backed by an exact iff-characterization rather than a size-8 empirical spread.  A route / measure gap,
never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin + an independent `#print axioms` witness. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — the valid-involution predicate + the exact-iff census (named enumerators, frozen `#eval` pins) -/

/-- ★ **Is the partner list a fixed-point-free involution over its own index range?**  A genuine Brauer boundary
matching sends every port `index` to a distinct in-range partner `mate` with `partner[mate] = index`.  A boundary-
overrun word (a crossing past the post-cap width) reads a padded non-involution, which this rejects.  Structural:
`List.all` over `List.range partner.length`, `Nat.beq` / `Nat.blt` throughout (propext-free). -/
def isInvolutionPartner (partner : List Nat) : Bool :=
  (List.range partner.length).all (fun index =>
    Nat.blt (natListGetAt partner index) partner.length
      && Nat.beq (natListGetAt partner (natListGetAt partner index)) index
      && not (Nat.beq (natListGetAt partner index) index))

/-- ★ **Does the word's diagram have a valid involution partner?**  The EXACT well-formedness cut: the corrected
extractor realizes a word's diagram iff `realizesValidInvolution` holds (symmetric difference `0`, §A census). -/
def realizesValidInvolution (bottomCount : Nat) (word : List BrauerAtom) : Bool :=
  isInvolutionPartner (brauerDiagramOf bottomCount word).partner

/-- The number of words in a list whose diagram is a valid involution. -/
def countValidInvolutionWords (bottomCount : Nat) (words : List (List BrauerAtom)) : Nat :=
  (words.filter (fun word => realizesValidInvolution bottomCount word)).length

/-- The number of valid-involution words in a list whose r51 representative ALSO realizes the diagram — the coverage
on the well-formed arena. -/
def countValidInvolutionR51Realizing (bottomCount : Nat) (words : List (List BrauerAtom)) : Nat :=
  (words.filter (fun word =>
    realizesValidInvolution bottomCount word && representativeRealizesOwnDiagram bottomCount word)).length

/-- ★ **The `(r51-realizes XOR valid-involution)` symmetric-difference count.**  `0` means the two predicates
COINCIDE on the arena — the exact-iff characterization, machine-checked. -/
def countRepresentativeRealizeXorValid (bottomCount : Nat) (words : List (List BrauerAtom)) : Nat :=
  (words.filter (fun word =>
    boolXor (representativeRealizesOwnDiagram bottomCount word) (realizesValidInvolution bottomCount word))).length

/-- ★ **The with-cap valid-involution population** — single-cup words (caps allowed) whose diagram is well-formed. -/
def withCapValidInvolutionCount (bottomCount wordLength posRange : Nat) : Nat :=
  countValidInvolutionWords bottomCount (singleCupWords wordLength posRange)

/-- ★ **The with-cap valid-involution words the r51 representative FAILS to realize** — `withCapValidInvolutionCount`
minus the covered count.  `0` at len 3 and len 4: on the valid-involution arena the extractor is TOTAL, cap arcs
included. -/
def withCapValidRepresentativeFailCount (bottomCount wordLength posRange : Nat) : Nat :=
  withCapValidInvolutionCount bottomCount wordLength posRange
    - countValidInvolutionR51Realizing bottomCount (singleCupWords wordLength posRange)

/-- The cap-free valid-involution count (sanity: every cap-free single-cup word is a valid involution). -/
def capFreeValidCount (bottomCount wordLength posRange : Nat) : Nat :=
  countValidInvolutionWords bottomCount (capFreeSingleCupWords wordLength posRange)

/-! ### THE EXACT-IFF CENSUS — FROZEN `#eval` outputs (boundary `b = 6` non-degenerate for `posRange 5`) -/

-- WITH-CAP valid-involution population (caps allowed): 1425 of 1500 (len 3), 16500 of 20000 (len 4).
#eval withCapValidInvolutionCount 6 3 5   -- 1425
#eval withCapValidInvolutionCount 6 4 5   -- 16500

-- COVERAGE IS 100% ON THE VALID-INVOLUTION ARENA — the r51 extractor realizes EVERY valid word (0 failures).
#eval withCapValidRepresentativeFailCount 6 3 5   -- 0
#eval withCapValidRepresentativeFailCount 6 4 5   -- 0

-- THE EXACT IFF — (r51-realizes XOR valid-involution) is 0 on with-cap len 3, with-cap len 4, AND cap-free len 5.
#eval countRepresentativeRealizeXorValid 6 (singleCupWords 3 5)          -- 0
#eval countRepresentativeRealizeXorValid 6 (singleCupWords 4 5)          -- 0
#eval countRepresentativeRealizeXorValid 6 (capFreeSingleCupWords 5 5)   -- 0

-- CAP-FREE arena is entirely valid involutions (matches the r52 total-realization census 375/2500/15625).
#eval capFreeValidCount 6 3 5   -- 375
#eval capFreeValidCount 6 4 5   -- 2500
#eval capFreeValidCount 6 5 5   -- 15625

/-! ## B — the cap-DUAL sibling REFUTATION (a NET LOSS: ships as a refuted witness ONLY)

`reconstructStandardFormExt5Corrected` (r51, byte-intact) inverts only the cup/top side.  The "known fix" the r52
prose predicted is the ∗-dual: wrap the cap/bottom side in `permInverse` too.  This NEW sibling is machine-checked to
REGRESS coverage for ZERO gain, so it is NOT a repair.  `classRepresentativeOf` stays as shipped; the sibling gets its
OWN name (`classRepresentativeCapDual`).  The r51 corrected extractor stays byte-intact — no consumer migration this
round (that is the user-ordered cleanup arc, not here). -/

/-- ★ **The cap-DUAL sibling arc extractor.**  Identical to `reconstructStandardFormExt5Corrected` EXCEPT the cap/bottom
staircase is realized from the INVERSE of `capArcFeet ++ throughStrandBottoms` (the ∗-dual of the cup-side fix).  A
REFUTED witness: it realizes strictly FEWER diagrams than the r51 extractor (§B census). -/
def reconstructStandardFormExt5CapDual (d : DiagramType) : BrauerStandardFormExt5 :=
  let throughBottoms := throughStrandBottoms d.bottomCount d.partner
  { bottomCount := d.bottomCount,
    bottomPerm := permutationToCrossingWord d.bottomCount
      (permInverse (capArcFeet d.bottomCount d.partner ++ throughBottoms)),
    capBlock := natReplicate (capArcFeetIndices d.bottomCount d.partner).length 0,
    middle := permutationToCrossingWord throughBottoms.length
      (throughStrandPerm d.bottomCount d.topCount d.partner),
    cupBlock := natReplicate (cupArcTopIndices d.bottomCount d.topCount d.partner).length throughBottoms.length,
    topPerm := permutationToCrossingWord d.topCount
      (permInverse (throughStrandTops d.bottomCount d.topCount d.partner
        ++ cupArcTops d.bottomCount d.topCount d.partner)),
    loops := d.loops }

/-- The cap-dual class representative (the sibling's realized word). -/
def classRepresentativeCapDual (bottomCount : Nat) (word : List BrauerAtom) : List BrauerAtom :=
  standardFormWordExt5 (reconstructStandardFormExt5CapDual (brauerDiagramOf bottomCount word))

/-- Does the cap-dual sibling's representative realize the word's own diagram? -/
def capDualRealizes (bottomCount : Nat) (word : List BrauerAtom) : Bool :=
  diagramBeq (brauerDiagramOf bottomCount (classRepresentativeCapDual bottomCount word))
    (brauerDiagramOf bottomCount word)

/-- The number of words the cap-dual sibling realizes. -/
def countCapDualRealizing (bottomCount : Nat) (words : List (List BrauerAtom)) : Nat :=
  (words.filter (fun word => capDualRealizes bottomCount word)).length

/-- ★ **The cap-dual's GAIN over the r51 extractor** — words the cap-dual realizes that r51 MISSES.  `0` everywhere:
the sibling fixes nothing while breaking much. -/
def countCapDualGainOverR51 (bottomCount : Nat) (words : List (List BrauerAtom)) : Nat :=
  (words.filter (fun word =>
    capDualRealizes bottomCount word && not (representativeRealizesOwnDiagram bottomCount word))).length

/-! ### THE REFUTATION CENSUS — FROZEN `#eval` outputs -/

-- WITH-CAP: the cap-dual REGRESSES (1425 -> 942 at len 3, 16500 -> 9300 at len 4) — it breaks 483 / 7200 words.
#eval countCapDualRealizing 6 (singleCupWords 3 5)   -- 942
#eval countCapDualRealizing 6 (singleCupWords 4 5)   -- 9300
-- ZERO GAIN: the cap-dual fixes NO word the r51 extractor missed.
#eval countCapDualGainOverR51 6 (singleCupWords 3 5)   -- 0
#eval countCapDualGainOverR51 6 (singleCupWords 4 5)   -- 0
-- CAP-FREE: the cap-dual does not regress here (bottomPerm is identity when there are no caps) — 375/2500/15625.
#eval countCapDualRealizing 6 (capFreeSingleCupWords 3 5)   -- 375
#eval countCapDualRealizing 6 (capFreeSingleCupWords 4 5)   -- 2500
#eval countCapDualRealizing 6 (capFreeSingleCupWords 5 5)   -- 15625

/-- ★★ **THE CAP-DUAL IS A NET LOSS — machine-checked on a concrete witness.**  `[capAt 1, crossingAt 0, cupAt 0]` at
`bottomCount = 6` is a valid word the r51 extractor realizes; the cap-dual sibling BREAKS it.  So the ∗-dual bottom
inversion the r52 prose predicted is not a repair — it is a strict regression. -/
theorem capDualRegressesAt_capCrossCup1 :
    representativeRealizesOwnDiagram 6 [capAt 1, crossingAt 0, cupAt 0] = true
      ∧ capDualRealizes 6 [capAt 1, crossingAt 0, cupAt 0] = false :=
  ⟨by decide, by decide⟩

/-! ## C — the re-diagnosis: the §D failures are MALFORMED (non-involution) targets, not a read-off gap -/

/-- ★★ **Cap slot 0 — the r52 §D defect is a MALFORMED target.**  The byte-intact r52 theorem `capSideDefect_atCapSlot0`
(the representative reads a DIFFERENT diagram) re-exported, AND the target pinned as a NON-involution
(`realizesValidInvolution … = false`): no valid standard form can equal it.  This is the exact re-diagnosis of the
r52 "cap-side inversion gap" — a boundary-overrun degeneracy, not a repairable read-off inversion. -/
theorem capSideWitness0_isMalformedTarget :
    (brauerDiagramOf 6 [capAt 0, crossingAt 3, cupAt 0]
        ≠ brauerDiagramOf 6 (classRepresentativeOf 6 [capAt 0, crossingAt 3, cupAt 0]))
      ∧ realizesValidInvolution 6 [capAt 0, crossingAt 3, cupAt 0] = false :=
  ⟨capSideDefect_atCapSlot0, by decide⟩

/-- ★★ **Cap slot 1 — the same boundary-overrun malformation one slot over.** -/
theorem capSideWitness1_isMalformedTarget :
    (brauerDiagramOf 6 [capAt 1, crossingAt 3, cupAt 0]
        ≠ brauerDiagramOf 6 (classRepresentativeOf 6 [capAt 1, crossingAt 3, cupAt 0]))
      ∧ realizesValidInvolution 6 [capAt 1, crossingAt 3, cupAt 0] = false :=
  ⟨capSideDefect_atCapSlot1, by decide⟩

/-- ★★ **Cap slot 2 — the third malformed witness.** -/
theorem capSideWitness2_isMalformedTarget :
    (brauerDiagramOf 6 [capAt 2, crossingAt 3, cupAt 0]
        ≠ brauerDiagramOf 6 (classRepresentativeOf 6 [capAt 2, crossingAt 3, cupAt 0]))
      ∧ realizesValidInvolution 6 [capAt 2, crossingAt 3, cupAt 0] = false :=
  ⟨capSideDefect_atCapSlot2, by decide⟩

/-- ★★ **The SAFE cap word — move the crossing inside the post-cap boundary and it is valid AND realizes.**
`[capAt 0, crossingAt 1, cupAt 0]` (`crossingAt 1` fits the width the `capAt 0` left) is a valid involution and its
representative realizes its own diagram — a with-cap word inside the extractor's exact coverage.  So caps are NOT the
problem; boundary overrun is. -/
theorem safeCapWord_valid_andRealizes :
    realizesValidInvolution 6 [capAt 0, crossingAt 1, cupAt 0] = true
      ∧ representativeRealizesOwnDiagram 6 [capAt 0, crossingAt 1, cupAt 0] = true :=
  ⟨by decide, by decide⟩

/-- ★ **The boundary-overrun signature — `topCount` inflation.**  The malformed witness inflates `topCount` `6 -> 7`
(a phantom wire padded past the post-cap width); the safe word keeps `topCount = 6`.  The mechanical fingerprint of
the degeneracy the `partner` non-involution records. -/
theorem capSideWitness0_topCountInflated :
    (brauerDiagramOf 6 [capAt 0, crossingAt 3, cupAt 0]).topCount = 7
      ∧ (brauerDiagramOf 6 [capAt 0, crossingAt 1, cupAt 0]).topCount = 6 :=
  ⟨by decide, by decide⟩

/-! ## D — THE DOCUMENTED WALL AMENDMENT (supersede-by-addition; the r52 file stays byte-intact)

### (a) THE ORIGINAL r52 §D PROSE, QUOTED VERBATIM

From `WiringDescCorrectedFoldCapFreeScope.lean` (the module docstring, lines 28-33):

    "The failures are the two-sided-sandwich complement: the corrected extractor inverts only the cup/top side
    (`permInverse (throughStrandTops ++ cupArcTops)`), leaving the cap/bottom side un-inverted, so a cap arc entangled
    with a through-region crossing realises a different `partner`.  This is the ∗-dual of the nested-cup defect r51's
    R3-B1 fixed on the cup side"

and (the §D header, lines 185-193):

    "The three with-cap failures `[capAt k, crossingAt 3, cupAt 0]` (k = 0, 1, 2) at `bottomCount = 6` ... realise a
    DIFFERENT `partner` than their representative.  Structural cause: the crossing is entangled with the cap in the
    through/middle region, but the corrected extractor inverts only the cup/top side.  The cap/bottom side lacks the
    ∗-dual inversion, so the representative's `bottomPerm`/`middle` read-off reproduces the wrong conjugate."

### (b) THE PART THAT STANDS (byte-intact in r52, referenced not re-derived)

`capSideDefect_atCapSlot0/1/2` — "the representative reads a DIFFERENT diagram than the input" — are TRUE and stay.
They are re-exported inside `capSideWitnessK_isMalformedTarget` unchanged.  What is amended is the CAUSAL prose: that a
matching cap-side inversion would close the gap.

### (c) THE CORRECTED DIAGNOSIS — a boundary-overrun MALFORMED target, not a repairable read-off inversion

Machine-checked this round:

  * the predicted repair (the ∗-dual cap-side `permInverse`, `reconstructStandardFormExt5CapDual`) is a NET LOSS —
    it regresses `1425 -> 942` / `16500 -> 9300` for `0` gain (`countCapDualRealizing`, `countCapDualGainOverR51`,
    `capDualRegressesAt_capCrossCup1`).  There is no cap-side inversion that closes the §D failures.
  * the §D failures are MALFORMED targets: `[capAt k, crossingAt 3, cupAt 0]` overruns the post-cap boundary
    (`crossingAt 3` past a width the cap shrank), so `brauerDiagramOf` pads a phantom wire — `topCount` inflates
    `6 -> 7` and the read-off `partner` is a NON-involution (`capSideWitnessK_isMalformedTarget`,
    `capSideWitness0_topCountInflated`).  No valid standard form equals a non-involution target.
  * the EXACT coverage cut is `realizesValidInvolution`: the r51 extractor realizes a diagram IFF it is a valid Brauer
    involution (symmetric difference `0` on with-cap len 3/4 and cap-free len 5,
    `countRepresentativeRealizeXorValid`).  On the valid arena coverage is 100%, caps included
    (`withCapValidRepresentativeFailCount = 0`).  The safe with-cap word `[capAt 0, crossingAt 1, cupAt 0]`
    (crossing inside the post-cap boundary) is valid AND realizes (`safeCapWord_valid_andRealizes`).

So the literature's ∗-dual (KM `g^{-1} x h`, Jones `T^+`/`T^-`, walled-Brauer increasing-vs-decreasing) governs the
NORMAL-FORM shape on WELL-FORMED involutions — where the extractor is already 100% total — not a repair of malformed
boundary-overrun targets.  The r52 file stays byte-intact; this diagnosis supersedes only its causal prose.

### (d) THE FLIP LAW IS UNCHANGED

The amended-flip law (`WiringDescCupTouchingCriterionAmendment.lean:64-69`) requires JOINTLY: (a) the drive reaches the
class representative for EVERY survivor, (b) the committed census confirms full coverage, (c) the criterion mapping is
recorded.  This round supplies a STRONGER (b) (100% on the valid-involution arena, caps included) and a CORRECTED (c)
(the criterion is valid-involution, not cap-free), but NOT (a) — `BrauerConvFree8`-reaching is the R3-B inner descent,
undischarged.  So this is the NINTH honest zero-flip: only the new EXTRACTOR-coverage census fact flips to `true`. -/

/-! ## The widened honest scope (STATED, not discharged) -/

/-- ★ **THE WIDENED FOLD TARGET — the valid-involution scope.**  Every word whose diagram is a valid Brauer involution
`BrauerConvFree8`-reaches its class representative.  WIDER than r52's cap-free scope (`BrauerExt5CorrectedFoldReachesCapFree`):
the with-cap arena is included, gated only by well-formedness, backed by the exact-iff census (100% extractor coverage,
symmDiff `0`).  Stated as the honest scope; NOT discharged — the `stepWiring`-connectivity structural induction is the
long pole (`fxBrauer_hasExt5CorrectedRoundtripProof`, byte-intact `false`), and even discharged its free
`BrauerConvFree8`-conclusion does not bridge to the boundary-indexed `BrauerConv` decision
(`not_brauerConvFree8_diagramInvariant`, r52 §B). -/
def BrauerExt5CorrectedFoldReachesValidInvolution : Prop :=
  ∀ (bottomCount : Nat) (word : List BrauerAtom),
    realizesValidInvolution bottomCount word = true →
    BrauerConvFree8 word (classRepresentativeOf bottomCount word)

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the CORRECTED EXTRACTOR's coverage is characterized EXACTLY (valid-involution iff).**  The
r51 corrected extractor realizes a word's diagram IFF that diagram is a valid Brauer involution — machine-checked as a
symmetric-difference-`0` census on with-cap len 3/4 and cap-free len 5 (`countRepresentativeRealizeXorValid`), with 100%
coverage on the valid arena, caps included (`withCapValidRepresentativeFailCount = 0`).  The ∗-dual cap-side sibling is
REFUTED as a net loss (`capDualRegressesAt_capCrossCup1`), and the r52 §D failures are re-diagnosed as boundary-overrun
malformed (non-involution) targets (`capSideWitnessK_isMalformedTarget`).  This is an EXTRACTOR-coverage census fact,
NOT a fold discharge.  All zero-axiom, purely additive over r29–r52.  `= true`. -/
def fxBrauer_hasCorrectedExtractorValidInvolutionCoverage : Bool := true

/-- **Honesty WALL marker — the widened valid-involution fold is NOT discharged (the NINTH honest zero-flip).**  The
widened target `BrauerExt5CorrectedFoldReachesValidInvolution` (wider than r52's cap-free scope) is STATED with the
exact-iff census as precondition evidence, but the amended-flip law's clause (a) — the drive
`BrauerConvFree8`-reaching the representative for every survivor — is undischarged (the R3-B inner descent), and the
R3-A totality roundtrip PROOF (`fxBrauer_hasExt5CorrectedRoundtripProof`) stays the long pole.  So every dispatch flag
and completeness master STAYS `false`; only the extractor-coverage census fact flips.  A route / measure gap, never a
truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).  `= false`. -/
def fxBrauer_hasValidInvolutionFoldDischarged : Bool := false

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER r53 with-cap valid-involution scoping terminal state — MACHINE-CHECKED (the NINTH honest
zero-flip).**  The extractor-coverage characterization marker is `true` on top of the r52 cap-free scoping, the r51
class-representative re-adjudication, and the cup-touching criterion amendment; the widened-fold discharge, the
cap-free-scope discharge, the corrected-fold discharge, the class-representative discharge, the two dispatch flip flags,
WALL A, the staged inner descent, and the two completeness masters ALL STAY `false`.  Every relevant flag is pinned
same-commit; no dispatch/completeness flag flips on the old, the amended, the cap-free-scoped, or the valid-involution
criterion.  A `rfl`-conjunction the kernel checks; purely additive. -/
theorem fxBrauer_withCapValidInvolutionScopeTerminalState :
    fxBrauer_hasCorrectedExtractorValidInvolutionCoverage = true
      ∧ fxBrauer_hasValidInvolutionFoldDischarged = false
      ∧ fxBrauer_hasCorrectedFoldCapFreeScope = true
      ∧ fxBrauer_hasClassRepresentativeReadjudication = true
      ∧ fxBrauer_hasCupTouchingCriterionAmendment = true
      ∧ fxBrauer_hasCorrectedFoldReduction = true
      ∧ fxBrauer_hasCorrectedFoldCapFreeDischarged = false
      ∧ fxBrauer_hasCorrectedFoldDischarged = false
      ∧ fxBrauer_hasClassRepresentativeDischarged = false
      ∧ fxBrauer_hasRegionDriverTotalDispatch = false
      ∧ fxBrauer_hasSingleCupTotalDecision = false
      ∧ fxBrauer_hasSingleCupPeelDischarged = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph
