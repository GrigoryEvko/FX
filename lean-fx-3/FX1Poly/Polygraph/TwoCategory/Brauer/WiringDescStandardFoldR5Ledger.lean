import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardFoldGlue
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardFoldPhases
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStagedDescent
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCorrectedFold
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescExtractorLedger

/-! # BRAUER-MIDDLE r5 B3 + B4 + B5 — the TAG-CORRESPONDENCE decomposition (named), the roundtrip WALL, and the
machine-checked terminal r5 ledger

This is the honest terminal ledger for the BRAUER-MIDDLE r5 round (#2013), scoped to R3-A.  The round SHIPPED,
zero-axiom, TWO of the three R3-A legs the r4 ledger named:

  * **B1 — R3-A-INTERIOR** (`fxBrauer_hasInteriorCupFold = true`, `Brauer/WiringDescStandardFoldInterior.lean`).  The
    interior-offset cup phase fold `cupFold_creates_atOffset` generalizing the r4 position-`0` `cupFold_creates` to the
    `throughBottoms.length`-offset cup block the corrected extractor `reconstructStandardFormExt5Corrected` fires when
    through-strands are present — via the append-at-front computation `natListInsertAtFront`.  Cross-checked FIRING at
    the nonzero offset `1` behind one through wire.

  * **B2 — R3-A-CROSSING-GLUE** (`fxBrauer_hasSixPhaseGlue = true`, `Brauer/WiringDescStandardFoldGlue.lean`).  The
    six-phase `processBrauer_append` split assembly `standardFormFold_appendSplit` (the Brauer
    `canonicalSpiderFold_connected`-analog skeleton) + the fold-level forest preservation
    `processBrauer_links_isUnionFindForest` + the COMPOSED cap/interior-cup phase fold `capThenCupFold_connects`
    (connecting every cap pair AND every fresh cup pair, composed via `processBrauer_append`) + its survival past any
    trailing crossing/circle word `capThenCupFold_connects_survivesTail` (the T-CONNECT direction on the cap/cup arcs,
    the crossing phases threaded as connectivity-monotone words).  Cross-checked FIRING on the mixed word
    `[capAt 0, cupAt 2]`.

## B3 — R3-A-TAGCORR, the third leg, DECOMPOSED and NAMED (the standing long-pole residual)

The recon decomposed the tag correspondence into four sub-legs; the r5 feasibility call is that TAGCORR alone is a
full round or more, so this round NAMES the sub-legs and ships no fabricated flip:

  * **T-ENUM** — the read-offs `capArcFeet` / `throughStrandPerm` / `cupArcTops` / `permInverse` enumerate exactly
    `d`'s cap arcs (foot order), through-strands (top order), and cup arcs (nested order), with the two crossing words
    the correct conjugators.  A property of the `filterMap` read-offs (`Brauer/WiringDescArcExtractor.lean`,
    `Brauer/WiringDescArcMiddle.lean`); GENUINELY NEW, no FROB analog.

  * **T-CONNECT** — for every arc `(i, j)` of `d`, the six-phase fold state has `matchingSameComponent … i j = true`.
    Mostly a LEMMA AWAY: supplied by the r5 GLUE phase folds (`capThenCupFold_connects` connects each cap / cup pair,
    the crossing-graph bridge connects each through-strand, all surviving by
    `processBrauer_isSameComponent_ofBase` / `capThenCupFold_connects_survivesTail`).

  * **T-DISJOINT** (THE LONG POLE) — for every boundary pair NOT matched by `d`, `matchingSameComponent … = false`;
    equivalently every union-find component of the fold holds `≤ 2` boundary nodes (a forest-cardinality invariant
    threaded through all six phases).  GENUINELY NEW, NO FROB analog (FROB's target is all-connected, so this
    direction was vacuous there) — the real reason TAGCORR is the long pole.

  * **T-CLOSE** — the target-closure lemma `extractDiagram_realizes_partner_ofConnectivity` (the Brauer twin of FROB's
    `spiderPartition_of_allConnected`, closing against a partner LIST rather than a fixed all-zero partition)
    reassembling `extractDiagram foldState = d` from T-CONNECT ∧ T-DISJOINT ∧ length ∧ loops.  NEW lemma, mechanical
    once T-CONNECT ∧ T-DISJOINT land.

## B4 — the roundtrip WALL (no fabricated flip; #2013 does NOT close)

Even a fully closed R3-A (all three legs) only flips the EXTRACTOR-TOTALITY node
(`fxBrauer_hasExt5CorrectedRoundtripProof` / `fxBrauer_hasExt5TotalExtractorRoundtrip`), and those flip
hypothesis-free ONLY when T-ENUM ∧ T-DISJOINT ∧ T-CLOSE are all discharged.  T-DISJOINT and T-ENUM are unbuilt, so
they STAY `false` — no partial flip.  Above R3-A there still stand R3-B-INNER and R3-C-DRIVER (the full completeness
driver, capped at the pass-5-arc interleaved-arc wall), so `fxBrauer_hasBrauerV2FullCompleteness` /
`fxBrauer_hasBrauerCompleteness` / `fxBrauer_hasFreeBrauerStraighteningNF` STAY `false`; #2013 does not close.  Per
the 110-percent directive every residual is a ROUTE / totality gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889
Thm 2.6 guarantees completeness; the corrected extractor's exhaustive size-8 census makes the roundtrip's TRUTH
concrete).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## B3 — the named TAG-CORRESPONDENCE residual -/

/-- **Honesty WALL marker — the TAG CORRESPONDENCE (R3-A-TAGCORR) is DECOMPOSED into four sub-legs, all unbuilt.**
`R3-A-TAGCORR = T-ENUM ∧ T-CONNECT ∧ T-DISJOINT ∧ T-CLOSE` (file header).  T-CONNECT is mostly supplied by the r5
GLUE phase folds (`capThenCupFold_connects` + monotonicity), but T-ENUM (the read-off enumeration) and above all
T-DISJOINT (the forest-cardinality no-over-connection invariant, THE long pole, no FROB analog) and T-CLOSE (the
target-closure lemma `extractDiagram_realizes_partner_ofConnectivity`) are unbuilt.  No sub-leg lemma is fabricated
this round.  `= false`. -/
def fxBrauer_hasTagCorrDecomposition : Bool := false

/-! ## B5 — the machine-checked terminal r5 ledger -/

/-- ★★★ **The BRAUER-MIDDLE r5 GRAND LEDGER — MACHINE-CHECKED.**  The two shipped R3-A legs (`fxBrauer_hasInteriorCupFold`
= B1 interior, `fxBrauer_hasSixPhaseGlue` = B2 crossing-glue) are `true`, on top of the r4 cup/cap phase folds
(`fxBrauer_hasCupCapPhaseFolds`), and EVERY wall — the R3-A-TAGCORR decomposition node, the R3-A-PROOF roundtrip node,
the extractor-totality roundtrip node, the r3 residual nodes, and the master V2 / connectivity / straightening
completeness flags — is `false`.  A `rfl`-conjunction the kernel checks over the shipped markers: the round shipped
two of the three R3-A legs (interior + crossing-glue), but the tag correspondence (T-ENUM ∧ T-DISJOINT ∧ T-CLOSE) is
unbuilt, so the roundtrip proof is not assembled, #2013 does NOT close, and no master flip is fabricated. -/
theorem fxBrauer_r5GrandLedger :
    (fxBrauer_hasCupCapPhaseFolds = true
      ∧ fxBrauer_hasInteriorCupFold = true
      ∧ fxBrauer_hasSixPhaseGlue = true)
    ∧ (fxBrauer_hasTagCorrDecomposition = false
      ∧ fxBrauer_hasInteriorCupFoldRoundtrip = false
      ∧ fxBrauer_hasSixPhaseGlueRoundtrip = false)
    ∧ (fxBrauer_hasExt5CorrectedRoundtripFromPhaseFolds = false
      ∧ fxBrauer_hasExt5CorrectedRoundtripProof = false
      ∧ fxBrauer_hasExt5TotalExtractorRoundtrip = false)
    ∧ (fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasCorrectedFoldDischarged = false)
    ∧ (fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false) :=
  ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-! ## The terminal honesty marker -/

/-- ★★ **Honesty marker — BRAUER-MIDDLE r5 did NOT close #2013 (the honest wall, two of three R3-A legs shipped).**
The round shipped R3-A-INTERIOR (the interior-offset cup phase fold) and R3-A-CROSSING-GLUE (the six-phase
`processBrauer_append` split + the composed cap/interior-cup phase-fold connectivity), each zero-axiom and
structural, cross-checked firing on concrete instances.  These are two of the three R3-A legs.  But the third leg —
the TAG CORRESPONDENCE R3-A-TAGCORR (T-ENUM ∧ T-DISJOINT ∧ T-CLOSE, of which the forest-cardinality disjointness
T-DISJOINT is the long pole, no FROB analog) — is decomposed and NAMED, not built.  So
`fxBrauer_hasExt5CorrectedRoundtripProof` / `fxBrauer_hasExt5TotalExtractorRoundtrip` stay `false` (no flip
fabricated), the masters stay `false`, and #2013 does not close.  The exact standing wall is R3-A-TAGCORR (then,
above R3-A, still R3-B-INNER ∧ R3-C-DRIVER) — every one a ROUTE / totality gap, never a truth gap.  `= false`. -/
def fxBrauer_hasBrauerMiddleR5Complete : Bool := false

end FX1Poly.Polygraph
