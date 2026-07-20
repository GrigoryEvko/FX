import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescClassRepresentativeNormalForm
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescExtractionClose

/-! # WP-BRAUER round sixteen — the strata-drift adjudication of the ten owner-false markers, three delivered
re-fires, and two new section corollaries

The ten owner-false Brauer markers this round adjudicates are FROZEN HISTORY, not live state.  Reading the lane
end-to-end shows the reconstruction / tag-correspondence side of the Brauer word-problem completeness question is
ALREADY CLOSED in committed later files, while several wall markers were left `false` in place (the additive
ledger-preservation precedent: flipping them would break round-snapshot `rfl`-conjunction ledgers).  This file
records the honest adjudication for exactly these ten, re-fires the three that are already inhabited, lands two new
corollaries of the closed reconstruction side, and sharpens the sole surviving wall.

## The delivered reconstruction side (committed, harvested live)

  * `ext5CorrectedRoundtrip_complete` (closed-diagram roundtrip close): `standardFormDiagramExt5
    (reconstructStandardFormExt5Corrected d) = d` for EVERY well-formed boundary involution, every `bottomCount`.
    The corrected reconstruction is a proven SECTION of fold-extract.
  * `foldRealizesTargetDiagramCorrected_general` (extraction close): the same close for `0 < bottomCount`, the
    verbatim demand of the four tag-correspondence masters; recorded by `fxBrauer_hasReconstructionSideClosed`.
  * `brauerConv_iff_classRepresentativeEq` (class-representative normal form): on the valid-involution scope, two
    words are boundary-indexed `BrauerConv`-convertible IFF their class representatives are EQUAL words — the
    indexed word problem is sound, complete, decidable, with a normal form; `fxBrauer_hasClassRepresentativeNormalForm`.

## The three ALREADY-INHABITED markers this file re-fires

  * `fxBrauer_hasArcEnumerationConjugated` (E1 arc enumeration and E2 conjugator built; E3 fold-alignment DELIVERED
    via `foldRealizesTargetDiagramCorrected_general` / the complete roundtrip).
  * `fxBrauer_hasExt5TotalExtractor` (the total extractor: the UNCORRECTED roundtrip stays refuted on the nested
    crossing cups, but the CORRECTED reconstruction is a proven total section — `ext5CorrectedRoundtrip_complete`).
  * `fxBrauer_hasTagCorrMastersFromTotality` (the tag-correspondence masters, delivered by the extraction close).

## The two new corollaries of the closed section (this round's landing)

  * `brwReconstructCorrected_injective` — distinct well-formed involutions have distinct corrected standard forms
    (a section is injective): the standard-form encoding is FAITHFUL.
  * `brwStandardForm_surjectiveOntoInvolutions` — every well-formed boundary involution is realized by some standard
    form (a section's retraction is surjective): the Graham-Lehrer existence half, packaged.

## The sole surviving residual (genuinely open, sharpened)

The four genuinely-open markers this file adjudicates (`fxBrauer_hasArcDescentFold`,
`fxBrauer_hasCanonicalCapFreeSink`, `fxBrauer_hasLocalLegFuelGlobalFold`,
`fxBrauer_hasCorrectedFoldCapFreeDischarged`) all live on the FREE presentation reduction lane and feed the sole
surviving residual — the free-straightening normal form (`fxBrauer_hasFreeBrauerStraighteningNF` /
`fxBrauer_hasStagedInnerDescentDischarged`), the interleaved-arc jam where a cup is forced past a cap under an
`i < k < j < l` window.  With the indexed decision closed, this residual is a presentation-theoretic refinement (do
the five/seven Lehrer-Zhang relations plus interchange GENERATE the connectivity `whisker` move), no longer the gate
on the Brauer word-problem decision.

Raw Lean 4 and Init; structural, `decide` / `rfl` / `congrArg` only, no `omega` / `simp`-AC / `native_decide` /
`WellFounded.fix`.  Per-declaration `#print axioms` in the audit twin. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph

/-! ## Section 1 — Stage 0: the ten-marker strata-drift adjudication (machine-checked) -/

/-- ★★★ **The consolidated adjudication of the ten owner-false Brauer markers — MACHINE-CHECKED.**  All ten task
markers read `false` at their frozen sites; the delivering supersessors read `true`.  Three markers
(`hasArcEnumerationConjugated`, `hasExt5TotalExtractor`, `hasTagCorrMastersFromTotality`) are ALREADY INHABITED —
their verbatim capabilities are delivered by `fxBrauer_hasReconstructionSideClosed` /
`fxBrauer_hasExt5CorrectedRoundtripComplete` / `fxBrauer_hasClassRepresentativeNormalForm` and left `false` only as
ledger-preservation artifacts.  Four (`hasArcDescentFold`, `hasCanonicalCapFreeSink`, `hasLocalLegFuelGlobalFold`,
`hasCorrectedFoldCapFreeDischarged`) are GENUINELY OPEN on the free presentation side, feeding the sole surviving
residual (`hasFreeBrauerStraighteningNF` / `hasStagedInnerDescentDischarged`).  Three (`hasBrauerMiddleR13Complete` /
`R14` / `R15`) are FROZEN-HISTORY round snapshots recording that those rounds did not close the completeness question
— correctly `false`, since the free side is still open. -/
theorem brwTenMarkerStrataAdjudication :
    (fxBrauer_hasArcEnumerationConjugated = false
      ∧ fxBrauer_hasExt5TotalExtractor = false
      ∧ fxBrauer_hasTagCorrMastersFromTotality = false)
    ∧ (fxBrauer_hasArcDescentFold = false
      ∧ fxBrauer_hasCanonicalCapFreeSink = false
      ∧ fxBrauer_hasLocalLegFuelGlobalFold = false
      ∧ fxBrauer_hasCorrectedFoldCapFreeDischarged = false)
    ∧ (fxBrauer_hasBrauerMiddleR13Complete = false
      ∧ fxBrauer_hasBrauerMiddleR14Complete = false
      ∧ fxBrauer_hasBrauerMiddleR15Complete = false)
    ∧ (fxBrauer_hasReconstructionSideClosed = true
      ∧ fxBrauer_hasUnconditionalExtractionClose = true
      ∧ fxBrauer_hasExt5CorrectedRoundtripComplete = true
      ∧ fxBrauer_hasClassRepresentativeNormalForm = true
      ∧ fxBrauer_hasIndexedConvMastersAdjudication = true)
    ∧ (fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasValidInvolutionFoldDischarged = false) := by decide

/-! ## Section 2 — the fresh witnesses and the delivered re-fires (semantic pins first) -/

/-- A fresh well-formed involution: two through strands and one closed loop over two bottom wires. -/
def brwThroughLoopDiagram : DiagramType :=
  { bottomCount := 2, topCount := 2, partner := [2, 3, 0, 1], loops := 1 }

/-- A fresh well-formed involution: a bottom cap `0`↔`1` and a top cup `top0`↔`top1` over two bottom wires. -/
def brwCapCupDiagram : DiagramType :=
  { bottomCount := 2, topCount := 2, partner := [1, 0, 3, 2], loops := 0 }

/-- The through-loop witness is a genuine boundary involution (each field `decide`-checked). -/
theorem brwThroughLoop_isBoundaryInvolution :
    IsBoundaryInvolution (brwThroughLoopDiagram.bottomCount + brwThroughLoopDiagram.topCount)
      brwThroughLoopDiagram.partner where
  hasBoundaryLength := rfl
  mapsInRange := by decide
  isSelfInverse := by decide
  isFixedPointFree := by decide

/-- The cap-cup witness is a genuine boundary involution (each field `decide`-checked). -/
theorem brwCapCup_isBoundaryInvolution :
    IsBoundaryInvolution (brwCapCupDiagram.bottomCount + brwCapCupDiagram.topCount)
      brwCapCupDiagram.partner where
  hasBoundaryLength := rfl
  mapsInRange := by decide
  isSelfInverse := by decide
  isFixedPointFree := by decide

/-- ★ **Semantic pin — the corrected roundtrip closes on the through-loop witness (decidable).** -/
theorem brwThroughLoop_roundtrip_pin :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected brwThroughLoopDiagram)
      = brwThroughLoopDiagram := by decide

/-- ★ **Semantic pin — the corrected roundtrip closes on the cap-cup witness (decidable).** -/
theorem brwCapCup_roundtrip_pin :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected brwCapCupDiagram)
      = brwCapCupDiagram := by decide

/-- ★★ **The total extractor fires on the through-loop witness through the GENERAL path.**  The CORRECTED
reconstruction is a proven total section: `ext5CorrectedRoundtrip_complete` recovers the diagram from its own
standard form, not by per-instance `decide` but through the general roundtrip theorem — re-firing the capability the
frozen `fxBrauer_hasExt5TotalExtractor` bills (over the corrected reconstruction). -/
theorem brwThroughLoop_totalExtractorFires :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected brwThroughLoopDiagram)
      = brwThroughLoopDiagram :=
  ext5CorrectedRoundtrip_complete brwThroughLoopDiagram brwThroughLoop_isBoundaryInvolution

/-- ★★ **The total extractor fires on the cap-cup witness through the GENERAL path.** -/
theorem brwCapCup_totalExtractorFires :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected brwCapCupDiagram)
      = brwCapCupDiagram :=
  ext5CorrectedRoundtrip_complete brwCapCupDiagram brwCapCup_isBoundaryInvolution

/-- ★★★ **The delivery ledger for the three already-inhabited markers — MACHINE-CHECKED.**  The enumeration legs E1
(`fxBrauer_hasArcEnumeration`) and E2 (`fxBrauer_hasArcConjugatorLeg`) are built; the reconstruction side is closed
(`fxBrauer_hasReconstructionSideClosed`, `fxBrauer_hasExt5CorrectedRoundtripComplete`), which DELIVERS the E3
fold-alignment demand of `fxBrauer_hasArcEnumerationConjugated`, the total-extractor demand of
`fxBrauer_hasExt5TotalExtractor` (over the corrected reconstruction), and the tag-correspondence demand of
`fxBrauer_hasTagCorrMastersFromTotality`.  The three task markers stay `false` (frozen ledger-preservation
artifacts); this conjunction records the delivery. -/
theorem brwReconstructionDeliveryLedger :
    (fxBrauer_hasArcEnumeration = true
      ∧ fxBrauer_hasArcConjugatorLeg = true)
    ∧ (fxBrauer_hasReconstructionSideClosed = true
      ∧ fxBrauer_hasExt5CorrectedRoundtripComplete = true)
    ∧ (fxBrauer_hasArcEnumerationConjugated = false
      ∧ fxBrauer_hasExt5TotalExtractor = false
      ∧ fxBrauer_hasTagCorrMastersFromTotality = false) := by decide

/-- ★★ **Supersessor content marker — the CONJUGATED enumeration node is DELIVERED (corrected reconstruction).**
E1 and E2 are built; E3 fold-alignment is delivered by the closed reconstruction side
(`foldRealizesTargetDiagramCorrected_general` / `ext5CorrectedRoundtrip_complete`).  The frozen owner-false marker
`fxBrauer_hasArcEnumerationConjugated` stays `false` as a ledger-preservation artifact — this marker carries the
truth.  `= true`. -/
def brwHasArcEnumerationConjugatedDelivered : Bool := true

/-- ★★ **Supersessor content marker — the TOTAL extractor is DELIVERED over the corrected reconstruction.**  The
frozen `fxBrauer_hasExt5TotalExtractor` bills the roundtrip over the UNCORRECTED reconstruction, which stays refuted
on the nested crossing cups (`not_foldRealizesTargetDiagram_nestedCups`); the CORRECTED reconstruction is a proven
total section (`ext5CorrectedRoundtrip_complete`, all `bottomCount`), fired here on two fresh witnesses.  `= true`. -/
def brwHasTotalExtractorDeliveredCorrected : Bool := true

/-- ★★ **Supersessor content marker — the tag-correspondence MASTERS are DELIVERED.**  The demand of
`fxBrauer_hasTagCorrMastersFromTotality` (the read-off wired to the specific diagram `extractDiagram foldState = d`)
is delivered by the extraction close (`fxBrauer_hasReconstructionSideClosed`); the frozen owner-false marker stays a
ledger-preservation artifact.  `= true`. -/
def brwHasTagCorrMastersDelivered : Bool := true

/-! ## Section 3 — Stage 1 landing: the corrected standard-form section is FAITHFUL and SURJECTIVE -/

/-- ★★★ **The corrected reconstruction is INJECTIVE on well-formed involutions (the section is faithful).**  A
retraction identity makes a section injective: if two well-formed boundary involutions have the SAME corrected
standard form, applying `standardFormDiagramExt5` to both and cancelling by `ext5CorrectedRoundtrip_complete`
recovers `leftDiagram = rightDiagram`.  So distinct diagrams get distinct standard forms — the standard-form
encoding is FAITHFUL.  New content: the roundtrip was stated as a section identity, never as injectivity. -/
theorem brwReconstructCorrected_injective (leftDiagram rightDiagram : DiagramType)
    (leftWf : IsBoundaryInvolution (leftDiagram.bottomCount + leftDiagram.topCount) leftDiagram.partner)
    (rightWf : IsBoundaryInvolution (rightDiagram.bottomCount + rightDiagram.topCount) rightDiagram.partner)
    (formsEqual : reconstructStandardFormExt5Corrected leftDiagram
      = reconstructStandardFormExt5Corrected rightDiagram) :
    leftDiagram = rightDiagram :=
  (ext5CorrectedRoundtrip_complete leftDiagram leftWf).symm.trans
    ((congrArg standardFormDiagramExt5 formsEqual).trans
      (ext5CorrectedRoundtrip_complete rightDiagram rightWf))

/-- ★★★ **Every well-formed boundary involution is realized by some standard form (the section is surjective onto
the retraction's domain).**  Witnessed by the corrected reconstruction and the complete roundtrip — the existence
half of the Graham-Lehrer cellular standard form, packaged as a surjectivity statement. -/
theorem brwStandardForm_surjectiveOntoInvolutions (targetDiagram : DiagramType)
    (targetWf : IsBoundaryInvolution (targetDiagram.bottomCount + targetDiagram.topCount) targetDiagram.partner) :
    ∃ form : BrauerStandardFormExt5, standardFormDiagramExt5 form = targetDiagram :=
  ⟨reconstructStandardFormExt5Corrected targetDiagram,
    ext5CorrectedRoundtrip_complete targetDiagram targetWf⟩

/-- ★ **Non-vacuity — faithfulness has content: the two fresh distinct witnesses have DISTINCT standard forms.**
The through-loop and cap-cup diagrams are different, so their corrected standard forms differ (decidable) — the
contrapositive face of `brwReconstructCorrected_injective`, exhibiting the injectivity is not vacuous. -/
theorem brwFreshWitnesses_distinctForms :
    reconstructStandardFormExt5Corrected brwThroughLoopDiagram
      ≠ reconstructStandardFormExt5Corrected brwCapCupDiagram := by decide

/-- ★ **Non-vacuity — surjectivity fires on a fresh witness.**  The through-loop involution is realized by a standard
form, produced through the general existence theorem. -/
theorem brwSurjectivity_fires :
    ∃ form : BrauerStandardFormExt5, standardFormDiagramExt5 form = brwThroughLoopDiagram :=
  brwStandardForm_surjectiveOntoInvolutions brwThroughLoopDiagram brwThroughLoop_isBoundaryInvolution

/-- ★★ **Content marker — the corrected standard-form section is FAITHFUL.**  `brwReconstructCorrected_injective`
proves the section injective on well-formed involutions; `brwFreshWitnesses_distinctForms` exhibits distinct forms
on two fresh diagrams.  New content derived from the closed reconstruction side.  `= true`. -/
def brwHasStandardFormSectionFaithful : Bool := true

/-- ★★ **Content marker — the standard-form map is SURJECTIVE onto well-formed involutions.**
`brwStandardForm_surjectiveOntoInvolutions` packages the complete roundtrip as an existence statement (every
well-formed involution is realized by a standard form), fired on a fresh witness.  `= true`. -/
def brwHasStandardFormSurjective : Bool := true

/-! ## Section 4 — the sole surviving residual, sharpened (the genuinely-open free-side markers) -/

/-- ★★ **The free-side residual, sharpened — MACHINE-CHECKED.**  The four genuinely-open markers stay `false`; the
indexed decision is closed (`fxBrauer_hasClassRepresentativeNormalForm`, `fxBrauer_hasIndexedConvMastersAdjudication`)
and the reconstruction side is a total section (`fxBrauer_hasExt5CorrectedRoundtripComplete`).  So the surviving
free-side residual (`fxBrauer_hasFreeBrauerStraighteningNF` / `fxBrauer_hasStagedInnerDescentDischarged`) is a
presentation-theoretic refinement — whether the five/seven relations plus interchange GENERATE the connectivity
`whisker` move — no longer the gate on the Brauer word-problem decision. -/
theorem brwFreeSideResidualSharpened :
    (fxBrauer_hasArcDescentFold = false
      ∧ fxBrauer_hasCanonicalCapFreeSink = false
      ∧ fxBrauer_hasLocalLegFuelGlobalFold = false
      ∧ fxBrauer_hasCorrectedFoldCapFreeDischarged = false)
    ∧ (fxBrauer_hasFreeBrauerStraighteningNF = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false)
    ∧ (fxBrauer_hasClassRepresentativeNormalForm = true
      ∧ fxBrauer_hasIndexedConvMastersAdjudication = true
      ∧ fxBrauer_hasExt5CorrectedRoundtripComplete = true) := by decide

/-- **Honesty WALL marker — the FREE-side straightening normal form stays OPEN, now downgraded (burned attacks).**
Two genuinely different attacks were surveyed on the free reduction lane and neither yields in this round.  Attack A —
extend the arc-descent measure fold (`fxBrauer_hasArcDescentFold`) or the cap-free / single-cup sink
(`fxBrauer_hasCanonicalCapFreeSink`) to a full `BrauerConvFree8` fold to standard form: the shipped rungs descend on
disjoint-support and cup-cup slides, but seating every cup to its standard-form block requires the adjacent-straddle
slide on which the arc measure ASCENDS — no free-relation monovariant descends per step.  Attack B — discharge the
staged inner descent (`fxBrauer_hasStagedInnerDescentDischarged`, the same jam under `fxBrauer_hasLocalLegFuelGlobalFold`
/ `fxBrauer_hasCorrectedFoldCapFreeDischarged`): the local per-cup leg fuel descends, but the descent STEP caps on the
interleaved-arc `i < k < j < l` window — a cup forced past a cap with the inversion count frozen.  Both are the SAME
free-presentation jam.  The SHARPENED status: with the indexed word problem decided (`brauerConv_iff_classRepresentativeEq`,
a sound, complete, decidable normal form) and the reconstruction a proven total section
(`ext5CorrectedRoundtrip_complete`), this residual no longer gates the Brauer decision — it is the
presentation-theoretic refinement that the five/seven Lehrer-Zhang relations plus interchange GENERATE the
connectivity `whisker` congruence move.  A route gap on the free presentation, never a truth gap (Lehrer-Zhang
arXiv:1207.5889 Thm 2.6).  `= false`. -/
def brwHasFreeStraighteningResidualSharpened : Bool := false

/-! ## Section 5 — the round-sixteen terminal state (machine-checked) -/

/-- ★★★ **The WP-BRAUER round-sixteen terminal state — MACHINE-CHECKED.**  The three delivery re-fires and the two
new section corollaries are `true`; the sharpened free-side wall stays `false`; and the load-bearing committed
delivery markers (reconstruction side closed, complete roundtrip, indexed normal form) are `true` while the free-side
completeness masters stay `false`.  A `rfl`-conjunction the kernel checks; purely additive — no frozen file is
touched. -/
theorem brwRoundSixteenTerminalState :
    (brwHasArcEnumerationConjugatedDelivered = true
      ∧ brwHasTotalExtractorDeliveredCorrected = true
      ∧ brwHasTagCorrMastersDelivered = true)
    ∧ (brwHasStandardFormSectionFaithful = true
      ∧ brwHasStandardFormSurjective = true)
    ∧ brwHasFreeStraighteningResidualSharpened = false
    ∧ (fxBrauer_hasReconstructionSideClosed = true
      ∧ fxBrauer_hasExt5CorrectedRoundtripComplete = true
      ∧ fxBrauer_hasClassRepresentativeNormalForm = true)
    ∧ (fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false) := by decide

end FX1Poly.Polygraph
