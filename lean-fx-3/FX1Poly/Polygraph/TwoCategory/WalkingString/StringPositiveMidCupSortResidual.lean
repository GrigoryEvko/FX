import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMidZeroValleyReassembly
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyDegenerateSplit

/-! # WalkingString/StringPositiveMidCupSortResidual — the doubly-positive wall DECOMPOSED to ONE named cup-sort
brick, with the colour-blind block reassembly gated on it PROVED (FC-3 r40, the positive-mid decomposition)

FC-3 r39 (`StringOneSubProducerBeam`) collapsed the whole adjoint-triple #2020 decision to fire from a SINGLE
remaining colour-keyed sub-producer, `StringCellValleyTraceEquivPositive` (`StringValleyDegenerateSplit`) — the
DOUBLY-positive valley trace-equivalence (positive source width AND positive mid-width `0 < survivorTopTotal`).  That
sub-producer is the last standing wall of the completeness master.  This file DECOMPOSES it.

The recon's dependency tree shows the doubly-positive cell assembly is colour-BLIND EXCEPT for exactly one node: the
positive-mid pure-cup SORT (`pureCupSpine_sort` at positive `bottomCount`).  Every other ingredient of the assembly —
the block split, the cap sort (`stringPureCapSpine_sort_unconditional`, unconditional since r26), the cup
reconstruction, the width telescopes, the append congruence — is already shipped and signature-blind.  So the wall
factors as a SINGLETON conjunction: `StringCellValleyTraceEquivPositive` follows from the ONE named brick

    `StringPositiveMidPureCupDeterminacy`

  — the positive-mid analog of the width-`0` cup determinacy `StringWidthZeroPureCupDeterminacyShared` (r17), verbatim
  except the width-`0` bottom boundary is replaced by an arbitrary `midWidth` carrying `0 < midWidth` (the through-strand
  survivor count).  This is the SHARPENED residual: down from the vague "doubly-positive SORT" to a single
  width-generic pure-cup determinacy obligation.

## What this ships (each zero-axiom, machine-checked)

  * ★ `def StringPositiveMidPureCupDeterminacy` — the single OPEN sub-Prop the wall factors through (W2).  Its
    docstring carries the ADJUDICATION: TRUE by the same forcing argument as the width-`0` case, un-inhabited this
    round because the width-generic sort (the r17 LOCATE/drop assembly re-parameterized off `matchingOfSpineList 0`
    to `matchingOfSpineList midWidth`, ADDING survivor-through-strand re-ranking) is a genuine multi-round port.
  * ★★ `stringPositiveMidSameMatchingValleys_spineTraceEquiv` — the colour-blind BLOCK REASSEMBLY glue, gated on the
    ONE brick, PROVED (W3, the conjunction lemma).  A near-byte-identical token-swap of the shipped mid-`0` block
    reassembly `stringMidZeroSameMatchingValleys_spineTraceEquiv` (`StringMidZeroValleyReassembly`): the CAP arm fires
    the shipped unconditional cap sort, the CUP arm fires the ONE positive-mid brick (in place of the width-`0`
    determinacy proof), and the two arms combine through the generic `spineTraceEquiv_appendCongr`.  The ONLY change
    from the mid-`0` reassembly is the cup boundary width `0 → midWidth` and the cup arm's producer.
  * ★ The distinct-block evidence: `stringPositiveMidDistinctDoubleCupLeftFirst/RightFirst` — the two firing orders of
    a disjoint double-cup over `midWidth = 2` survivors (`G·H`), with EQUAL `matchingOfSpineList 2`
    (`stringPositiveMidDistinctDoubleCup_matchingsAgree`, `by decide`) yet DISTINCT spines
    (`stringPositiveMidDistinctDoubleCup_leftContextLengthsDiffer`, leftContext-length lists `[0, 4] ≠ [2, 0]`,
    `by decide`) — a genuine equal-matching distinct pair at positive mid-width, on which `SpineTraceEquiv.refl`
    FAILS.  `stringPositiveMidReassembly_firesOnDistinctDoubleCup` fires the reassembly (gated on the brick) on that
    pair, relating the two DISTINCT cup spines: the reassembly is non-vacuous, not merely diagonal.

## No flip (honest)

The single remaining sub-producer `StringPositiveMidPureCupDeterminacy` is the un-ported length-rigidity wall, NOT
inhabited this round.  So the block reassembly stays gated on it, `StringCellValleyTraceEquiv` is not inhabited, and
the masters `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) and
`fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) STAY `false`.  This file records — as theorems — that the
wall is now exactly ONE precise, width-generic cup-sort brick (down from the vague doubly-positive SORT), with the
whole colour-blind block assembly gated on it discharged.

Raw Lean 4 + Init.  The block reassembly is a token-swap of the shipped mid-`0` reassembly; the distinct fire's
`matchingOfSpineList 2` reduction is heavy, so this file raises `maxHeartbeats` (`by decide` / `rfl` under the raised
budget — `native_decide` is banned).  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace FX1Poly.Polygraph

/-! ## W2 — the single named sub-Prop the doubly-positive wall factors through -/

/-- ★ **The positive-mid pure-cup determinacy** — the ONE named brick the doubly-positive wall
`StringCellValleyTraceEquivPositive` (`StringValleyDegenerateSplit`) factors through.  Two boundary-chained AND
boundary-word-chained pure-cup string spines over a POSITIVE mid-width bottom boundary (`0 < midWidth`, the
through-strand survivor count) that share their `spineListTopWord` and have EQUAL `matchingOfSpineList midWidth` are
`SpineTraceEquiv`.

Verbatim the width-`0` cup determinacy `StringWidthZeroPureCupDeterminacyShared` (r17, INHABITED by
`stringWidthZeroPureCupDeterminacyShared_proof`) EXCEPT the width-`0` bottom boundary is generalized to an arbitrary
`midWidth` carrying `0 < midWidth` — the survivor strands the cup legs interleave with.

**★ ADJUDICATION (FC-3 r40): TRUE by forcing, un-inhabited this round (multi-round width-generic sort).**  The
width-`0` case (`StringWidthZeroForcingAdjudication`) adjudicated the bare Prop TRUE by forcing: a cup's codomain is
forced by its endpoint mode, and the matching pins each chord's endpoint mode, so the top word is a function of the
matching — equal matching forces equal top word.  The forcing argument is width-agnostic, so the positive-mid Prop is
equally TRUE.  It is NOT inhabited this round because the DERIVATION — the r17 fueled partner-LOCATE
(`stringMatchingLocateAux`) + word-threaded sort (`stringMatchingPureCupSpineSortFueled`) and its enabling bricks
(`stringMatchingLastCup_isShortChord`, `stringMatchingChordShift_below/above`,
`stringDropLastCup_matching_injective`, `matchingOpenWiresCupEndSplit`) — are ALL hardcoded to `matchingOfSpineList 0`
/ the seed `⟨List.range 0, [], 0, 0⟩`.  Re-parameterizing them off `matchingOfSpineList midWidth` / seed
`⟨List.range midWidth, …⟩`, ADDING the survivor-through-strand re-ranking (the `ValleyAppendSplit` #2185 residual), is a
genuine multi-round port — the r17 "NOVEL ASSEMBLY" repeated at positive width.  Cited: Forest–Mimram
(arXiv:2109.05369) — the snake-count measure and the two-critical-pair confluence route the multi-round discharge
should follow. -/
def StringPositiveMidPureCupDeterminacy : Prop :=
  ∀ {overallSource overallTarget : adjointTripleGraph.Mode}
    (midWidth : Nat)
    (bottomWord : ModalityPath adjointTripleGraph overallSource overallTarget)
    (cupFirst cupSecond : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)),
    AllCupArity cupFirst → AllCupArity cupSecond →
    SpineBoundaryChained midWidth cupFirst → SpineBoundaryChained midWidth cupSecond →
    SpineBoundaryWordChained bottomWord cupFirst → SpineBoundaryWordChained bottomWord cupSecond →
    spineListTopWord bottomWord cupFirst = spineListTopWord bottomWord cupSecond →
    0 < midWidth →
    matchingOfSpineList midWidth cupFirst = matchingOfSpineList midWidth cupSecond →
    SpineTraceEquiv adjointTripleModeSignature cupFirst cupSecond

/-! ## W3 — the colour-blind block reassembly gated on the ONE brick (the conjunction lemma) -/

/-- ★★ **The positive-mid string valley block reassembly** (the conjunction lemma, W3).  Two valleys
`capBlock ++ cupBlock` whose cup blocks run from a POSITIVE mid-boundary width `midWidth` (`0 < midWidth`, the cap
block leaving through-strands), with the CAP block `diagram` agreement + length agreement and the CUP block
`matchingOfSpineList midWidth` agreement (plus per-block arities / chains / shared words) are `SpineTraceEquiv`.

The positive-mid mirror of `stringMidZeroSameMatchingValleys_spineTraceEquiv` (`StringMidZeroValleyReassembly`): the
CAP arm reconstructs the full cap arc equality (`stringPureCapSpines_internalCapCountsAgree_ofDiagram` +
`stringPureCapTailsCancel_ofDiagramAndInternalCap`) which the positivity-free `stringPureCapSpine_sort_unconditional`
turns into the cap trace, and the CUP arm runs the ONE named positive-mid brick `StringPositiveMidPureCupDeterminacy`
(in place of the width-`0` proof `stringWidthZeroPureCupDeterminacyShared_proof`).  The two arms combine through the
generic `spineTraceEquiv_appendCongr` (no string clone).  The ONLY changes from the mid-`0` reassembly are the cup
boundary width `0 → midWidth`, the `0 < midWidth` witness, and the cup producer. -/
theorem stringPositiveMidSameMatchingValleys_spineTraceEquiv
    (positiveMidCup : StringPositiveMidPureCupDeterminacy)
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (capBottomCount midWidth : Nat)
    (midPos : 0 < midWidth)
    (capWord midWord : ModalityPath adjointTripleGraph overallSource overallTarget)
    (capBlockFirst capBlockSecond cupBlockFirst cupBlockSecond :
      List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (capPureFirst : AllCapArity capBlockFirst) (capPureSecond : AllCapArity capBlockSecond)
    (cupPureFirst : AllCupArity cupBlockFirst) (cupPureSecond : AllCupArity cupBlockSecond)
    (capChainedFirst : SpineBoundaryChained capBottomCount capBlockFirst)
    (capChainedSecond : SpineBoundaryChained capBottomCount capBlockSecond)
    (cupChainedFirst : SpineBoundaryChained midWidth cupBlockFirst)
    (cupChainedSecond : SpineBoundaryChained midWidth cupBlockSecond)
    (capWordChainedFirst : SpineBoundaryWordChained capWord capBlockFirst)
    (capWordChainedSecond : SpineBoundaryWordChained capWord capBlockSecond)
    (cupWordChainedFirst : SpineBoundaryWordChained midWord cupBlockFirst)
    (cupWordChainedSecond : SpineBoundaryWordChained midWord cupBlockSecond)
    (cupTopWordEq : spineListTopWord midWord cupBlockFirst
      = spineListTopWord midWord cupBlockSecond)
    (capLengthEq : capBlockFirst.length = capBlockSecond.length)
    (capDiagramAgree : (arcStructureOfSpineList capBottomCount capBlockFirst).diagram
      = (arcStructureOfSpineList capBottomCount capBlockSecond).diagram)
    (cupMatchEq : matchingOfSpineList midWidth cupBlockFirst = matchingOfSpineList midWidth cupBlockSecond) :
    SpineTraceEquiv adjointTripleModeSignature
      (capBlockFirst ++ cupBlockFirst) (capBlockSecond ++ cupBlockSecond) := by
  -- CAP arm: reconstruct the full cap arc equality (shipped, positivity-free, width-generic on the cap bottom count).
  have capInternalCapCountsAgree :
      (arcStructureOfSpineList capBottomCount capBlockFirst).internalCapCounts
        = (arcStructureOfSpineList capBottomCount capBlockSecond).internalCapCounts :=
    stringPureCapSpines_internalCapCountsAgree_ofDiagram capBottomCount capBlockFirst capBlockSecond
      capPureFirst capPureSecond capChainedFirst capChainedSecond capDiagramAgree
  have capArcEqual : arcStructureOfSpineList capBottomCount capBlockFirst
      = arcStructureOfSpineList capBottomCount capBlockSecond :=
    stringPureCapTailsCancel_ofDiagramAndInternalCap capBottomCount capBlockFirst capBlockSecond
      capPureFirst capPureSecond capLengthEq capDiagramAgree capInternalCapCountsAgree
  have capTrace : SpineTraceEquiv adjointTripleModeSignature capBlockFirst capBlockSecond :=
    stringPureCapSpine_sort_unconditional capBottomCount capWord capBlockFirst capBlockSecond
      capChainedFirst capChainedSecond capWordChainedFirst capWordChainedSecond
      capPureFirst capPureSecond capArcEqual
  -- CUP arm: the ONE named positive-mid brick on the pure-cup block over the POSITIVE mid-boundary.
  have cupTrace : SpineTraceEquiv adjointTripleModeSignature cupBlockFirst cupBlockSecond :=
    positiveMidCup midWidth midWord cupBlockFirst cupBlockSecond
      cupPureFirst cupPureSecond cupChainedFirst cupChainedSecond
      cupWordChainedFirst cupWordChainedSecond cupTopWordEq midPos cupMatchEq
  exact spineTraceEquiv_appendCongr capTrace cupTrace

/-! ## The distinct-block evidence — a disjoint double-cup over positive mid-width in its two firing orders

The two firing orders of a disjoint double-cup over `midWidth = 2` survivors (`G·H`): the first opens a cup at window
`0` then a cup at window `4` (over the grown `G·H·G·H`); the second opens a cup at window `2` then a cup at window `0`.
Both add two disjoint arcs over the two survivor strands; the FINAL top boundary has the same component structure in
both orders, so their `matchingOfSpineList 2` AGREE — yet their spines DIFFER (the cups fire at different windows), so
`SpineTraceEquiv.refl` FAILS on the pair.  A genuine equal-matching distinct pair at positive mid-width — the input
profile the positive-mid cup determinacy must handle. -/

/-- `G·H·G·H`, the mid-boundary after one cup opens over the two `G·H` survivors. -/
def stringGHGH : ModalityPath adjointTripleGraph AdjointTripleMode.tip AdjointTripleMode.tip :=
  composePath stringGH stringGH

/-- Cup `η'` at window `0` over the two `G·H` survivors (leftContext `id_tip`, rightContext `G·H`). -/
def stringPositiveMidCupAtZeroOverGH :
    SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.tip :=
  ⟨AdjointTripleMode.tip, AdjointTripleMode.tip,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
    stringGH, StringTwoCell.unitUpper, stringGH⟩

/-- Cup `η'` at window `4` over the grown boundary `G·H·G·H` (leftContext `G·H·G·H`, rightContext `id_tip`). -/
def stringPositiveMidCupAtFourOverGHGH :
    SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.tip :=
  ⟨AdjointTripleMode.tip, AdjointTripleMode.tip,
    stringGHGH,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
    stringGH, StringTwoCell.unitUpper,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip⟩

/-- Cup `η'` at window `2` over the two `G·H` survivors (leftContext `G·H`, rightContext `id_tip`). -/
def stringPositiveMidCupAtTwoOverGH :
    SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.tip :=
  ⟨AdjointTripleMode.tip, AdjointTripleMode.tip,
    stringGH,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
    stringGH, StringTwoCell.unitUpper,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip⟩

/-- Cup `η'` at window `0` over the grown boundary `G·H·G·H` (leftContext `id_tip`, rightContext `G·H·G·H`). -/
def stringPositiveMidCupAtZeroOverGHGH :
    SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.tip :=
  ⟨AdjointTripleMode.tip, AdjointTripleMode.tip,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
    stringGH, StringTwoCell.unitUpper, stringGHGH⟩

/-- The disjoint double-cup firing the window-`0` cup first (then the window-`4` cup) — leftContext windows `[0, 4]`. -/
def stringPositiveMidDistinctDoubleCupLeftFirst :
    List (SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.tip) :=
  [stringPositiveMidCupAtZeroOverGH, stringPositiveMidCupAtFourOverGHGH]

/-- The disjoint double-cup firing the window-`2` cup first (then the window-`0` cup) — leftContext windows `[2, 0]`. -/
def stringPositiveMidDistinctDoubleCupRightFirst :
    List (SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.tip) :=
  [stringPositiveMidCupAtTwoOverGH, stringPositiveMidCupAtZeroOverGHGH]

/-- ★ **The two firing orders AGREE on `matchingOfSpineList 2`.**  Both disjoint double-cups add the same two arcs
over the same two survivor strands; the final top boundary's component structure is order-independent, so their
canonical boundary matchings coincide.  Decided at the `DiagramType` level (Nat / `List Nat` fields — a genuine
`DecidableEq`, NOT a spine-level `decide`). -/
theorem stringPositiveMidDistinctDoubleCup_matchingsAgree :
    matchingOfSpineList 2 stringPositiveMidDistinctDoubleCupLeftFirst
      = matchingOfSpineList 2 stringPositiveMidDistinctDoubleCupRightFirst := by
  decide

/-- ★ **The distinctness anchor.**  The two firing orders' spines have DIFFERENT leftContext-length projection lists
(`[0, 4]` window-`0`-first vs `[2, 0]` window-`2`-first), so they are genuinely distinct lists — decidable at the
`List Nat` projection (the r39 technique, sidestepping any spine-level `DecidableEq`).  This certifies the reassembly
fire below relates two genuinely distinct spines: `SpineTraceEquiv.refl` cannot inhabit its conclusion. -/
theorem stringPositiveMidDistinctDoubleCup_leftContextLengthsDiffer :
    stringPositiveMidDistinctDoubleCupLeftFirst.map (fun spineAtom => spineAtom.leftContext.length)
      ≠ stringPositiveMidDistinctDoubleCupRightFirst.map (fun spineAtom => spineAtom.leftContext.length) := by
  decide

/-- ★★ **The block reassembly FIRES on the genuine DISTINCT double-cup pair.**  Instantiating
`stringPositiveMidSameMatchingValleys_spineTraceEquiv` (gated on the ONE brick `positiveMidCup`) on the two firing
orders of the disjoint double-cup over `midWidth = 2` (`G·H` survivors) — as the two CUP blocks, over EMPTY cap
blocks — runs the reassembly end-to-end and produces a `SpineTraceEquiv` of TWO SYNTACTICALLY DISTINCT spines
(leftContext-length projections `[0, 4]` vs `[2, 0]`, `stringPositiveMidDistinctDoubleCup_leftContextLengthsDiffer`)
with EQUAL boundary `matchingOfSpineList 2` (`stringPositiveMidDistinctDoubleCup_matchingsAgree`).  Every chaining /
arity / word hypothesis is `rfl` (`composePath` computes on the closed cons-lists), `0 < 2` and the `matchingOfSpineList
2` agreement by `decide`.  Unlike a diagonal probe (conclusion `SpineTraceEquiv X X`, `refl`-provable), this conclusion
relates DISTINCT spines: `SpineTraceEquiv.refl _` FAILS on it with the type mismatch `SpineTraceEquiv ?m ?m` (both
endpoints equal) vs the goal's distinct `… LeftFirst RightFirst` — so the reassembly is genuinely non-vacuous, NOT
diagonal.  The fire is GATED on the single open brick `positiveMidCup`, since the positive-mid cup sort is not
inhabited this round. -/
theorem stringPositiveMidReassembly_firesOnDistinctDoubleCup
    (positiveMidCup : StringPositiveMidPureCupDeterminacy) :
    SpineTraceEquiv adjointTripleModeSignature
      stringPositiveMidDistinctDoubleCupLeftFirst stringPositiveMidDistinctDoubleCupRightFirst :=
  stringPositiveMidSameMatchingValleys_spineTraceEquiv positiveMidCup
    2 2 (by decide) stringGH stringGH
    [] []
    stringPositiveMidDistinctDoubleCupLeftFirst stringPositiveMidDistinctDoubleCupRightFirst
    AllCapArity.nil AllCapArity.nil
    (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))
    (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))
    (SpineBoundaryChained.nil 2) (SpineBoundaryChained.nil 2)
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (SpineBoundaryWordChained.nil _) (SpineBoundaryWordChained.nil _)
    (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.nil _)))
    (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.nil _)))
    rfl rfl rfl
    stringPositiveMidDistinctDoubleCup_matchingsAgree

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the doubly-positive wall is DECOMPOSED to ONE named cup-sort brick; the colour-blind block
reassembly gated on it is PROVED (FC-3 r40).**  `StringCellValleyTraceEquivPositive` — the last standing sub-producer
after r39 — factors through the SINGLE named brick `StringPositiveMidPureCupDeterminacy` (the positive-mid pure-cup
determinacy, the width-`0` determinacy generalized off the width-`0` bottom boundary to an arbitrary `midWidth` with
`0 < midWidth`).  The colour-blind block reassembly `stringPositiveMidSameMatchingValleys_spineTraceEquiv` — a
near-byte-identical token-swap of the shipped mid-`0` reassembly, changing only the cup boundary width `0 → midWidth`
and the cup producer — is PROVED gated on that ONE brick: the CAP arm fires the shipped unconditional cap sort, the
CUP arm fires the brick, the two combine through the generic append congruence.

  CENSUS (N/K): the doubly-positive wall decomposes into K = 1 named sub-Prop, `StringPositiveMidPureCupDeterminacy`,
  which is OPEN (N_open = 1); the colour-blind block reassembly gated on it is PROVED (N_proved-glue = 1, plus the
  genuine distinct-block fire `stringPositiveMidReassembly_firesOnDistinctDoubleCup` and its two `decide` anchors).
  So this round: 1 named sub-Prop stated + adjudicated, 1 conjunction/glue lemma proved, 0 sub-Props inhabited, 0
  masters flipped.

  What this does NOT flip (honestly): the single remaining brick `StringPositiveMidPureCupDeterminacy` is the
  un-ported length-rigidity wall — TRUE by forcing (same argument as the width-`0` case) but un-inhabited this round
  because its DERIVATION (the r17 LOCATE/drop assembly re-parameterized off `matchingOfSpineList midWidth` with
  survivor-through-strand re-ranking) is a genuine multi-round port.  So the block reassembly stays gated,
  `StringCellValleyTraceEquiv` is not inhabited, and `fxString_hasAdjointTripleCompleteness`
  (`StringMatchingCompleteness`) / `fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) STAY `false`.  This
  round flips ONLY this NEW marker.  `= true`. -/
def fxString_hasPositiveMidCupSortResidual : Bool := true

end FX1Poly.Polygraph
