import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidCupSortResidual
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCupReconstructUngated
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineValleyWidthTelescope
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCapReconstruct
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCupReconstruct
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSurvivorTopTotalMidWidth
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcMatchViewFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLastCupReadoff

/-! # WalkingString/StringPositiveMidValleyProducer — the POSITIVE-mid whole-valley `SpineTraceEquiv` producer:
the append-split assembled from a single whole-boundary matching equality, gated on the ONE cup-sort brick
(FC-3 r41, the positive-mid producer's block-level headline)

## What is already SHIPPED (not re-proved here)

The append-split at POSITIVE mid-width is DONE.  The two total restriction functions `capRestrict` / `cupRestrict`
(`ValleyCapRestrict` / `ValleyCupRestrict`, WalkingAdjunction) read the WHOLE valley's `DiagramType` and recover the
per-block matchings ON THE NOSE — the through-strand seam re-ranking (`survivorTopRank` / `nthSurvivorTop`) is
ABSORBED into those functions, so no up-to-permutation adjustment is ever needed at the diagram level.  The two
halves of the split are the shipped equational splitters:

  * `stringSameWholeMatching_capBlockMatchingEq` (`StringValleyCapReconstruct`, r32) — MID-WIDTH-FREE (needs only
    `0 < bottomCount`): `matchingOf bc capBlockFirst = matchingOf bc capBlockSecond`, by `congrArg capRestrict`
    over the whole equality sandwiched between two `stringCapRestrict_reconstructs`;
  * `stringSameWholeMatching_cupBlockMatchingEq` (`StringValleyCupReconstruct`, r33) — UNCONDITIONAL (a pure
    `congrArg cupRestrict` between two cup reconstructions): `matchingOf midWidth cupBlockFirst = matchingOf
    midWidth cupBlockSecond`, each read at its own mid-width.  At POSITIVE mid-width the reconstruction inputs are
    supplied by `stringCupRestrict_reconstructs_unconditional` (`StringValleyCupReconstructUngated`, r34, needing
    only `0 < midWidth`).

The mid-width telescopes are mid-generic too: `stringSurvivorTopTotal_eq_midWidth` (survivorTopTotal(whole) =
mid-width, no mid-`0` gate) and `stringCapLength_eq_of_midWidth_eq` (cap length from equal mid-widths).  So the
append-split covers ALL mid-widths — it is not a round of its own; this file merely ASSEMBLES it.

## What this file ships — the positive-mid whole-valley producer (the assembly)

`stringPositiveMidValleysWithEqualMatching_spineTraceEquiv` — a near-byte-identical token-swap of the shipped
mid-`0` producer `stringMidZeroValleysWithEqualMatching_spineTraceEquiv` (`StringMidZeroValleyProducer`, r36).
Two valleys `capBlock ++ cupBlock` (pure cap, pure cup, boundary-chained, POSITIVE bottom count, POSITIVE mid-width
`0 < survivorTopTotal (matchingOf bc (capBlock ++ cupBlock))`) with EQUAL whole-boundary `matchingOf` are
`SpineTraceEquiv`, GATED on the ONE open brick `StringPositiveMidPureCupDeterminacy` (the positive-mid cup sort,
r40).  From the single whole-boundary equality it DERIVES the four per-block facts the r40 block reassembly consumes:

  * the mid-widths are POSITIVE and EQUAL (`stringSurvivorTopTotal_eq_midWidth` + `wholeEq`) — replacing r36's
    both-widths-are-`0` derivation;
  * the cap length agreement (`stringCapLength_eq_of_midWidth_eq`) — identical to r36;
  * the cap `diagram` agreement (`stringSameWholeMatching_capBlockMatchingEq` → `arcDiagram_eq_matching`) —
    identical to r36;
  * the cup `matchingOf` agreement at the (positive) mid-width — the ONLY swaps from r36 are the cup reconstruction
    (`stringMidZeroCupBlockReconstruct_holds` → `stringCupRestrict_reconstructs_unconditional`, fed the positive
    mid-width witness) and the alignment of the second cup width to the first via `midEq` (rather than collapsing
    both to `0`).

Then the r40 block reassembly `stringPositiveMidSameMatchingValleys_spineTraceEquiv` closes.  The ONLY deltas from
r36 are: mid-width `0 → midWidth` (a runtime open-wire count, not the constant `0`), the `0 < midWidth` witness,
the unconditional cup reconstruction, and the width alignment through `midEq`.

## FRAMING (exactly what this gives — no K=1 claim)

This producer is an ASSEMBLY gated on the single open brick `StringPositiveMidPureCupDeterminacy`; it is NOT a
decomposition of that wall.  It takes the shipped positive-covering append-split and the r40 block reassembly and
turns a single whole-boundary matching equality (plus the honest valley-shape inputs) into a `SpineTraceEquiv`
producer — leaving the cup-sort brick exactly as open as r40 left it.  The reassembly gated on a hypothesis is not
a decomposition of the wall.

### The honest THREE-LAYER CENSUS (positive-mid pipeline)

  * **L1 (r40, `StringPositiveMidCupSortResidual`)** — the colour-blind BLOCK reassembly
    `stringPositiveMidSameMatchingValleys_spineTraceEquiv`: given the four PRE-SPLIT per-block facts (cap length,
    cap diagram, cup `matchingOf` at positive mid-width, cup top-word), plus arities / chains / words, it produces
    the `SpineTraceEquiv`, gated on the ONE brick.  SHIPPED last round.
  * **L2 (THIS round, r41, this file)** — the whole-valley PRODUCER
    `stringPositiveMidValleysWithEqualMatching_spineTraceEquiv`: DERIVES those four facts from a SINGLE
    whole-boundary matching equality via the shipped (positive-covering) append-split + telescopes, then feeds L1.
    Still gated on the ONE brick.  The append-split itself was already shipped (r32–r34); this round assembles it
    into the whole-valley producer.  Non-vacuity: the distinct-double-cup fire
    `stringPositiveMidProducer_firesOnDistinctDoubleCup` relates two syntactically DISTINCT spines (leftContext
    projections `[0, 4] ≠ [2, 0]`) with equal whole `matchingOfSpineList 2` — `SpineTraceEquiv.refl` FAILS on it.
  * **L3 (the r42 bill, NOT done this round)** — the positive CELL reducer inhabiting
    `StringCellValleyTraceEquivPositive` (`StringValleyDegenerateSplit`): must additionally DERIVE the boundary
    words from a `RawTwoCellExpr` valley (peel `capWord := sourcePath`, exhibit a SHARED `midWord` for two
    parallel cap blocks at POSITIVE mid-width — the positive analog of the r37 `stringSharedMidWord_ofMidZero`,
    whose length-`0` path-uniqueness route does NOT generalize), then invoke this producer.  That word-rigidity
    brick + the cell reducer are the r42 bill.

## The literature ceiling, honored

The diagram monoids (Brauer / partition) are non-cancellative: whole-boundary agreement forces the factors only
UP TO the middle permutation once a cap++cup valley admits a closed loop.  The string lane sidesteps that ceiling
by the canonical-seam-labeling route (synthesis option (a)): `capRestrict` / `cupRestrict` fix a canonical linear
order on the mid-boundary and absorb the survivor re-ranking, so the block equalities are literal `DiagramType`
equalities, NOT up-to-permutation classes.  A truth-probe on the wide valley `[ε] ++ [η']` (bottomCount `4`,
mid-width `2`) machine-confirmed both directions: `matchingOf 4 [ε] = capRestrict (matchingOf 4 ([ε] ++ [η']))`
and `matchingOf 2 [η'] = cupRestrict (matchingOf 4 ([ε] ++ [η']))` decide `true` — on the nose, seam absorbed.
The residual hardness (recovering the SPINE from the matching — the SORT) lives entirely in the ONE open brick.

Raw Lean 4 + Init; pure block assembly over the shipped cap/cup splitters, the mid-width telescopes, the
unconditional cup reconstruction, and the r40 word-threaded block reassembly, no `omega` / `simp`-AC /
`WellFounded.fix`.  The distinct-block fire's `matchingOfSpineList 2` reductions are heavy, so this file raises
`maxHeartbeats` (`by decide` under the raised budget — `native_decide` is banned).
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace FX1Poly.Polygraph

/-! ## L2 — the positive-mid whole-valley producer (the append-split assembled), gated on the ONE cup-sort brick -/

/-- ★★ **The positive-mid whole-valley string `SpineTraceEquiv` producer, gated on the ONE cup-sort brick.**  Two
valleys `capBlock ++ cupBlock` (pure-cap prefix, pure-cup suffix, boundary-chained, POSITIVE bottom count, POSITIVE
mid-width) with EQUAL whole-boundary `matchingOf` are `SpineTraceEquiv`, gated on
`StringPositiveMidPureCupDeterminacy`.

The positive-mid mirror of `stringMidZeroValleysWithEqualMatching_spineTraceEquiv` (`StringMidZeroValleyProducer`,
r36).  The two string sorts are word-threaded (the r17 precedent): the caller supplies the shared cap boundary word
`capWord`, the shared mid boundary word `midWord`, and the shared cup `spineListTopWord` (`cupTopWordEq`).  From the
single whole-boundary matching equality it derives, internally:

  * both mid-widths are POSITIVE (`stringSurvivorTopTotal_eq_midWidth` + the `midPositive` witness) and EQUAL
    (`midEq`, via `wholeEq`);
  * the cap prefixes are boundary-chained (`spineBoundaryChained_prefix_ofAppend`); the cap lengths agree
    (`stringCapLength_eq_of_midWidth_eq`); the cap blocks agree (`stringSameWholeMatching_capBlockMatchingEq`) →
    the cap `diagram` agreement (`arcDiagram_eq_matching` at the positive cap width);
  * the cup blocks agree at the (positive) mid-widths — the unconditional cup reconstruction
    `stringCupRestrict_reconstructs_unconditional` (r34, fed the positive mid-width witness) through
    `stringSameWholeMatching_cupBlockMatchingEq`, then the second cup width aligned to the first via `midEq`.

Then the r40 block reassembly `stringPositiveMidSameMatchingValleys_spineTraceEquiv` closes.  The ONLY deltas from
r36 are the mid-width `0 → midWidth`, the `0 < midWidth` witness, the unconditional cup reconstruction, and the
`midEq` width alignment. -/
theorem stringPositiveMidValleysWithEqualMatching_spineTraceEquiv
    (positiveMidCup : StringPositiveMidPureCupDeterminacy)
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount : Nat) (bottomPositive : 0 < bottomCount)
    (capWord midWord : ModalityPath adjointTripleGraph overallSource overallTarget)
    (capBlockFirst capBlockSecond cupBlockFirst cupBlockSecond :
      List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (capPureFirst : AllCapArity capBlockFirst) (capPureSecond : AllCapArity capBlockSecond)
    (cupPureFirst : AllCupArity cupBlockFirst) (cupPureSecond : AllCupArity cupBlockSecond)
    (cupChainedFirst : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockFirst)
    (cupChainedSecond : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length cupBlockSecond)
    (wholeChainedFirst : SpineBoundaryChained bottomCount (capBlockFirst ++ cupBlockFirst))
    (wholeChainedSecond : SpineBoundaryChained bottomCount (capBlockSecond ++ cupBlockSecond))
    (capWordChainedFirst : SpineBoundaryWordChained capWord capBlockFirst)
    (capWordChainedSecond : SpineBoundaryWordChained capWord capBlockSecond)
    (cupWordChainedFirst : SpineBoundaryWordChained midWord cupBlockFirst)
    (cupWordChainedSecond : SpineBoundaryWordChained midWord cupBlockSecond)
    (cupTopWordEq : spineListTopWord midWord cupBlockFirst
      = spineListTopWord midWord cupBlockSecond)
    (midPositive : 0 < survivorTopTotal (matchingOfSpineList bottomCount (capBlockFirst ++ cupBlockFirst)))
    (wholeEq : matchingOfSpineList bottomCount (capBlockFirst ++ cupBlockFirst)
      = matchingOfSpineList bottomCount (capBlockSecond ++ cupBlockSecond)) :
    SpineTraceEquiv adjointTripleModeSignature
      (capBlockFirst ++ cupBlockFirst) (capBlockSecond ++ cupBlockSecond) := by
  -- The two mid-widths equal their whole-valley survivor totals.
  have survFirst :
      survivorTopTotal (matchingOfSpineList bottomCount (capBlockFirst ++ cupBlockFirst))
        = (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length :=
    stringSurvivorTopTotal_eq_midWidth bottomCount bottomPositive capBlockFirst cupBlockFirst
      capPureFirst cupPureFirst cupChainedFirst
  have survSecond :
      survivorTopTotal (matchingOfSpineList bottomCount (capBlockSecond ++ cupBlockSecond))
        = (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length :=
    stringSurvivorTopTotal_eq_midWidth bottomCount bottomPositive capBlockSecond cupBlockSecond
      capPureSecond cupPureSecond cupChainedSecond
  -- Both mid-widths are POSITIVE.
  have midPositiveFirst :
      0 < (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length := by
    rw [← survFirst]; exact midPositive
  have midPositiveSecond :
      0 < (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length := by
    rw [← survSecond, ← wholeEq]; exact midPositive
  -- The two mid-widths are EQUAL (via the whole-matching equality).
  have midEq :
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length
        = (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length := by
    rw [← survFirst, ← survSecond, wholeEq]
  -- The two cap prefixes are boundary-chained (restriction of the whole valley chaining).
  have capChainedFirst : SpineBoundaryChained bottomCount capBlockFirst :=
    spineBoundaryChained_prefix_ofAppend capBlockFirst cupBlockFirst bottomCount wholeChainedFirst
  have capChainedSecond : SpineBoundaryChained bottomCount capBlockSecond :=
    spineBoundaryChained_prefix_ofAppend capBlockSecond cupBlockSecond bottomCount wholeChainedSecond
  -- The cap length agreement from the (equal) mid-widths.
  have capLengthEq : capBlockFirst.length = capBlockSecond.length :=
    stringCapLength_eq_of_midWidth_eq bottomCount capBlockFirst capBlockSecond capPureFirst capPureSecond
      capChainedFirst capChainedSecond midEq
  -- The cap-block matchings agree (shipped cap half, needs only the positive bottom count).
  have capMatchEq : matchingOfSpineList bottomCount capBlockFirst
      = matchingOfSpineList bottomCount capBlockSecond :=
    stringSameWholeMatching_capBlockMatchingEq bottomCount bottomPositive capBlockFirst capBlockSecond
      cupBlockFirst cupBlockSecond capPureFirst capPureSecond cupPureFirst cupPureSecond
      cupChainedFirst cupChainedSecond wholeChainedFirst wholeChainedSecond wholeEq
  -- The cap `diagram` agreement (positive cap-width `arcDiagram_eq_matching`).
  have capDiagramAgree : (arcStructureOfSpineList bottomCount capBlockFirst).diagram
      = (arcStructureOfSpineList bottomCount capBlockSecond).diagram := by
    rw [arcDiagram_eq_matching bottomCount capBlockFirst
        (stringSpineHasCupCapAtoms_ofAllCapArity capBlockFirst capPureFirst) capChainedFirst bottomPositive,
      arcDiagram_eq_matching bottomCount capBlockSecond
        (stringSpineHasCupCapAtoms_ofAllCapArity capBlockSecond capPureSecond) capChainedSecond bottomPositive,
      capMatchEq]
  -- The two POSITIVE-mid cup reconstructions (the r34 UNCONDITIONAL reconstruct, fed the positive mid-width).
  have reconFirst := stringCupRestrict_reconstructs_unconditional bottomCount bottomPositive
    capBlockFirst cupBlockFirst capPureFirst cupPureFirst cupChainedFirst wholeChainedFirst midPositiveFirst
  have reconSecond := stringCupRestrict_reconstructs_unconditional bottomCount bottomPositive
    capBlockSecond cupBlockSecond capPureSecond cupPureSecond cupChainedSecond wholeChainedSecond midPositiveSecond
  -- The cup-block matchings agree, each at its own mid-width.
  have cupMatchEqRaw :
      matchingOfSpineList
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockFirst
        = matchingOfSpineList
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length cupBlockSecond :=
    stringSameWholeMatching_cupBlockMatchingEq bottomCount capBlockFirst capBlockSecond cupBlockFirst cupBlockSecond
      reconFirst reconSecond wholeEq
  -- Align the second cup width to the first (via `midEq`), and transport the second cup chain likewise.
  have cupMatchEq :
      matchingOfSpineList
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockFirst
        = matchingOfSpineList
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockSecond := by
    have raw := cupMatchEqRaw
    rw [← midEq] at raw
    exact raw
  have cupChainedSecondAtFirst :
      SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockSecond := by
    rw [midEq]; exact cupChainedSecond
  exact stringPositiveMidSameMatchingValleys_spineTraceEquiv positiveMidCup
    bottomCount (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length
    midPositiveFirst capWord midWord
    capBlockFirst capBlockSecond cupBlockFirst cupBlockSecond
    capPureFirst capPureSecond cupPureFirst cupPureSecond
    capChainedFirst capChainedSecond cupChainedFirst cupChainedSecondAtFirst
    capWordChainedFirst capWordChainedSecond cupWordChainedFirst cupWordChainedSecond
    cupTopWordEq capLengthEq capDiagramAgree cupMatchEq

/-! ## The distinct-block evidence — the producer FIRES on the genuine distinct double-cup at positive mid-width -/

/-- ★★ **The whole-valley producer FIRES on the genuine DISTINCT double-cup pair.**  Instantiating
`stringPositiveMidValleysWithEqualMatching_spineTraceEquiv` (gated on the ONE brick `positiveMidCup`) on the two
firing orders of the disjoint double-cup over `midWidth = 2` (`G·H` survivors, `StringPositiveMidCupSortResidual`)
— as the two CUP blocks, over EMPTY cap blocks (`bottomCount = 2`) — runs the WHOLE producer end-to-end from a
SINGLE whole-boundary matching equality: the survivor telescope pins both mid-widths to the positive `2`, the cap
splitter (vacuous over the empty cap) and the unconditional cup reconstruction supply the per-block agreements, and
the r40 block reassembly fires the cup arm through the brick.  The conclusion relates two SYNTACTICALLY DISTINCT
spines (leftContext-length projections `[0, 4] ≠ [2, 0]`,
`stringPositiveMidDistinctDoubleCup_leftContextLengthsDiffer`) with EQUAL whole `matchingOfSpineList 2`
(`stringPositiveMidDistinctDoubleCup_matchingsAgree`).  `0 < 2` and `0 < survivorTopTotal (matchingOfSpineList 2 …)`
by `decide` under the raised budget; every chaining / arity / word hypothesis is `rfl` (`composePath` computes on
the closed cons-lists).  Unlike a diagonal probe (`SpineTraceEquiv X X`, `refl`-provable), this conclusion relates
DISTINCT spines: `SpineTraceEquiv.refl _` FAILS on it — the producer is genuinely non-vacuous, NOT diagonal.  The
fire is GATED on the single open brick `positiveMidCup`. -/
theorem stringPositiveMidProducer_firesOnDistinctDoubleCup
    (positiveMidCup : StringPositiveMidPureCupDeterminacy) :
    SpineTraceEquiv adjointTripleModeSignature
      stringPositiveMidDistinctDoubleCupLeftFirst stringPositiveMidDistinctDoubleCupRightFirst :=
  stringPositiveMidValleysWithEqualMatching_spineTraceEquiv positiveMidCup
    2 (by decide) stringGH stringGH
    [] []
    stringPositiveMidDistinctDoubleCupLeftFirst stringPositiveMidDistinctDoubleCupRightFirst
    AllCapArity.nil AllCapArity.nil
    (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))
    (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (SpineBoundaryWordChained.nil _) (SpineBoundaryWordChained.nil _)
    (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.nil _)))
    (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.nil _)))
    rfl (by decide)
    stringPositiveMidDistinctDoubleCup_matchingsAgree

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the positive-mid whole-valley producer is ASSEMBLED, gated on the ONE cup-sort brick (FC-3
r41).**  `stringPositiveMidValleysWithEqualMatching_spineTraceEquiv` — the positive-mid mirror of the r36 mid-`0`
producer — takes a SINGLE whole-boundary matching equality at POSITIVE mid-width and derives the four per-block
facts the r40 block reassembly consumes (cap length, cap diagram, cup `matchingOf` at the positive mid-width, cup
top-word), then feeds `stringPositiveMidSameMatchingValleys_spineTraceEquiv`.  The append-split it uses was already
SHIPPED and positive-covering (r32–r34: `stringSameWholeMatching_capBlockMatchingEq` /
`stringSameWholeMatching_cupBlockMatchingEq` / `stringCupRestrict_reconstructs_unconditional`, with the seam
re-ranking absorbed on-the-nose into `capRestrict` / `cupRestrict`); this round ASSEMBLES it into the whole-valley
producer.  The distinct-double-cup fire `stringPositiveMidProducer_firesOnDistinctDoubleCup` runs it end-to-end on
two syntactically DISTINCT spines (`[0, 4] ≠ [2, 0]`) with equal whole `matchingOfSpineList 2`, so it is genuinely
non-vacuous, not diagonal.

  THREE-LAYER CENSUS (the positive-mid pipeline): L1 = the r40 BLOCK reassembly (four pre-split facts → trace,
  gated on the brick, SHIPPED); L2 = THIS round's whole-valley PRODUCER (one whole-matching equality → the four
  facts → L1, gated on the brick); L3 = the positive CELL reducer inhabiting `StringCellValleyTraceEquivPositive`
  (needs, additionally, the boundary-word derivation over a `RawTwoCellExpr` valley — the positive shared-`midWord`
  word-rigidity brick, whose r37 length-`0` route does NOT generalize — plus this producer) = the r42 bill, NOT
  done this round.

  What this does NOT flip (honestly): this is an ASSEMBLY gated on the single open brick
  `StringPositiveMidPureCupDeterminacy`, NOT a decomposition of that wall.  The brick stays open; the producer
  stays gated on it; `StringCellValleyTraceEquivPositive` is not inhabited; and the completeness masters
  `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) and `fxString_hasConvOfMapEqPortFlip`
  (`StringConvOfMapEqPort`) STAY `false`.  No K = 1 claim is made without the brick→wall sort theorem.  This round
  flips ONLY this NEW marker: the positive-mid whole-valley producer is assembled at the block level.  `= true`. -/
def fxString_hasPositiveMidValleyProducer : Bool := true

end FX1Poly.Polygraph
