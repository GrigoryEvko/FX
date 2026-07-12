import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidValleyProducer
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMidZeroValleyCellReducer
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringOneSubProducerBeam
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSurvivorTopTotalMidWidth
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineValleyWidthTelescope
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCapReconstruct
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapInternalCountsPointwise
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPureCapArcReconstruct
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCapHeadExtractionWordPinInhabited
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineTopWordSwapInvariant
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcMatchViewFold
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwapGeneration

/-! # WalkingString/StringPositiveMidValleyCellReducer — the POSITIVE-mid cell-level reducer that INHABITS
`StringCellValleyTraceEquivPositive` GATED ON THE ONE cup-sort brick (FC-3 r42, the L3 layer)

`StringValleyDegenerateSplit` sharpened the monolithic Piece-II residual into three colour-keyed sub-producers.  The
r38 cell reducer `stringMidZeroValleyTraceEquiv_holds` (`StringMidZeroValleyCellReducer`) discharged one of them
(`StringMidZeroValleyTraceEquiv`) hypothesis-free; the r39 beam `StringOneSubProducerBeam` wired the shipped r17
width-`0` proof, collapsing the whole #2020 decision to fire from a SINGLE remaining colour-keyed sub-producer,
`StringCellValleyTraceEquivPositive` (the DOUBLY-positive valley trace-equivalence).  The r40 decomposition
(`StringPositiveMidCupSortResidual`) and r41 producer (`StringPositiveMidValleyProducer`) factored that sub-producer's
BLOCK-level content through the single named cup-sort brick `StringPositiveMidPureCupDeterminacy`.  This file lands the
CELL-level reducer: it inhabits `StringCellValleyTraceEquivPositive`, GATED on that one brick — the last connective
link.  With the brick inhabited, `StringCellValleyTraceEquivPositive` becomes unconditional and the whole #2020
completeness+decision headline follows (the brick→master implications are recorded here as theorems).

## What this ships (each zero-axiom, machine-checked, gated on the ONE open brick)

  * ★★ `stringPositiveMidValleyTraceEquiv_holds` — the positive-mid CELL reducer.  A near-byte-identical additive
    mirror of the r38 mid-`0` reducer `stringMidZeroValleyTraceEquiv_holds`: block-split both whole `RawTwoCellExpr`
    valleys, derive the boundary-length chains (whole from `RawTwoCellExpr.spineBoundaryChained_spine`, cap prefix by
    the shipped prefix restriction, cup suffix at the mid-width by the r38 Brick A
    `stringSpineBoundaryChained_cupSuffix_ofCapPrefix`), derive the boundary-word chains (`capWord := sourcePath` via
    W3, `midWord := spineListTopWord sourcePath capA` via the r38 Brick B
    `spineBoundaryWordChained_cupSuffix_ofCapPrefix`), then feed the r41 whole-valley producer
    `stringPositiveMidValleysWithEqualMatching_spineTraceEquiv` (gated on the brick).  Exactly THREE deltas from the
    r38 reducer: (δ1) conclusion / intro binds `midPos : 0 < survivorTopTotal` in place of `midZeroA`; (δ2) the mid
    witness `midPositive` in place of `midZeroFirst`; (δ3) the shared `midWord`.
  * ★ **δ3 — the shared `midWord` via the CAP-TRACE route** (the ONLY substantive delta).  The r38 reducer got the
    shared cap top word from the mid-`0`-only brick `stringSharedMidWord_ofMidZero` (its length-`0` path-uniqueness
    route does NOT generalize).  This file gets it a DIFFERENT, mid-generic way: `spineListTopWord` is INVARIANT under
    the UNCONDITIONAL cap sort, so from the (positivity-free) cap-trace `SpineTraceEquiv capA capB` — reconstructed by
    the shipped cap-side kit (`stringSameWholeMatching_capBlockMatchingEq` → `arcDiagram_eq_matching` →
    `stringPureCapSpines_internalCapCountsAgree_ofDiagram` → `stringPureCapTailsCancel_ofDiagramAndInternalCap` →
    `stringPureCapSpine_sort_unconditional`) — the top-word invariance `spineListTopWord_atomicTraceEquiv`
    (through `spineTraceEquiv_iff_atomicTraceEquiv`) yields `spineListTopWord sourcePath capA = spineListTopWord
    sourcePath capB` at ANY mid-width.  This route is BRICK-FREE (the cap sort is unconditional, reads no cup data):
    the r42 recon correction to the r41 census, which conflated "the r37 route fails" with "the fact is hard" — only
    the CUP-side sort (the brick) is genuinely hard.
  * ★ `stringMatchingReductsShareSpineTrace_ofBrick` / `stringConvOfMapEq_ofBrick` /
    `decidableStringSaturatedConv_ofBrick` — the BRICK→MASTER implications.  Composing the cell reducer with the r39
    one-sub-producer beam, the ENTIRE #2020 residual now gates on the SINGLE brick
    `StringPositiveMidPureCupDeterminacy` (down from the sub-producer `StringCellValleyTraceEquivPositive`): the
    completeness reduct-existence residual, the base completeness, and the full word-problem DECISION all become
    deliverable the moment the brick is inhabited.  These record — as theorems — that T1 proves the last connective
    tissue: the whole headline reduces to exactly ONE cup-sort brick.

## The honest THREE-LAYER CENSUS (positive-mid pipeline)

  * **L1 (r40, `StringPositiveMidCupSortResidual`)** — the colour-blind BLOCK reassembly
    `stringPositiveMidSameMatchingValleys_spineTraceEquiv`, gated on the ONE brick.  SHIPPED.
  * **L2 (r41, `StringPositiveMidValleyProducer`)** — the whole-valley PRODUCER
    `stringPositiveMidValleysWithEqualMatching_spineTraceEquiv`: a single whole-boundary matching equality → the four
    per-block facts → L1.  Still gated on the ONE brick.  SHIPPED.
  * **L3 (THIS round, r42, this file)** — the positive CELL reducer
    `stringPositiveMidValleyTraceEquiv_holds` inhabiting `StringCellValleyTraceEquivPositive`: derives the boundary
    words from a `RawTwoCellExpr` valley (cap word via W3, shared `midWord` via the cap-trace route, cup words via
    Brick B), then feeds L2.  Still gated on the ONE brick — plus the brick→master implications.

## No master flip (honest)

This round does NOT inhabit the brick `StringPositiveMidPureCupDeterminacy` (the positive-mid CUP sort — the r17
LOCATE/drop assembly re-parameterized off `matchingOfSpineList midWidth` with survivor-through-strand re-ranking, a
genuine multi-round port; cited: Ridout–Saint-Aubin arXiv:1204.4505 Jones normal form / Riehl–Verity arXiv:1310.8279
strictly-undulating width-induction / Delpeuch–Vicary arXiv:1804.07832 right-normal handedness — all three uniformly
"peel the extremal cup with matched-pair cancellation").  So `StringCellValleyTraceEquivPositive` stays gated,
`StringCellValleyTraceEquiv` is not inhabited, and the completeness masters `fxString_hasAdjointTripleCompleteness`
(`StringMatchingCompleteness`) and `fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) STAY `false`.  This
round flips ONLY the NEW marker below: the positive-mid CELL reducer is assembled and the whole residual is collapsed
to the single brick.

Raw Lean 4 + Init; the reducer is pure block-split + word-derivation over the shipped r41 producer, the r38 bricks,
the shipped cap-side reconstruction kit, and the top-word invariance; no `omega` / `simp`-AC / `WellFounded.fix`.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace FX1Poly.Polygraph

/-! ## Local propext-free `List.range` length (per-file copy; the core `List.length_range` leaks propext, and the
r38 reducer's copy is `private`) -/

/-- The `List.range` accumulator length, structural and propext-free.  Per-file copy with a distinct name from the
r38 mid-`0` reducer's `private` twin so the umbrella build's global table stays duplicate-free. -/
private theorem stringPositiveMidReducerRangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := stringPositiveMidReducerRangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

/-- `(List.range count).length = count`, propext-free (per-file copy; the core lemma leaks). -/
private theorem stringPositiveMidReducerRangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [stringPositiveMidReducerRangeLoopLength count []]
  exact Nat.add_zero count

/-! ## The positive-mid cell-level reducer — `StringCellValleyTraceEquivPositive` inhabited, gated on the ONE brick -/

/-- ★★ **The doubly-positive valley determinacy sub-producer, INHABITED gated on the ONE cup-sort brick.**
`StringCellValleyTraceEquivPositive` holds given `brick : StringPositiveMidPureCupDeterminacy`: two whole VALLEY
string cells with equal boundary `matchingOf`, POSITIVE source width, and POSITIVE mid-width are `SpineTraceEquiv`.

Block-split both valleys (`stringSpineValley_blockSplit`); derive the length chains (whole from
`RawTwoCellExpr.spineBoundaryChained_spine`, cap prefix by `spineBoundaryChained_prefix_ofAppend`, cup suffix at the
mid-width by the r38 Brick A); derive the word chains (`capWord := sourcePath` via W3
`spineBoundaryWordChained_prefix_ofAppend`, `midWord := spineListTopWord sourcePath capA` via the r38 Brick B); derive
the shared `midWord` (δ3) via the BRICK-FREE cap-trace route (`spineListTopWord_atomicTraceEquiv` on the unconditional
cap sort); derive the shared cup top word by the top-word append law folded against both
`RawTwoCellExpr.spineListTopWord_spine`; then fire the r41 producer
`stringPositiveMidValleysWithEqualMatching_spineTraceEquiv` (gated on `brick`).  The positive-mid mirror of the r38
`stringMidZeroValleyTraceEquiv_holds`, word-threaded — exactly three deltas (δ1 mid witness type, δ2 mid witness, δ3
shared `midWord` route). -/
theorem stringPositiveMidValleyTraceEquiv_holds
    (brick : StringPositiveMidPureCupDeterminacy) : StringCellValleyTraceEquivPositive := by
  intro sourceMode targetMode sourcePath targetPath valleyA valleyB isValleyA isValleyB
    matchingEq sourcePos midPos
  -- Block-split both valley spines into cap-prefix ++ cup-suffix.
  obtain ⟨capA, cupA, splitA, capPureA, cupPureA⟩ := stringSpineValley_blockSplit valleyA.spine isValleyA
  obtain ⟨capB, cupB, splitB, capPureB, cupPureB⟩ := stringSpineValley_blockSplit valleyB.spine isValleyB
  -- The two whole valleys are boundary-chained at the source width.
  have wholeChainedA : SpineBoundaryChained sourcePath.length (capA ++ cupA) := by
    rw [← splitA]; exact valleyA.spineBoundaryChained_spine
  have wholeChainedB : SpineBoundaryChained sourcePath.length (capB ++ cupB) := by
    rw [← splitB]; exact valleyB.spineBoundaryChained_spine
  -- The cup suffixes are boundary-chained at the mid-width (restrict the whole chain over the cap prefix, Brick A).
  have seedWholeA : SpineBoundaryChained
      (⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ : WireState).openWires.length (capA ++ cupA) := by
    show SpineBoundaryChained (List.range sourcePath.length).length (capA ++ cupA)
    rw [stringPositiveMidReducerRangeLength]; exact wholeChainedA
  have seedWholeB : SpineBoundaryChained
      (⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ : WireState).openWires.length (capB ++ cupB) := by
    show SpineBoundaryChained (List.range sourcePath.length).length (capB ++ cupB)
    rw [stringPositiveMidReducerRangeLength]; exact wholeChainedB
  have cupChainedA : SpineBoundaryChained
      (processSpine ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ capA).openWires.length cupA :=
    stringSpineBoundaryChained_cupSuffix_ofCapPrefix capA capPureA cupA
      ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ seedWholeA
  have cupChainedB : SpineBoundaryChained
      (processSpine ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ capB).openWires.length cupB :=
    stringSpineBoundaryChained_cupSuffix_ofCapPrefix capB capPureB cupB
      ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ seedWholeB
  -- The cap prefixes are boundary-chained at the source width (prefix restriction).
  have capChainedA : SpineBoundaryChained sourcePath.length capA :=
    spineBoundaryChained_prefix_ofAppend capA cupA sourcePath.length wholeChainedA
  have capChainedB : SpineBoundaryChained sourcePath.length capB :=
    spineBoundaryChained_prefix_ofAppend capB cupB sourcePath.length wholeChainedB
  -- The whole valleys are boundary-WORD-chained from the source word.
  have wholeWordA : SpineBoundaryWordChained sourcePath (capA ++ cupA) := by
    rw [← splitA]; exact valleyA.spineBoundaryWordChained_spine
  have wholeWordB : SpineBoundaryWordChained sourcePath (capB ++ cupB) := by
    rw [← splitB]; exact valleyB.spineBoundaryWordChained_spine
  -- The cap word chains (W3 peel) and cup word chains (Brick B drop).
  have capWordA : SpineBoundaryWordChained sourcePath capA :=
    spineBoundaryWordChained_prefix_ofAppend sourcePath capA cupA wholeWordA
  have capWordB : SpineBoundaryWordChained sourcePath capB :=
    spineBoundaryWordChained_prefix_ofAppend sourcePath capB cupB wholeWordB
  have cupWordA : SpineBoundaryWordChained (spineListTopWord sourcePath capA) cupA :=
    spineBoundaryWordChained_cupSuffix_ofCapPrefix sourcePath capA cupA wholeWordA
  have cupWordBraw : SpineBoundaryWordChained (spineListTopWord sourcePath capB) cupB :=
    spineBoundaryWordChained_cupSuffix_ofCapPrefix sourcePath capB cupB wholeWordB
  -- Re-read the matching hypothesis at the spine level.
  have wholeEqA : matchingOf valleyA = matchingOfSpineList sourcePath.length (capA ++ cupA) := by
    show matchingOfSpineList sourcePath.length valleyA.spine
      = matchingOfSpineList sourcePath.length (capA ++ cupA)
    rw [splitA]
  have wholeEqB : matchingOf valleyB = matchingOfSpineList sourcePath.length (capB ++ cupB) := by
    show matchingOfSpineList sourcePath.length valleyB.spine
      = matchingOfSpineList sourcePath.length (capB ++ cupB)
    rw [splitB]
  have wholeEq : matchingOfSpineList sourcePath.length (capA ++ cupA)
      = matchingOfSpineList sourcePath.length (capB ++ cupB) :=
    wholeEqA.symm.trans (matchingEq.trans wholeEqB)
  -- δ2: the mid-POSITIVE witness at the spine level (in place of the r38 mid-`0` witness).
  have midPositive : 0 < survivorTopTotal (matchingOfSpineList sourcePath.length (capA ++ cupA)) := by
    rw [← wholeEqA]; exact midPos
  -- δ3: the shared `midWord` via the BRICK-FREE CAP-TRACE route (mid-generic; the r38 length-`0` route does not
  -- generalize, but the top word is invariant under the unconditional cap sort at any mid-width).
  have survFirst : survivorTopTotal (matchingOfSpineList sourcePath.length (capA ++ cupA))
      = (processSpine ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ capA).openWires.length :=
    stringSurvivorTopTotal_eq_midWidth sourcePath.length sourcePos capA cupA capPureA cupPureA cupChainedA
  have survSecond : survivorTopTotal (matchingOfSpineList sourcePath.length (capB ++ cupB))
      = (processSpine ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ capB).openWires.length :=
    stringSurvivorTopTotal_eq_midWidth sourcePath.length sourcePos capB cupB capPureB cupPureB cupChainedB
  have midEq : (processSpine ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ capA).openWires.length
      = (processSpine ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ capB).openWires.length := by
    rw [← survFirst, ← survSecond, wholeEq]
  have capLengthEq : capA.length = capB.length :=
    stringCapLength_eq_of_midWidth_eq sourcePath.length capA capB capPureA capPureB
      capChainedA capChainedB midEq
  have capMatchEq : matchingOfSpineList sourcePath.length capA = matchingOfSpineList sourcePath.length capB :=
    stringSameWholeMatching_capBlockMatchingEq sourcePath.length sourcePos capA capB
      cupA cupB capPureA capPureB cupPureA cupPureB
      cupChainedA cupChainedB wholeChainedA wholeChainedB wholeEq
  have capDiagramAgree : (arcStructureOfSpineList sourcePath.length capA).diagram
      = (arcStructureOfSpineList sourcePath.length capB).diagram := by
    rw [arcDiagram_eq_matching sourcePath.length capA
        (stringSpineHasCupCapAtoms_ofAllCapArity capA capPureA) capChainedA sourcePos,
      arcDiagram_eq_matching sourcePath.length capB
        (stringSpineHasCupCapAtoms_ofAllCapArity capB capPureB) capChainedB sourcePos,
      capMatchEq]
  have capInternalCapCountsAgree : (arcStructureOfSpineList sourcePath.length capA).internalCapCounts
      = (arcStructureOfSpineList sourcePath.length capB).internalCapCounts :=
    stringPureCapSpines_internalCapCountsAgree_ofDiagram sourcePath.length capA capB
      capPureA capPureB capChainedA capChainedB capDiagramAgree
  have capArcEqual : arcStructureOfSpineList sourcePath.length capA
      = arcStructureOfSpineList sourcePath.length capB :=
    stringPureCapTailsCancel_ofDiagramAndInternalCap sourcePath.length capA capB
      capPureA capPureB capLengthEq capDiagramAgree capInternalCapCountsAgree
  have capTrace : SpineTraceEquiv adjointTripleModeSignature capA capB :=
    stringPureCapSpine_sort_unconditional sourcePath.length sourcePath capA capB
      capChainedA capChainedB capWordA capWordB capPureA capPureB capArcEqual
  have sharedMid : spineListTopWord sourcePath capA = spineListTopWord sourcePath capB :=
    spineListTopWord_atomicTraceEquiv (spineTraceEquiv_iff_atomicTraceEquiv.mp capTrace) sourcePath
  -- Transport the second cup's word chain to the shared mid word.
  have cupWordB : SpineBoundaryWordChained (spineListTopWord sourcePath capA) cupB := sharedMid ▸ cupWordBraw
  -- The shared cup top word: both cup blocks thread to the common `targetPath`.
  have topA : spineListTopWord (spineListTopWord sourcePath capA) cupA = targetPath := by
    rw [← spineListTopWord_append sourcePath capA cupA, ← splitA]
    exact valleyA.spineListTopWord_spine
  have topB : spineListTopWord (spineListTopWord sourcePath capA) cupB = targetPath := by
    rw [sharedMid, ← spineListTopWord_append sourcePath capB cupB, ← splitB]
    exact valleyB.spineListTopWord_spine
  have cupTopWordEq :
      spineListTopWord (spineListTopWord sourcePath capA) cupA
        = spineListTopWord (spineListTopWord sourcePath capA) cupB :=
    topA.trans topB.symm
  -- Fire the r41 producer with the derived word arguments, transporting back through the block splits.
  rw [splitA, splitB]
  exact stringPositiveMidValleysWithEqualMatching_spineTraceEquiv brick sourcePath.length sourcePos
    sourcePath (spineListTopWord sourcePath capA) capA capB cupA cupB
    capPureA capPureB cupPureA cupPureB cupChainedA cupChainedB wholeChainedA wholeChainedB
    capWordA capWordB cupWordA cupWordB cupTopWordEq midPositive wholeEq

/-! ## The brick→master implications — the whole #2020 residual gates on the SINGLE cup-sort brick -/

/-- ★ **Brick → completeness reduct-existence.**  Composing the L3 cell reducer with the r39 one-sub-producer beam:
`StringMatchingReductsShareSpineTrace` — the completeness reduct-existence residual — follows from ONLY the single
cup-sort brick `StringPositiveMidPureCupDeterminacy`.  The standing residual is collapsed from the sub-producer
`StringCellValleyTraceEquivPositive` down to the ONE brick. -/
theorem stringMatchingReductsShareSpineTrace_ofBrick
    (brick : StringPositiveMidPureCupDeterminacy) : StringMatchingReductsShareSpineTrace :=
  stringMatchingReductsShareSpineTrace_ofOneSubProducer (stringPositiveMidValleyTraceEquiv_holds brick)

/-- ★ **Brick → base completeness.**  `matchingOf cellA = matchingOf cellB → cellA ≈ cellB`, from ONLY the single
cup-sort brick, routed through the L3 reducer and the r39 one-sub-producer beam. -/
theorem stringConvOfMapEq_ofBrick
    (brick : StringPositiveMidPureCupDeterminacy)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (matchingsEqual : matchingOf cellA = matchingOf cellB) :
    StringSaturatedTwoCellConv cellA cellB :=
  stringConvOfMapEq_ofOneSubProducer (stringPositiveMidValleyTraceEquiv_holds brick) cellA cellB matchingsEqual

/-- ★★ **Brick → the FULL adjoint-triple word-problem DECISION.**  `Decidable (StringSaturatedTwoCellConv cellA
cellB)` on EVERY parallel pair, gated on ONLY the single cup-sort brick `StringPositiveMidPureCupDeterminacy`.  The
`isFalse` leg is residual-free (rides only the unconditional r2 soundness); the `isTrue` leg is gated on the one
brick, threaded through the L3 reducer and the r39 one-sub-producer beam.  This is the whole #2020 headline reduced to
exactly ONE cup-sort brick. -/
def decidableStringSaturatedConv_ofBrick
    (brick : StringPositiveMidPureCupDeterminacy)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    Decidable (StringSaturatedTwoCellConv cellA cellB) :=
  decidableStringSaturatedConv_ofOneSubProducer (stringPositiveMidValleyTraceEquiv_holds brick) cellA cellB

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the positive-mid CELL reducer is assembled and the whole #2020 residual is collapsed to the
SINGLE cup-sort brick (FC-3 r42, the L3 layer).**  `stringPositiveMidValleyTraceEquiv_holds : (brick) →
StringCellValleyTraceEquivPositive` — the last standing sub-producer after r39 — is now inhabited GATED on the ONE
named brick `StringPositiveMidPureCupDeterminacy`.  The cell reducer is a near-byte-identical additive mirror of the
r38 mid-`0` reducer with exactly three deltas: (δ1) the intro binds `midPos : 0 < survivorTopTotal` in place of
`midZeroA`; (δ2) the mid witness `midPositive` in place of the r38 mid-`0` witness; (δ3) the shared `midWord` — the
ONLY substantive change — obtained via the BRICK-FREE cap-trace route (`spineListTopWord_atomicTraceEquiv` on the
unconditional cap sort `stringPureCapSpine_sort_unconditional`, which is mid-generic), NOT the r38 length-`0`
`stringSharedMidWord_ofMidZero`.  Every other word/length argument is copied verbatim from r38 (mid-generic): block
split, Brick A/B chains, W3 cap word, top-word append.

  The BRICK→MASTER implications (`stringMatchingReductsShareSpineTrace_ofBrick`, `stringConvOfMapEq_ofBrick`,
  `decidableStringSaturatedConv_ofBrick`) compose the L3 reducer with the r39 one-sub-producer beam: the completeness
  reduct-existence residual, the base completeness, and the FULL word-problem DECISION all now gate on ONLY the single
  cup-sort brick — no more `StringCellValleyTraceEquivPositive` as a separate open obligation.  This is the brick→wall
  implication theorem the K = 1 framing requires: the whole FC-3 #2020 headline reduces to exactly ONE brick.

  What this does NOT flip (honestly): this round does NOT inhabit the brick `StringPositiveMidPureCupDeterminacy` (the
  positive-mid CUP sort — the r17 LOCATE/drop assembly re-parameterized off `matchingOfSpineList midWidth` with
  survivor-through-strand re-ranking, a genuine multi-round port; the printed precedent is uniform — Ridout–Saint-Aubin
  Jones normal form / Riehl–Verity strictly-undulating width-induction / Delpeuch–Vicary right-normal handedness, all
  "peel the extremal cup with matched-pair cancellation").  So `StringCellValleyTraceEquivPositive` stays gated on it,
  `StringCellValleyTraceEquiv` is not inhabited, and the completeness masters `fxString_hasAdjointTripleCompleteness`
  (`StringMatchingCompleteness`) and `fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) STAY `false`.  This
  round flips ONLY this NEW marker.  `= true`. -/
def fxString_hasPositiveMidValleyCellReducer : Bool := true

end FX1Poly.Polygraph
