import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyMatchingSpineTraceEquiv
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingWidthZeroSort
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupAssembly
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyWidthTelescope

/-! # SpineValleyMidZeroReassembly — the mid-width-`0` valley block reassembly (Track B, MidZero cap dual)

The FULL `CellValleyTraceEquiv` lift (`SpineValleyCellDegenerate`) case-splits every valley on source width and
mid-width.  The doubly-positive branch is the shipped `cellValleyTraceEquiv_ofPositive`; the empty-source branch
(`sourcePath.length = 0`) reduces DIRECTLY to the width-0 pure-cup determinacy
(`degenerateEmptySource_of_widthZero`).  The remaining Tier-D branch is case (b) — **mid-width `0`**
(`survivorTopTotal (matchingOf valleyA) = 0`, the cap block consuming every bottom wire so the cup block runs from
a width-`0` mid-state) at POSITIVE source width.  This is NOT a bare width-0 cup application: the whole-valley
theorem `valleysWithEqualMatching_spineTraceEquiv` hard-requires `0 < midWidth`, so case (b) needs a mid-width-`0`
BLOCK REASSEMBLY — the cap dual of the width-0 cup brick.

This file lands the **reassembly**, all zero-axiom:

  * ★ **`midZeroSameMatchingValleys_spineTraceEquiv`** — the mid-`0` mirror of the shipped
    `sameMatchingValleys_spineTraceEquiv` with the CUP arm swapped from `pureCupSpine_sort` (which hard-requires
    `0 < cupBottomCount`) to the POSITIVITY-FREE width-0 determinacy `widthZeroPureCupDeterminacy_proof`.  The CAP
    arm is unchanged (positive cap bottom count `= sourcePath.length`): the cap `diagram` agreement + the cap
    length agreement reconstruct the full cap arc equality (`pureCapTailsCancel_ofDiagramAndInternalCap`, the
    cap-side internal-count free leg) which `pureCapSpine_sort` — itself positivity-free — turns into the cap
    trace equivalence.  The cup arm runs at `cupBottomCount = 0` on the PURE MATCHING carrier: two boundary-chained
    pure-cup spines over the width-`0` mid-boundary with equal `matchingOfSpineList 0` are `SpineTraceEquiv` by the
    ported width-0 LOCATE stack.  The two arms combine through `spineTraceEquiv_appendCongr`.

The cap arm consumes the cap block `diagram` agreement (arc carrier); the cup arm consumes the cup block width-`0`
`matchingOfSpineList` agreement (matching carrier).  This file is the pure ASSEMBLY — it takes those two per-block
agreements plus the block lengths / arities / boundary chaining; producing the two per-block agreements from a
whole-valley `matchingOf` equality (the cap split + the mid-`0` cup reconstruction) is the wiring lift, landed
downstream in `SpineValleyCellDegenerate`.

Raw Lean 4 + Init; pure block assembly over the shipped cap tails-cancel / cap sort and the ported width-0 cup
determinacy, no `omega` / `simp`-AC / `WellFounded.fix`.  Per-declaration `#assert_no_axioms` gated in the audit
twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The mid-`0` valley block reassembly (cap dual of the width-0 cup brick) -/

/-- ★ **The mid-width-`0` valley block reassembly.**  Two valleys `capBlock ++ cupBlock` whose cup blocks run from
the mid-boundary width `0` (the cap block consumes every bottom wire), with:

  * the CAP block `diagram` agreement (`capDiagramAgree`) at the POSITIVE cap bottom count (= source width) and the
    cap length agreement (`capLengthEq`), and
  * the CUP block width-`0` `matchingOfSpineList` agreement (`cupMatchEq`),

are `SpineTraceEquiv`.  The mid-`0` mirror of `sameMatchingValleys_spineTraceEquiv`: the CAP arm is unchanged
(cap `diagram` + length + the cap-side internal-count free leg reconstruct the full cap arc equality, which the
positivity-free `pureCapSpine_sort` turns into the cap trace), and the CUP arm is swapped to the positivity-free
width-0 determinacy `widthZeroPureCupDeterminacy_proof` (the ported LOCATE stack, on the pure matching carrier at
`bottomCount = 0`).  The two arms combine through `spineTraceEquiv_appendCongr`. -/
theorem midZeroSameMatchingValleys_spineTraceEquiv
    {overallSource overallTarget : adjunctionGraph.Mode}
    (capBottomCount : Nat)
    (capBlockFirst capBlockSecond cupBlockFirst cupBlockSecond :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (capPureFirst : AllCapArity capBlockFirst) (capPureSecond : AllCapArity capBlockSecond)
    (cupPureFirst : AllCupArity cupBlockFirst) (cupPureSecond : AllCupArity cupBlockSecond)
    (capChainedFirst : SpineBoundaryChained capBottomCount capBlockFirst)
    (capChainedSecond : SpineBoundaryChained capBottomCount capBlockSecond)
    (cupChainedFirst : SpineBoundaryChained 0 cupBlockFirst)
    (cupChainedSecond : SpineBoundaryChained 0 cupBlockSecond)
    (capLengthEq : capBlockFirst.length = capBlockSecond.length)
    (capDiagramAgree : (arcStructureOfSpineList capBottomCount capBlockFirst).diagram
      = (arcStructureOfSpineList capBottomCount capBlockSecond).diagram)
    (cupMatchEq : matchingOfSpineList 0 cupBlockFirst = matchingOfSpineList 0 cupBlockSecond) :
    SpineTraceEquiv adjunctionModeSignature
      (capBlockFirst ++ cupBlockFirst) (capBlockSecond ++ cupBlockSecond) := by
  -- CAP arm: reconstruct the full cap arc equality from the cap `diagram` + length agreement (cap-side
  -- internal-count free leg discharged internally), then the positivity-free `pureCapSpine_sort`.
  have capInternalCapCountsAgree :
      (arcStructureOfSpineList capBottomCount capBlockFirst).internalCapCounts
        = (arcStructureOfSpineList capBottomCount capBlockSecond).internalCapCounts :=
    pureCapSpines_internalCapCountsAgree_ofDiagram capBottomCount capBlockFirst capBlockSecond
      capPureFirst capPureSecond capChainedFirst capChainedSecond capDiagramAgree
  have capArcEqual : arcStructureOfSpineList capBottomCount capBlockFirst
      = arcStructureOfSpineList capBottomCount capBlockSecond :=
    pureCapTailsCancel_ofDiagramAndInternalCap capBottomCount capBlockFirst capBlockSecond
      capPureFirst capPureSecond capLengthEq capDiagramAgree capInternalCapCountsAgree
  have capTrace : SpineTraceEquiv adjunctionModeSignature capBlockFirst capBlockSecond :=
    pureCapSpine_sort capBottomCount capBlockFirst capBlockSecond capChainedFirst capChainedSecond
      capPureFirst capPureSecond capArcEqual
  -- CUP arm: the positivity-free width-0 pure-cup determinacy on the pure matching carrier.
  have cupTrace : SpineTraceEquiv adjunctionModeSignature cupBlockFirst cupBlockSecond :=
    widthZeroPureCupDeterminacy_proof cupBlockFirst cupBlockSecond cupPureFirst cupPureSecond
      cupChainedFirst cupChainedSecond cupMatchEq
  exact spineTraceEquiv_appendCongr capTrace cupTrace

/-! ## The isolated mid-`0` cup-block reconstruction residual + the gated spine-level reduction -/

/-- The **mid-width-`0` cup-block reconstruction** residual — the mid-`0` analog of the shipped
`cupRestrict_reconstructs` (`ValleyCupReconstruct`) with `midPositive` replaced by the mid-`0` witness
(`survivorTopTotal (matchingOf bc (capBlock ++ cupBlock)) = 0`).  It states that the cup block's OWN diagram is
`cupRestrict` of the whole valley's diagram — read at the mid-boundary width `capState.openWires.length` (which is
`0` under the witness, `survivorTopTotal_eq_midWidth`).

At mid-`0` the three NON-partner fields close exactly as in the positive `cupRestrict_reconstructs`
(`cupRestrict_bottomCount_eq` / `cupRestrict_topCount_eq` / `cupRestrict_loops_eq`, none needing `0 < midWidth`),
and the cup-BOTTOM (case 1) and survivor-TOP (case 2) partner cases are VACUOUS (no port below the width-`0`
mid-boundary; no survivor top since `survivorTopTotal = 0`).  The SOLE genuine content is the top-top cup-arc
partner (case 3) at floor `0`: the cup-alone run (from-scratch seed `⟨[], [], 0, 0⟩`) and the in-valley cup run
(from `capState`, an all-open-wires-`0` state carrying inert cap links, fresh legs `bc + k`) agree on the top-top
partner offset.  Since `survivorTopTotal = 0` there is no survivor scatter, so this is the PURE fresh-leg shift
`bc + k ↔ 0 + k` (the "links-irrelevance at `0` open wires") — the mid-`0` mirror of `cupTopTopPartner`
(`ValleyCupTopTopSeed`), whose shipped proof rides `pureCapTopPartnerBelow` at a POSITIVE floor and so does not
specialize to floor `0`.  This is the isolated residual of the mid-`0` reassembly; everything else above it is
landed here. -/
def MidZeroCupBlockReconstruct : Prop :=
  ∀ {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat),
    0 < bottomCount →
    ∀ (capBlock cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget)),
      AllCapArity capBlock → AllCupArity cupBlock →
      SpineBoundaryChained
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock →
      SpineBoundaryChained bottomCount (capBlock ++ cupBlock) →
      survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock)) = 0 →
      matchingOfSpineList
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock
        = cupRestrict (matchingOfSpineList bottomCount (capBlock ++ cupBlock))

/-- ★ **The mid-width-`0` whole-valley `SpineTraceEquiv`, gated on the mid-`0` cup reconstruction.**  Two valleys
`capBlock ++ cupBlock` (pure-cap prefix, pure-cup suffix, boundary-chained, POSITIVE bottom count, mid-width `0`)
with EQUAL whole-boundary `matchingOf` are `SpineTraceEquiv`.  Mirrors the shipped
`valleysWithEqualMatching_spineTraceEquiv` (the positive-mid-width top of the Piece-II pyramid), but at mid-`0`:

  * the cap blocks agree (shipped `sameWholeMatching_capBlockMatchingEq`, needs only the POSITIVE bottom count),
    converted to the cap `diagram` agreement (`arcDiagram_eq_matching` at the positive cap width);
  * the two mid-widths are BOTH `0` (`survivorTopTotal_eq_midWidth` + the mid-`0` witness), giving the cap length
    agreement (`capLength_eq_of_midWidth_eq`);
  * the cup blocks agree at width `0` (the gated mid-`0` reconstruction fed through the pure equational
    `sameWholeMatching_cupBlockMatchingEq`, then aligned to width `0`);

then the mid-`0` block reassembly `midZeroSameMatchingValleys_spineTraceEquiv` closes.  Gated ONLY on
`MidZeroCupBlockReconstruct` — the single isolated brick. -/
theorem midZeroValleysWithEqualMatching_spineTraceEquiv
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat) (bottomPositive : 0 < bottomCount)
    (capBlockFirst capBlockSecond cupBlockFirst cupBlockSecond :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (capPureFirst : AllCapArity capBlockFirst) (capPureSecond : AllCapArity capBlockSecond)
    (cupPureFirst : AllCupArity cupBlockFirst) (cupPureSecond : AllCupArity cupBlockSecond)
    (cupChainedFirst : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockFirst)
    (cupChainedSecond : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length cupBlockSecond)
    (wholeChainedFirst : SpineBoundaryChained bottomCount (capBlockFirst ++ cupBlockFirst))
    (wholeChainedSecond : SpineBoundaryChained bottomCount (capBlockSecond ++ cupBlockSecond))
    (midZeroFirst : survivorTopTotal (matchingOfSpineList bottomCount (capBlockFirst ++ cupBlockFirst)) = 0)
    (wholeEq : matchingOfSpineList bottomCount (capBlockFirst ++ cupBlockFirst)
      = matchingOfSpineList bottomCount (capBlockSecond ++ cupBlockSecond))
    (cupReconstruct : MidZeroCupBlockReconstruct) :
    SpineTraceEquiv adjunctionModeSignature
      (capBlockFirst ++ cupBlockFirst) (capBlockSecond ++ cupBlockSecond) := by
  -- Both mid-widths are `0`.
  have midWidthFirstZero :
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length = 0 := by
    rw [← survivorTopTotal_eq_midWidth bottomCount bottomPositive capBlockFirst cupBlockFirst
      capPureFirst cupPureFirst cupChainedFirst]
    exact midZeroFirst
  have midZeroSecond :
      survivorTopTotal (matchingOfSpineList bottomCount (capBlockSecond ++ cupBlockSecond)) = 0 := by
    rw [← wholeEq]; exact midZeroFirst
  have midWidthSecondZero :
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length = 0 := by
    rw [← survivorTopTotal_eq_midWidth bottomCount bottomPositive capBlockSecond cupBlockSecond
      capPureSecond cupPureSecond cupChainedSecond]
    exact midZeroSecond
  have midEq :
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length
        = (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length := by
    rw [midWidthFirstZero, midWidthSecondZero]
  -- The two cap prefixes are boundary-chained (restriction of the whole valley chaining).
  have capChainedFirst : SpineBoundaryChained bottomCount capBlockFirst :=
    spineBoundaryChained_prefix_ofAppend capBlockFirst cupBlockFirst bottomCount wholeChainedFirst
  have capChainedSecond : SpineBoundaryChained bottomCount capBlockSecond :=
    spineBoundaryChained_prefix_ofAppend capBlockSecond cupBlockSecond bottomCount wholeChainedSecond
  -- The cap length agreement from the (equal) mid-widths.
  have capLengthEq : capBlockFirst.length = capBlockSecond.length :=
    capLength_eq_of_midWidth_eq bottomCount capBlockFirst capBlockSecond capPureFirst capPureSecond
      capChainedFirst capChainedSecond midEq
  -- The cap-block matchings agree (shipped cap half, needs only the positive bottom count).
  have capMatchEq : matchingOfSpineList bottomCount capBlockFirst
      = matchingOfSpineList bottomCount capBlockSecond :=
    sameWholeMatching_capBlockMatchingEq bottomCount bottomPositive capBlockFirst capBlockSecond
      cupBlockFirst cupBlockSecond capPureFirst capPureSecond cupPureFirst cupPureSecond
      cupChainedFirst cupChainedSecond wholeChainedFirst wholeChainedSecond wholeEq
  -- The cap `diagram` agreement (positive cap-width `arcDiagram_eq_matching`).
  have capDiagramAgree : (arcStructureOfSpineList bottomCount capBlockFirst).diagram
      = (arcStructureOfSpineList bottomCount capBlockSecond).diagram := by
    rw [arcDiagram_eq_matching bottomCount capBlockFirst
        (spineHasCupCapAtoms_ofAllCapArity capBlockFirst capPureFirst) capChainedFirst bottomPositive,
      arcDiagram_eq_matching bottomCount capBlockSecond
        (spineHasCupCapAtoms_ofAllCapArity capBlockSecond capPureSecond) capChainedSecond bottomPositive,
      capMatchEq]
  -- The two mid-`0` cup reconstructions.
  have reconFirst := cupReconstruct bottomCount bottomPositive capBlockFirst cupBlockFirst
    capPureFirst cupPureFirst cupChainedFirst wholeChainedFirst midZeroFirst
  have reconSecond := cupReconstruct bottomCount bottomPositive capBlockSecond cupBlockSecond
    capPureSecond cupPureSecond cupChainedSecond wholeChainedSecond midZeroSecond
  -- The cup-block matchings agree at the mid-widths, then aligned to width `0`.
  have cupMatchEqRaw :
      matchingOfSpineList
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockFirst
        = matchingOfSpineList
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length cupBlockSecond :=
    sameWholeMatching_cupBlockMatchingEq bottomCount capBlockFirst capBlockSecond cupBlockFirst cupBlockSecond
      reconFirst reconSecond wholeEq
  have cupMatchEq : matchingOfSpineList 0 cupBlockFirst = matchingOfSpineList 0 cupBlockSecond := by
    rw [midWidthFirstZero, midWidthSecondZero] at cupMatchEqRaw
    exact cupMatchEqRaw
  -- The cup blocks are boundary-chained at width `0`.
  have cupChained0First : SpineBoundaryChained 0 cupBlockFirst := midWidthFirstZero ▸ cupChainedFirst
  have cupChained0Second : SpineBoundaryChained 0 cupBlockSecond := midWidthSecondZero ▸ cupChainedSecond
  exact midZeroSameMatchingValleys_spineTraceEquiv bottomCount
    capBlockFirst capBlockSecond cupBlockFirst cupBlockSecond
    capPureFirst capPureSecond cupPureFirst cupPureSecond
    capChainedFirst capChainedSecond cupChained0First cupChained0Second
    capLengthEq capDiagramAgree cupMatchEq

end FX1Poly.Polygraph
