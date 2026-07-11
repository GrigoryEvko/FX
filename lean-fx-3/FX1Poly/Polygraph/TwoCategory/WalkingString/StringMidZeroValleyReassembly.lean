import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCapHeadExtractionWordPinInhabited
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWidthZeroPureCupSort
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapInternalCountsPointwise
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPureCapArcReconstruct
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineTopWord
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineTraceAppendCongruence

/-! # WalkingString/StringMidZeroValleyReassembly — the FIRST consumer of the unconditional cap sort
(FC-3 r27 B3, the mid-zero cap/cup valley block reassembly)

FC-3 r26 shipped the string pure-cap sort as an UNCONDITIONAL capability (`stringPureCapSpine_sort_unconditional`)
with no wired user.  This file lands its first consumer: the string clone of the walking-adjunction
`midZeroSameMatchingValleys_spineTraceEquiv` (`SpineValleyMidZeroReassembly`) — the mid-width-`0` valley block
reassembly, the cap dual of the shipped width-`0` cup determinacy.  Two valleys `capBlock ++ cupBlock` whose cup
blocks run from the mid-boundary width `0` (the cap block consuming every bottom wire) are `SpineTraceEquiv`:

  * the CAP arm reconstructs the full cap arc equality from the cap `diagram` + length agreement — the internal cap
    counts agree by the shipped `stringPureCapSpines_internalCapCountsAgree_ofDiagram`, then the small enabling
    clone `stringPureCapTailsCancel_ofDiagramAndInternalCap` (B2a) closes the full arc equality, which the
    positivity-free `stringPureCapSpine_sort_unconditional` turns into the cap trace;
  * the CUP arm runs the positivity-free width-`0` determinacy `stringWidthZeroPureCupDeterminacyShared_proof` on
    the pure-cup block over the width-`0` mid-boundary;
  * the two arms combine through the `{signature}`-generic `spineTraceEquiv_appendCongr` — no string clone (contrast
    the back-append-SINGLE case, which needed `stringSpineTraceEquiv_backAppendCongr`).

Unlike the adjunction reassembly, the two string sorts thread a boundary WORD alongside the length chain (the r17
precedent): the cap arm carries `capWord` + two `SpineBoundaryWordChained capWord` chains, and the cup arm carries
`midWord` + two `SpineBoundaryWordChained midWord` chains plus the shared `spineListTopWord` equality.  This is the
pure block ASSEMBLY — it takes the two per-block agreements (cap `diagram`, cup width-`0` `matchingOf`) plus the
per-block arities / lengths / chains as hypotheses.  Producing those agreements from a whole-valley `matchingOf`
equality (the mid-width telescope + the floor-`0` cup-block reconstruct) is the standing residual named in the
honesty marker.

Raw Lean 4 + Init; pure block assembly over the shipped cap tails-cancel / unconditional cap sort and the inhabited
width-`0` cup determinacy, no `omega` / `simp`-AC / `WellFounded.fix`.  Per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The mid-`0` valley block reassembly (cap dual of the width-`0` cup brick) -/

/-- ★ **The mid-width-`0` string valley block reassembly.**  Two valleys `capBlock ++ cupBlock` whose cup blocks
run from the mid-boundary width `0` (the cap block consumes every bottom wire), with:

  * the CAP block `diagram` agreement (`capDiagramAgree`) at the cap bottom count and the cap length agreement
    (`capLengthEq`), the two cap word-chains at the shared `capWord`, and
  * the CUP block width-`0` `matchingOfSpineList` agreement (`cupMatchEq`), the two cup word-chains at the shared
    `midWord`, and the shared cup `spineListTopWord` (`cupTopWordEq`),

are `SpineTraceEquiv`.  The string mid-`0` mirror of `midZeroSameMatchingValleys_spineTraceEquiv`: the CAP arm
reconstructs the full cap arc equality (`stringPureCapSpines_internalCapCountsAgree_ofDiagram` +
`stringPureCapTailsCancel_ofDiagramAndInternalCap`) which the positivity-free `stringPureCapSpine_sort_unconditional`
turns into the cap trace, and the CUP arm runs the positivity-free width-`0` determinacy
`stringWidthZeroPureCupDeterminacyShared_proof`.  The two arms combine through the generic
`spineTraceEquiv_appendCongr`. -/
theorem stringMidZeroSameMatchingValleys_spineTraceEquiv
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (capBottomCount : Nat)
    (capWord midWord : ModalityPath adjointTripleGraph overallSource overallTarget)
    (capBlockFirst capBlockSecond cupBlockFirst cupBlockSecond :
      List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (capPureFirst : AllCapArity capBlockFirst) (capPureSecond : AllCapArity capBlockSecond)
    (cupPureFirst : AllCupArity cupBlockFirst) (cupPureSecond : AllCupArity cupBlockSecond)
    (capChainedFirst : SpineBoundaryChained capBottomCount capBlockFirst)
    (capChainedSecond : SpineBoundaryChained capBottomCount capBlockSecond)
    (cupChainedFirst : SpineBoundaryChained 0 cupBlockFirst)
    (cupChainedSecond : SpineBoundaryChained 0 cupBlockSecond)
    (capWordChainedFirst : SpineBoundaryWordChained capWord capBlockFirst)
    (capWordChainedSecond : SpineBoundaryWordChained capWord capBlockSecond)
    (cupWordChainedFirst : SpineBoundaryWordChained midWord cupBlockFirst)
    (cupWordChainedSecond : SpineBoundaryWordChained midWord cupBlockSecond)
    (cupTopWordEq : spineListTopWord midWord cupBlockFirst
      = spineListTopWord midWord cupBlockSecond)
    (capLengthEq : capBlockFirst.length = capBlockSecond.length)
    (capDiagramAgree : (arcStructureOfSpineList capBottomCount capBlockFirst).diagram
      = (arcStructureOfSpineList capBottomCount capBlockSecond).diagram)
    (cupMatchEq : matchingOfSpineList 0 cupBlockFirst = matchingOfSpineList 0 cupBlockSecond) :
    SpineTraceEquiv adjointTripleModeSignature
      (capBlockFirst ++ cupBlockFirst) (capBlockSecond ++ cupBlockSecond) := by
  -- CAP arm: reconstruct the full cap arc equality from the cap `diagram` + length agreement (the internal cap
  -- counts agree by the shipped pointwise characterization), then the positivity-free unconditional cap sort.
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
  -- CUP arm: the positivity-free width-`0` pure-cup determinacy on the pure matching carrier.
  have cupTrace : SpineTraceEquiv adjointTripleModeSignature cupBlockFirst cupBlockSecond :=
    stringWidthZeroPureCupDeterminacyShared_proof midWord cupBlockFirst cupBlockSecond
      cupPureFirst cupPureSecond cupChainedFirst cupChainedSecond
      cupWordChainedFirst cupWordChainedSecond cupTopWordEq cupMatchEq
  exact spineTraceEquiv_appendCongr capTrace cupTrace

/-! ## Concrete truth-probe (anti-vacuity) — a genuine mixed cap/cup valley at `tip` -/

/-- A concrete CUP spine atom at `tip`: the upper unit `η : id_tip ⇒ G·H` with empty whiskering contexts.  Dom
`id_tip` (length `0`), cod `G·H` (length `2`), window `0` — a genuine cup, the same-endpoint partner of the cap
probe `stringCapSortProbeAtom` (both live at `tip`, so `[cap] ++ [cup]` is a genuine mixed valley). -/
def stringValleyReassemblyProbeCup :
    SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.tip :=
  ⟨AdjointTripleMode.tip, AdjointTripleMode.tip,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
    stringGH, StringTwoCell.unitUpper,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip⟩

/-- The cap block's shared boundary word: the lower counit's dom word `G·F` (the cap `ε` fires at width `2`). -/
def stringValleyReassemblyProbeCapWord :
    ModalityPath adjointTripleGraph AdjointTripleMode.tip AdjointTripleMode.tip :=
  composePath stringCapSortProbeAtom.leftContext
    (composePath stringCapSortProbeAtom.generatorDom stringCapSortProbeAtom.rightContext)

/-- The cup block's shared boundary word: the upper unit's dom word `id_tip` (the cup `η` fires at width `0`). -/
def stringValleyReassemblyProbeMidWord :
    ModalityPath adjointTripleGraph AdjointTripleMode.tip AdjointTripleMode.tip :=
  composePath stringValleyReassemblyProbeCup.leftContext
    (composePath stringValleyReassemblyProbeCup.generatorDom stringValleyReassemblyProbeCup.rightContext)

/-- ★ **The mid-`0` valley reassembly FIRES on a genuine mixed cap/cup valley.**  Instantiating the reassembly on
the concrete two-block valley `[ε] ++ [η]` at `tip` (a cap block that consumes both bottom wires to mid-width `0`,
then a cup block that opens two top wires) as both arguments — equal matching, equal diagram, shared top word —
runs BOTH arms end-to-end: the CAP arm reconstructs the arc equality and fires the unconditional cap sort on the
genuine cap `ε`, and the CUP arm fires the width-`0` determinacy on the genuine cup `η`, gluing through the generic
append congruence.  A machine-checked non-vacuity witness that neither arm is vacuous on a real mixed valley. -/
theorem stringMidZeroValleyReassembly_firesOnMixedValley :
    SpineTraceEquiv adjointTripleModeSignature
      ([stringCapSortProbeAtom] ++ [stringValleyReassemblyProbeCup])
      ([stringCapSortProbeAtom] ++ [stringValleyReassemblyProbeCup]) :=
  stringMidZeroSameMatchingValleys_spineTraceEquiv 2
    stringValleyReassemblyProbeCapWord stringValleyReassemblyProbeMidWord
    [stringCapSortProbeAtom] [stringCapSortProbeAtom]
    [stringValleyReassemblyProbeCup] [stringValleyReassemblyProbeCup]
    (AllCapArity.cons rfl rfl AllCapArity.nil) (AllCapArity.cons rfl rfl AllCapArity.nil)
    (AllCupArity.cons rfl rfl AllCupArity.nil) (AllCupArity.cons rfl rfl AllCupArity.nil)
    (SpineBoundaryChained.cons stringCapSortProbeAtom rfl (SpineBoundaryChained.nil 0))
    (SpineBoundaryChained.cons stringCapSortProbeAtom rfl (SpineBoundaryChained.nil 0))
    (SpineBoundaryChained.cons stringValleyReassemblyProbeCup rfl (SpineBoundaryChained.nil 2))
    (SpineBoundaryChained.cons stringValleyReassemblyProbeCup rfl (SpineBoundaryChained.nil 2))
    (SpineBoundaryWordChained.cons stringCapSortProbeAtom rfl (SpineBoundaryWordChained.nil _))
    (SpineBoundaryWordChained.cons stringCapSortProbeAtom rfl (SpineBoundaryWordChained.nil _))
    (SpineBoundaryWordChained.cons stringValleyReassemblyProbeCup rfl (SpineBoundaryWordChained.nil _))
    (SpineBoundaryWordChained.cons stringValleyReassemblyProbeCup rfl (SpineBoundaryWordChained.nil _))
    rfl rfl rfl rfl

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the unconditional cap sort is now WIRED into the mid-`0` valley leg (FC-3 r27).**
`stringMidZeroSameMatchingValleys_spineTraceEquiv` is the FIRST consumer of the r26 unconditional pure-cap sort:
the string clone of the walking-adjunction `midZeroSameMatchingValleys_spineTraceEquiv`.  Its CAP arm reconstructs
the full cap arc equality from the cap `diagram` + length agreement — internal cap counts by the shipped
`stringPureCapSpines_internalCapCountsAgree_ofDiagram`, then the small enabling clone
`stringPureCapTailsCancel_ofDiagramAndInternalCap` (this round's B2a) — and fires
`stringPureCapSpine_sort_unconditional`; its CUP arm fires the width-`0` determinacy
`stringWidthZeroPureCupDeterminacyShared_proof`; the two arms combine through the generic
`spineTraceEquiv_appendCongr` (no string clone).  The two string sorts are word-threaded (the r17 precedent): the
cap arm carries `capWord`, the cup arm `midWord` + the shared `spineListTopWord`.  The truth-probe
`stringMidZeroValleyReassembly_firesOnMixedValley` fires BOTH arms on a genuine mixed valley `[ε] ++ [η]` at `tip`
(cap `ε : G·F ⇒ id_tip` consuming both bottom wires to mid-width `0`, cup `η : id_tip ⇒ G·H` opening two top
wires), so neither arm is vacuous.

  What this does NOT flip (honestly): `StringMidZeroValleyTraceEquiv` (`StringValleyDegenerateSplit`) stays
  UNINHABITED — this reassembly is the pure block ASSEMBLY, taking the two per-block agreements as hypotheses; the
  whole-valley producer additionally needs the mid-width telescope (the string clones of
  `survivorTopTotal_eq_midWidth` / `capLength_eq_of_midWidth_eq` / `sameWholeMatching_{cap,cup}BlockMatchingEq`, M2)
  and the floor-`0` cup-block reconstruct (`StringMidZeroCupBlockReconstruct` analog, the ~560-line
  shift-simulation port, M3), both named and un-cloned this round.  So `fxString_hasAdjointTripleCompleteness`
  (`StringMatchingCompleteness`) and `fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) also stay `false`.
  This round flips ONLY this NEW marker: the cap sort is wired into one of the mid-zero producer's three bricks.
  `= true`. -/
def fxString_hasMidZeroValleyReassembly : Bool := true

end FX1Poly.Polygraph
