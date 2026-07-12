import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineValleyMidZeroCupReconstruct
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMidZeroValleyReassembly
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyDegenerateSplit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineValleyWidthTelescope
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCapReconstruct
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCupReconstruct
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSurvivorTopTotalMidWidth
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcMatchViewFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLastCupReadoff
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyAppendSplit

/-! # WalkingString/StringMidZeroValleyProducer — the gated mid-width-`0` whole-valley `SpineTraceEquiv` producer,
gate inlined (FC-3 r36, the mid-zero producer's block-level headline)

The string clone of the walking-adjunction `midZeroValleysWithEqualMatching_spineTraceEquiv`
(`SpineValleyMidZeroReassembly`): two valleys `capBlock ++ cupBlock` (pure-cap prefix, pure-cup suffix,
boundary-chained, POSITIVE bottom count, mid-width `0`) with EQUAL whole-boundary `matchingOf` are
`SpineTraceEquiv`.  Every dependency this producer needs is already SHIPPED, so this file is a pure ASSEMBLY that
combines them and threads the string sorts' boundary WORDS:

  * the two cap blocks agree (`stringSameWholeMatching_capBlockMatchingEq`, M2c cap, needs only the POSITIVE
    bottom count), converted to the cap `diagram` agreement via the `{signature}`-generic `arcDiagram_eq_matching`
    at the positive cap width;
  * both mid-widths are `0` (`stringSurvivorTopTotal_eq_midWidth` + the mid-`0` witness), giving the cap length
    agreement (`stringCapLength_eq_of_midWidth_eq`);
  * the mid-`0` cup-block reconstruction is DISCHARGED (the r35 `stringMidZeroCupBlockReconstruct_holds`), so it is
    INLINED here — not carried as a gate hypothesis; fed through the pure equational
    `stringSameWholeMatching_cupBlockMatchingEq` and aligned to width `0`;

then the mid-`0` block reassembly `stringMidZeroSameMatchingValleys_spineTraceEquiv` (r27) closes.  Unlike the
walking-adjunction producer — whose reassembly is un-word-threaded — the string reassembly threads a boundary WORD
alongside the length chain (the r17 precedent): the cap arm carries `capWord` + two `SpineBoundaryWordChained
capWord` chains, and the cup arm carries `midWord` + two `SpineBoundaryWordChained midWord` chains plus the shared
`spineListTopWord` equality.  So the producer takes those word data as hypotheses (exactly as the reassembly does),
threading them to the final call; the length chains it derives internally (cap prefix restriction, mid-`0`
transport) exactly as the adjunction producer does.

This is the block-level headline.  It does NOT inhabit `StringMidZeroValleyTraceEquiv`
(`StringValleyDegenerateSplit`) — that cell-level reducer additionally needs the WORD-chain derivation over a
NON-empty cap prefix at positive source width (a shared-`midWord` fact over two parallel cap blocks that both run
to mid-width `0`, the genuine word-threading delta), named in the honesty marker.  So the completeness masters
`fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) and `fxString_hasConvOfMapEqPortFlip`
(`StringConvOfMapEqPort`) stay `false`.

Raw Lean 4 + Init; pure block assembly over the shipped cap/cup splitters, the mid-width telescope, the discharged
mid-`0` cup reconstruction, and the word-threaded block reassembly, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The gated mid-width-`0` whole-valley producer (gate inlined) -/

/-- ★ **The mid-width-`0` whole-valley string `SpineTraceEquiv`, gate inlined.**  Two valleys
`capBlock ++ cupBlock` (pure-cap prefix, pure-cup suffix, boundary-chained, POSITIVE bottom count, mid-width `0`)
with EQUAL whole-boundary `matchingOf` are `SpineTraceEquiv`.  The string mirror of
`midZeroValleysWithEqualMatching_spineTraceEquiv`, but at the walking ADJOINT-TRIPLE signature and with the r35
mid-`0` cup reconstruction DISCHARGED (inlined, not a gate hypothesis).

The two string sorts are word-threaded (the r17 precedent): the caller supplies the shared cap boundary word
`capWord` (both cap blocks word-chained from it), the shared mid boundary word `midWord` (both cup blocks
word-chained from it), and the shared cup `spineListTopWord` (`cupTopWordEq`).  The length chains are derived
internally: the cap prefixes are boundary-chained (`spineBoundaryChained_prefix_ofAppend`), both mid-widths are `0`
(`stringSurvivorTopTotal_eq_midWidth` + the mid-`0` witness), and the width-`0` cup chains transport across.  The
cap blocks agree (`stringSameWholeMatching_capBlockMatchingEq`) → cap `diagram` agreement
(`arcDiagram_eq_matching`); the cap lengths agree (`stringCapLength_eq_of_midWidth_eq`); the cup blocks agree at
width `0` (the inlined `stringMidZeroCupBlockReconstruct_holds` fed through `stringSameWholeMatching_cupBlockMatchingEq`).
Then `stringMidZeroSameMatchingValleys_spineTraceEquiv` closes. -/
theorem stringMidZeroValleysWithEqualMatching_spineTraceEquiv
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
    (midZeroFirst : survivorTopTotal (matchingOfSpineList bottomCount (capBlockFirst ++ cupBlockFirst)) = 0)
    (wholeEq : matchingOfSpineList bottomCount (capBlockFirst ++ cupBlockFirst)
      = matchingOfSpineList bottomCount (capBlockSecond ++ cupBlockSecond)) :
    SpineTraceEquiv adjointTripleModeSignature
      (capBlockFirst ++ cupBlockFirst) (capBlockSecond ++ cupBlockSecond) := by
  -- Both mid-widths are `0`.
  have midWidthFirstZero :
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length = 0 := by
    rw [← stringSurvivorTopTotal_eq_midWidth bottomCount bottomPositive capBlockFirst cupBlockFirst
      capPureFirst cupPureFirst cupChainedFirst]
    exact midZeroFirst
  have midZeroSecond :
      survivorTopTotal (matchingOfSpineList bottomCount (capBlockSecond ++ cupBlockSecond)) = 0 := by
    rw [← wholeEq]; exact midZeroFirst
  have midWidthSecondZero :
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length = 0 := by
    rw [← stringSurvivorTopTotal_eq_midWidth bottomCount bottomPositive capBlockSecond cupBlockSecond
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
  -- The two mid-`0` cup reconstructions (the r35 DISCHARGED brick, inlined).
  have reconFirst := stringMidZeroCupBlockReconstruct_holds bottomCount bottomPositive capBlockFirst cupBlockFirst
    capPureFirst cupPureFirst cupChainedFirst wholeChainedFirst midZeroFirst
  have reconSecond := stringMidZeroCupBlockReconstruct_holds bottomCount bottomPositive capBlockSecond cupBlockSecond
    capPureSecond cupPureSecond cupChainedSecond wholeChainedSecond midZeroSecond
  -- The cup-block matchings agree at the mid-widths, then aligned to width `0`.
  have cupMatchEqRaw :
      matchingOfSpineList
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockFirst
        = matchingOfSpineList
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length cupBlockSecond :=
    stringSameWholeMatching_cupBlockMatchingEq bottomCount capBlockFirst capBlockSecond cupBlockFirst cupBlockSecond
      reconFirst reconSecond wholeEq
  have cupMatchEq : matchingOfSpineList 0 cupBlockFirst = matchingOfSpineList 0 cupBlockSecond := by
    rw [midWidthFirstZero, midWidthSecondZero] at cupMatchEqRaw
    exact cupMatchEqRaw
  -- The cup blocks are boundary-chained at width `0`.
  have cupChained0First : SpineBoundaryChained 0 cupBlockFirst := midWidthFirstZero ▸ cupChainedFirst
  have cupChained0Second : SpineBoundaryChained 0 cupBlockSecond := midWidthSecondZero ▸ cupChainedSecond
  exact stringMidZeroSameMatchingValleys_spineTraceEquiv bottomCount capWord midWord
    capBlockFirst capBlockSecond cupBlockFirst cupBlockSecond
    capPureFirst capPureSecond cupPureFirst cupPureSecond
    capChainedFirst capChainedSecond cupChained0First cupChained0Second
    capWordChainedFirst capWordChainedSecond cupWordChainedFirst cupWordChainedSecond
    cupTopWordEq capLengthEq capDiagramAgree cupMatchEq

/-! ## Concrete truth-probe (anti-vacuity) — the genuine mid-zero string valley `[ε] ++ [η']` at `tip` -/

/-- The cap block's shared boundary word for the width-telescope probe: the lower counit's dom word `G·F`. -/
def stringMidZeroValleyProducerProbeCapWord :
    ModalityPath adjointTripleGraph AdjointTripleMode.tip AdjointTripleMode.tip :=
  composePath stringWidthTelescopeProbeCapAtom.leftContext
    (composePath stringWidthTelescopeProbeCapAtom.generatorDom stringWidthTelescopeProbeCapAtom.rightContext)

/-- The cup block's shared mid boundary word for the width-telescope probe: the cap's cod word `id_tip` (the
mid-width-`0` boundary the cup `η'` fires from). -/
def stringMidZeroValleyProducerProbeMidWord :
    ModalityPath adjointTripleGraph AdjointTripleMode.tip AdjointTripleMode.tip :=
  composePath stringWidthTelescopeProbeCapAtom.leftContext
    (composePath stringWidthTelescopeProbeCapAtom.generatorCod stringWidthTelescopeProbeCapAtom.rightContext)

/-- ★ **The mid-zero whole-valley producer FIRES on a genuine mixed string valley.**  Instantiating the producer on
the concrete two-block valley `[ε] ++ [η']` at `tip` (`bottomCount = 2`, mid-width `0`: the cap `ε` consumes both
bottom wires, then the cup `η'` opens two top wires) as both arguments — equal matching, shared cap/mid words —
runs the WHOLE producer end-to-end: the mid-width telescope collapses both mid-widths to `0`, the cap splitter and
the inlined mid-`0` cup reconstruction supply the two per-block agreements, and the word-threaded reassembly fires
BOTH sort arms (cap sort on the genuine cap `ε`, width-`0` cup determinacy on the genuine cup `η'`).  A
machine-checked non-vacuity witness that the producer does real work on a real mixed mid-zero valley. -/
theorem stringMidZeroValleyProducer_firesOnMixedValley :
    SpineTraceEquiv adjointTripleModeSignature
      ([stringWidthTelescopeProbeCapAtom] ++ [stringWidthTelescopeProbeCupAtom])
      ([stringWidthTelescopeProbeCapAtom] ++ [stringWidthTelescopeProbeCupAtom]) :=
  stringMidZeroValleysWithEqualMatching_spineTraceEquiv 2 (by decide)
    stringMidZeroValleyProducerProbeCapWord stringMidZeroValleyProducerProbeMidWord
    [stringWidthTelescopeProbeCapAtom] [stringWidthTelescopeProbeCapAtom]
    [stringWidthTelescopeProbeCupAtom] [stringWidthTelescopeProbeCupAtom]
    (AllCapArity.cons rfl rfl AllCapArity.nil) (AllCapArity.cons rfl rfl AllCapArity.nil)
    (AllCupArity.cons rfl rfl AllCupArity.nil) (AllCupArity.cons rfl rfl AllCupArity.nil)
    (SpineBoundaryChained.cons stringWidthTelescopeProbeCupAtom rfl (SpineBoundaryChained.nil 2))
    (SpineBoundaryChained.cons stringWidthTelescopeProbeCupAtom rfl (SpineBoundaryChained.nil 2))
    (SpineBoundaryChained.cons stringWidthTelescopeProbeCapAtom rfl
      (SpineBoundaryChained.cons stringWidthTelescopeProbeCupAtom rfl (SpineBoundaryChained.nil 2)))
    (SpineBoundaryChained.cons stringWidthTelescopeProbeCapAtom rfl
      (SpineBoundaryChained.cons stringWidthTelescopeProbeCupAtom rfl (SpineBoundaryChained.nil 2)))
    (SpineBoundaryWordChained.cons stringWidthTelescopeProbeCapAtom rfl (SpineBoundaryWordChained.nil _))
    (SpineBoundaryWordChained.cons stringWidthTelescopeProbeCapAtom rfl (SpineBoundaryWordChained.nil _))
    (SpineBoundaryWordChained.cons stringWidthTelescopeProbeCupAtom rfl (SpineBoundaryWordChained.nil _))
    (SpineBoundaryWordChained.cons stringWidthTelescopeProbeCupAtom rfl (SpineBoundaryWordChained.nil _))
    rfl stringSurvivorTopTotal_mixedValley_isZero rfl

/-- ★ **The probe valley genuinely has mid-width `0`.**  A machine-checked (`decide`) cross-check that the cap `ε`
consumes both bottom wires, so the cup `η'` runs from the width-`0` mid-boundary — confirming the producer fires on
the genuine mid-zero domain, not a degenerate width. -/
theorem stringMidZeroValleyProducer_probe_midWidthIsZero :
    (processSpine ⟨List.range 2, [], 2, 0⟩ [stringWidthTelescopeProbeCapAtom]).openWires.length = 0 := by
  decide

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the mid-width-`0` whole-valley string producer is SHIPPED, gate inlined, zero-axiom (FC-3
r36).**  `stringMidZeroValleysWithEqualMatching_spineTraceEquiv` — the string clone of the walking-adjunction
`midZeroValleysWithEqualMatching_spineTraceEquiv`, at the walking ADJOINT-TRIPLE signature, with the r35 mid-`0`
cup reconstruction `stringMidZeroCupBlockReconstruct_holds` DISCHARGED and INLINED (not a gate hypothesis).  Two
valleys `capBlock ++ cupBlock` (pure cap, pure cup, boundary-chained, POSITIVE bottom count, mid-width `0`) with
EQUAL whole-boundary `matchingOf` are `SpineTraceEquiv`:

  * the cap blocks agree (`stringSameWholeMatching_capBlockMatchingEq`), converted to the cap `diagram` agreement
    (`arcDiagram_eq_matching` at the positive cap width);
  * both mid-widths are `0` (`stringSurvivorTopTotal_eq_midWidth` + the mid-`0` witness), giving the cap length
    agreement (`stringCapLength_eq_of_midWidth_eq`);
  * the cup blocks agree at width `0` (the inlined `stringMidZeroCupBlockReconstruct_holds` fed through
    `stringSameWholeMatching_cupBlockMatchingEq`);

then the word-threaded block reassembly `stringMidZeroSameMatchingValleys_spineTraceEquiv` (r27) closes.  The two
string sorts thread a boundary WORD (the r17 precedent): the producer takes `capWord`/`midWord` + the four
`SpineBoundaryWordChained` chains + the shared `spineListTopWord` (`cupTopWordEq`) as hypotheses, threading them to
the reassembly's cap/cup sorts.  The truth-probe `stringMidZeroValleyProducer_firesOnMixedValley` fires the WHOLE
producer end-to-end on the genuine mixed valley `[ε] ++ [η']` at `tip` (`bottomCount = 2`, mid-width `0`), and the
`decide` cross-check pins the mid-width to the concrete `0`, so the fire is not vacuous.

  What this does NOT flip (honestly): `StringMidZeroValleyTraceEquiv` (`StringValleyDegenerateSplit`) stays
  UNINHABITED.  This producer is the BLOCK-level headline — it takes the boundary WORDS as hypotheses (as the
  reassembly requires).  The cell-level reducer that inhabits `StringMidZeroValleyTraceEquiv` must DERIVE those
  words from the `RawTwoCellExpr` valley: block-split the valley, peel `capWord := sourcePath` off the whole
  word chain (`spineBoundaryWordChained_prefix_ofAppend`), and — the genuine word-threading delta — exhibit a
  SHARED `midWord` for the two parallel cap blocks.  At mid-width `0` both cap blocks' top words
  `spineListTopWord sourcePath capBlockFirst` and `…capBlockSecond` are length-`0` paths (`overallSource ⟶
  overallTarget`), hence both the unique nil path, hence equal — but proving
  `spineListTopWord sourcePath capBlockFirst = spineListTopWord sourcePath capBlockSecond` needs the
  (still un-shipped) top-word-length = mid-width bridge plus length-`0` `ModalityPath` uniqueness, which the
  walking-adjunction cell reducer sidesteps entirely (its reassembly is un-word-threaded).  That shared-`midWord`
  brick is the r37 target.  So `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) and
  `fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) stay `false`.  This round flips ONLY this NEW marker:
  the mid-zero producer is assembled and gate-inlined at the block level.  `= true`. -/
def fxString_hasMidZeroValleyProducer : Bool := true

end FX1Poly.Polygraph
