import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCapTopPartner
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupRestrict
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyAppendSplit

/-! # ValleyCupAssembly — the cup half of the valley-append split + the clean whole-valley theorem
(Piece II tail, final assembly)

The cap half of the valley-append split is fully shipped: `capRestrict_reconstructs` (the cap block's own
diagram is `capRestrict` of the whole valley's diagram) and `sameWholeMatching_capBlockMatchingEq` (equal
wholes force equal cap blocks, by `congrArg capRestrict`).  This file lands the DUAL cup half and the clean
whole-valley `SpineTraceEquiv` theorem — as verified WIRING gated on the single un-shipped lemma
`cupRestrict_reconstructs` (its `partner` field; see the ValleyCupRestrict honesty marker and the residual note
below).  Passing that one reconstruction equation as a hypothesis, everything above it is mechanical and CLOSED:

  * ★ `sameWholeMatching_cupBlockMatchingEq` — the DUAL of `sameWholeMatching_capBlockMatchingEq`: from the two
    cup-block reconstruction equations and a whole-valley `matchingOf` equality, the two cup blocks have equal
    `matchingOf` (each at its OWN mid-width).  Pure `congrArg cupRestrict` sandwich — the cup block's own diagram
    is a FUNCTION (`cupRestrict`) of the whole valley's diagram, so equal wholes force equal cup blocks.

  * ★ `valleyAppend_split` — BOTH per-block `matchingOf` equalities from ONE whole-valley equality: the cap half
    (shipped `sameWholeMatching_capBlockMatchingEq`) paired with the cup half above.  This is the topological
    factorization the Piece-I route describes: caps only remove bottom wires, cups only add top wires, so a whole
    equality splits into the two block equalities.

  * ★ `valleysWithEqualMatching_spineTraceEquiv` — the clean whole-valley theorem: two valleys `capBlock ++
    cupBlock` with EQUAL whole-boundary `matchingOf` are `SpineTraceEquiv`.  Assembles the two per-block
    equalities (with the two mid-widths aligned via `survivorTopTotal_eq_midWidth` + `congrArg survivorTopTotal`)
    and invokes the shipped Piece-II interface `valleysWithBlockMatchingEq_spineTraceEquiv`.

## The one residual — `cupRestrict_reconstructs`'s `partner` field (the suffix-rename hard node)

The three theorems here take `cupRestrict_reconstructs` (equivalently, its `partner` field) as a hypothesis
because it is a GENUINE new hard node, verified UN-SHIPPED (four honesty markers concur: ValleyCupRestrict,
MatchingRenameSupport, MatchingCupWindowScanSplit, CupShiftReranking).  The cap block is the valley's PREFIX, so
`capState` IS the intermediate state of the whole run (`processSpine_append`) and every cap partner leg is a
SAME-SEED comparison.  The cup block is the valley's SUFFIX: its own matching `matchingOf midWidth cupBlock` runs
from the from-scratch seed `⟨range midWidth, [], midWidth, 0⟩` (bottoms `0 … midWidth-1`, legs `midWidth + k`,
empty base links), whereas its action inside the whole valley runs from `capState` (bottoms the SCATTERED survivor
values `< bc`, legs `bc + k`, cap links present).  These two runs are related by a COMPOSITE seed rename — a
survivor SCATTER below `midWidth` (a genuine permutation, NOT a shift) COMPOSED with a leg shift `+ (bc − midWidth)`
above — over a NON-EMPTY base link list.  The shipped fresh-shift equivariance
(`runMatchingCell_wireView_freshShift`) requires a PURE `freshShiftAbove`-related seed pair, which the cup seeds
are NOT (the bottom scatter breaks it, and only the wire view is covered — not the component/`links` view the
partner field reads).  The base correspondence `componentView_ofFreshRename` and the single-cup scan transport
`findPartnerScan_range_cupWindowSplit` are shipped, but the MULTI-CUP component fold of the composite rename across
the whole cup block is un-shipped — a multi-session brick, not a one-file port.  No gate flag is flipped.

Raw Lean 4 + Init; pure equational assembly, no `omega` / `simp`-AC / `WellFounded.fix`.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The cup half of the valley-append split (gated on the reconstruction) -/

/-- ★ **The cup-block half of the valley-append split.**  Two valleys `capBlock ++ cupBlock` with EQUAL whole
`matchingOf` have EQUAL cup-block `matchingOf` (each read at its OWN mid-width `capState.openWires.length`).  The
DUAL of the shipped `sameWholeMatching_capBlockMatchingEq`: derived by `congrArg cupRestrict` over the whole
equality, sandwiched between the two cup reconstruction equations `cupReconstructsFirst`/`cupReconstructsSecond`
(each `matchingOf midWidth cupBlock = cupRestrict (matchingOf bc V)`).  The cup block's own diagram is a FUNCTION
(`cupRestrict`) of the whole valley's diagram, so equal wholes force equal cup blocks.  Gated on
`cupRestrict_reconstructs` (its `partner` field, the suffix-rename hard node). -/
theorem sameWholeMatching_cupBlockMatchingEq
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (capBlockFirst capBlockSecond cupBlockFirst cupBlockSecond :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (cupReconstructsFirst :
      matchingOfSpineList
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockFirst
        = cupRestrict (matchingOfSpineList bottomCount (capBlockFirst ++ cupBlockFirst)))
    (cupReconstructsSecond :
      matchingOfSpineList
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length cupBlockSecond
        = cupRestrict (matchingOfSpineList bottomCount (capBlockSecond ++ cupBlockSecond)))
    (wholeEq : matchingOfSpineList bottomCount (capBlockFirst ++ cupBlockFirst)
      = matchingOfSpineList bottomCount (capBlockSecond ++ cupBlockSecond)) :
    matchingOfSpineList
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockFirst
      = matchingOfSpineList
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length cupBlockSecond :=
  cupReconstructsFirst.trans ((congrArg cupRestrict wholeEq).trans cupReconstructsSecond.symm)

/-! ## The full valley-append split — BOTH per-block equalities from one whole equality -/

/-- ★ **The valley-append split.**  From a whole-valley `matchingOf` equality, derive BOTH per-block `matchingOf`
equalities: the cap blocks agree (at bottom count `bc`) and the cup blocks agree (each at its own mid-width).  The
cap half is the shipped `sameWholeMatching_capBlockMatchingEq` (`congrArg capRestrict`); the cup half is
`sameWholeMatching_cupBlockMatchingEq` (`congrArg cupRestrict`).  This is the topological factorization: caps
remove only bottom wires, cups add only top wires, so a whole equality splits into the two block equalities.  Gated
on the two cup reconstruction equations. -/
theorem valleyAppend_split
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
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
    (cupReconstructsFirst :
      matchingOfSpineList
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockFirst
        = cupRestrict (matchingOfSpineList bottomCount (capBlockFirst ++ cupBlockFirst)))
    (cupReconstructsSecond :
      matchingOfSpineList
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length cupBlockSecond
        = cupRestrict (matchingOfSpineList bottomCount (capBlockSecond ++ cupBlockSecond)))
    (wholeEq : matchingOfSpineList bottomCount (capBlockFirst ++ cupBlockFirst)
      = matchingOfSpineList bottomCount (capBlockSecond ++ cupBlockSecond)) :
    matchingOfSpineList bottomCount capBlockFirst = matchingOfSpineList bottomCount capBlockSecond
    ∧ matchingOfSpineList
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockFirst
      = matchingOfSpineList
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length cupBlockSecond :=
  ⟨sameWholeMatching_capBlockMatchingEq bottomCount bottomPositive capBlockFirst capBlockSecond cupBlockFirst
      cupBlockSecond capPureFirst capPureSecond cupPureFirst cupPureSecond cupChainedFirst cupChainedSecond
      wholeChainedFirst wholeChainedSecond wholeEq,
    sameWholeMatching_cupBlockMatchingEq bottomCount capBlockFirst capBlockSecond cupBlockFirst cupBlockSecond
      cupReconstructsFirst cupReconstructsSecond wholeEq⟩

/-! ## The clean whole-valley theorem -/

/-- ★ **The clean whole-valley `SpineTraceEquiv`.**  Two valleys `capBlock ++ cupBlock` (pure cap prefix, pure cup
suffix, boundary-chained, positive bottom count and mid-width, equal block lengths) whose WHOLE-boundary
`matchingOf` agree are `SpineTraceEquiv`.  Assembles the valley-append split: the cap blocks agree (shipped cap
half), the cup blocks agree (gated cup half) after aligning the two mid-widths via `survivorTopTotal_eq_midWidth`
(both equal `survivorTopTotal` of the common whole diagram, so `congrArg survivorTopTotal wholeEq` collapses them),
then the shipped Piece-II interface `valleysWithBlockMatchingEq_spineTraceEquiv` closes.  This is the top of the
Piece-II pyramid — gated only on `cupRestrict_reconstructs`. -/
theorem valleysWithEqualMatching_spineTraceEquiv
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
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
    (midPositive : 0 <
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length)
    (capLengthEq : capBlockFirst.length = capBlockSecond.length)
    (cupLengthEq : cupBlockFirst.length = cupBlockSecond.length)
    (cupReconstructsFirst :
      matchingOfSpineList
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockFirst
        = cupRestrict (matchingOfSpineList bottomCount (capBlockFirst ++ cupBlockFirst)))
    (cupReconstructsSecond :
      matchingOfSpineList
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length cupBlockSecond
        = cupRestrict (matchingOfSpineList bottomCount (capBlockSecond ++ cupBlockSecond)))
    (wholeEq : matchingOfSpineList bottomCount (capBlockFirst ++ cupBlockFirst)
      = matchingOfSpineList bottomCount (capBlockSecond ++ cupBlockSecond)) :
    SpineTraceEquiv adjunctionModeSignature
      (capBlockFirst ++ cupBlockFirst) (capBlockSecond ++ cupBlockSecond) := by
  -- The two cap prefixes are boundary-chained (whole valley chaining restricts to the prefix).
  have capChainedFirst : SpineBoundaryChained bottomCount capBlockFirst :=
    spineBoundaryChained_prefix_ofAppend capBlockFirst cupBlockFirst bottomCount wholeChainedFirst
  have capChainedSecond : SpineBoundaryChained bottomCount capBlockSecond :=
    spineBoundaryChained_prefix_ofAppend capBlockSecond cupBlockSecond bottomCount wholeChainedSecond
  -- The two mid-widths agree: both equal `survivorTopTotal` of the (equal) whole diagrams.
  have midEq :
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length
        = (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length :=
    (survivorTopTotal_eq_midWidth bottomCount bottomPositive capBlockFirst cupBlockFirst capPureFirst
        cupPureFirst cupChainedFirst).symm.trans
      ((congrArg survivorTopTotal wholeEq).trans
        (survivorTopTotal_eq_midWidth bottomCount bottomPositive capBlockSecond cupBlockSecond capPureSecond
          cupPureSecond cupChainedSecond))
  -- The cap-block matchings agree (shipped cap half).
  have capMatchEq : matchingOfSpineList bottomCount capBlockFirst
      = matchingOfSpineList bottomCount capBlockSecond :=
    sameWholeMatching_capBlockMatchingEq bottomCount bottomPositive capBlockFirst capBlockSecond cupBlockFirst
      cupBlockSecond capPureFirst capPureSecond cupPureFirst cupPureSecond cupChainedFirst cupChainedSecond
      wholeChainedFirst wholeChainedSecond wholeEq
  -- The cup-block matchings agree (gated cup half), then realign the second to the first mid-width.
  have cupMatchEqGated :
      matchingOfSpineList
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockFirst
        = matchingOfSpineList
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length cupBlockSecond :=
    sameWholeMatching_cupBlockMatchingEq bottomCount capBlockFirst capBlockSecond cupBlockFirst cupBlockSecond
      cupReconstructsFirst cupReconstructsSecond wholeEq
  have cupMatchEq :
      matchingOfSpineList
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockFirst
        = matchingOfSpineList
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockSecond := by
    rw [cupMatchEqGated, midEq]
  have cupChainedSecondAligned : SpineBoundaryChained
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockSecond := by
    rw [midEq]; exact cupChainedSecond
  exact valleysWithBlockMatchingEq_spineTraceEquiv bottomCount
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length
    capBlockFirst capBlockSecond cupBlockFirst cupBlockSecond
    capPureFirst capPureSecond cupPureFirst cupPureSecond
    capChainedFirst capChainedSecond cupChainedFirst cupChainedSecondAligned
    bottomPositive midPositive capLengthEq cupLengthEq capMatchEq cupMatchEq

/-! ## Honesty marker -/

/-- **Honesty marker — the cup half of the valley-append split + the clean whole-valley theorem are ASSEMBLED,
gated on the single un-shipped lemma `cupRestrict_reconstructs`.**

Landed here, all zero-axiom:

  * `sameWholeMatching_cupBlockMatchingEq` — the DUAL of the shipped `sameWholeMatching_capBlockMatchingEq`:
    `congrArg cupRestrict` over a whole-valley equality forces the two cup blocks' `matchingOf` equal (each at its
    own mid-width), given the two cup reconstruction equations.

  * `valleyAppend_split` — BOTH per-block `matchingOf` equalities from one whole equality (cap half shipped, cup
    half above).

  * `valleysWithEqualMatching_spineTraceEquiv` — the clean whole-valley `SpineTraceEquiv`: assembles the two
    per-block equalities (mid-widths aligned via `survivorTopTotal_eq_midWidth`) into the shipped Piece-II
    interface `valleysWithBlockMatchingEq_spineTraceEquiv`.

The three take `cupRestrict_reconstructs` (its `partner` field) as a HYPOTHESIS because it is a GENUINE new hard
node, verified UN-SHIPPED — the suffix seed-rename over the cup block is a COMPOSITE survivor-scatter (a
permutation) COMPOSED with a leg shift, over a NON-EMPTY base link list, which lands OUTSIDE the shipped pure
`freshShiftAbove` fresh-shift equivariance (wire view only) and OUTSIDE the shipped single-cup scan transport; the
multi-cup component fold of that composite rename is a multi-session brick.  Four honesty markers concur
(ValleyCupRestrict, MatchingRenameSupport, MatchingCupWindowScanSplit, CupShiftReranking).  fib-3 also has the
second open beam (Piece I, `MatchingReductsShareSpineTrace`, #1996), so `convOfMapEq` stays gated regardless.  No
gate flag is flipped.  `= true`. -/
def fxMode_hasValleyCupAssemblyGatedOnReconstruction : Bool := true

end FX1Poly.Polygraph
