import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCupTransfer
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCapSpine
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupSortComplete
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapSortComplete
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcTailsCancelAssembly
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineTraceAppendCongruence

/-! # ValleyMatchingSpineTraceEquiv — Piece II of the fib-3 gate, assembled modulo the two 2a residuals

The fib-3 existence route needs, for a valley `capBlock ++ cupBlock`, that two valleys with EQUAL boundary
matching are `SpineTraceEquiv`.  The block-level `matchingOf`/`diagram` equality feeds the two shipped
pure-block sorts (`pureCupSpine_sort` / `pureCapSpine_sort`), which want the FULL arc-structure equality of the
block.  The tails-cancel bricks (`pureCupTailsCancel_ofDiagramAndInternalCup`, and its cap dual built here)
reconstruct that full arc equality from the block `diagram` agreement PLUS the per-port internal turnback counts;
the free legs (total cup/cap counts, and the "opposite" internal count which vanishes on a pure block) are
supplied here.

This file lands:

  * the CAP-SIDE free legs, mirroring the shipped cup-side (`ArcPureCupTransfer`):
    - `pureCapSpine_internalCupCounts_eq_replicate` — a pure-cap spine has NO cup events
      (`cupEventNodes = []`), so its `internalCupCounts` vector is uniformly zero;
    - `pureCapSpines_internalCupCountsAgree_ofDiagram` — two pure-cap spines whose `diagram`s agree (hence whose
      `topCount = openWires.length` agree) carry equal `internalCupCounts` vectors (both `List.replicate total 0`);
    - `pureCapTailsCancel_ofDiagramAndInternalCap` — the cap dual of the shipped cup tails-cancel: for equal-length
      pure-cap spines, `diagram` + `internalCapCounts` agreement reconstructs the full arc-structure equality.

  * ★ `sameMatchingValleys_spineTraceEquiv` — Piece II, assembled: given two valleys `capBlock ++ cupBlock`
    with per-block `diagram` agreement and per-block length agreement (both consequences of block `matchingOf`
    equality via `arcDiagram_eq_matching`), and given the TWO residual per-port internal-count agreements
    (the cup block's `internalCupCounts`, the cap block's `internalCapCounts` — each a function of the `diagram`
    on a pure block, the standing "2a" characterizations), the two valleys are `SpineTraceEquiv`.  Everything
    other than the two named residuals is discharged: the cap-side internal-count free leg, the cup/cap
    tails-cancels, the two pure-block sorts, and the two-sided append congruence.

Raw Lean 4 + Init; structural / fuel recursion, no `omega` / `simp`-AC / `WellFounded.fix`.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range / list plumbing (per-file copies, following the codebase pattern) -/

/-- The range-loop's length is the count plus the seed length — hand-rolled (core `List.length_range`
leaks `propext` in this Init-only setting). -/
private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

/-- `(List.range count).length = count` — hand-rolled off `rangeLoopLength`. -/
private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

/-- A list of length zero is nil — a `noConfusion` peel, staying `propext`-free. -/
private theorem listEqNilOfLengthZero {carrier : Type _} :
    (elems : List carrier) → elems.length = 0 → elems = []
  | [], _ => rfl
  | _ :: _, lengthZero => Nat.noConfusion lengthZero

/-- Mapping a constantly-zero function over any list yields `List.replicate` of zeros — structural. -/
private theorem mapConst0EqReplicate {carrier : Type _} (weightOf : carrier → Nat)
    (allZero : ∀ elem, weightOf elem = 0) :
    (elems : List carrier) → elems.map weightOf = List.replicate elems.length 0
  | [] => rfl
  | headElem :: restElems => by
      show weightOf headElem :: restElems.map weightOf = List.replicate (restElems.length + 1) 0
      rw [allZero headElem, mapConst0EqReplicate weightOf allZero restElems]
      rfl

/-! ## The count reflections (re-derived locally, off the shared event-node length lemmas) -/

/-- The arc structure's total `cupCount` reflects the boundary-independent cup-atom count. -/
private theorem cupCountReflect {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom signature sourceMode targetMode)) :
    (arcStructureOfSpineList bottomCount atoms).cupCount = cupAtomCount atoms := by
  show (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      atoms).cupEventNodes.length = cupAtomCount atoms
  rw [processArcSpine_cupEventNodes_length]
  exact Nat.zero_add _

/-- The arc structure's total `capCount` reflects the boundary-independent cap-atom count. -/
private theorem capCountReflect {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom signature sourceMode targetMode)) :
    (arcStructureOfSpineList bottomCount atoms).capCount = capAtomCount atoms := by
  show (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      atoms).capEventNodes.length = capAtomCount atoms
  rw [processArcSpine_capEventNodes_length]
  exact Nat.zero_add _

/-! ## The cap-side internal CUP-count free leg (dual of the shipped cup-side cap leg) -/

/-- The arc `internalCupCounts` of a state with no cup events is `List.replicate total 0` — the per-port
turnback scan reads `countEventsInRoot … [] = 0` at every boundary port.  Dual of the shipped
`extractArc_internalCapCounts_eq_replicate_of_capNil`. -/
private theorem extractArc_internalCupCounts_eq_replicate_of_cupNil
    (bottomCount : Nat) (state : ArcWireState) (cupNil : state.cupEventNodes = []) :
    (extractArc bottomCount state).internalCupCounts
      = List.replicate (bottomCount + state.openWires.length) 0 := by
  have expandMap : (extractArc bottomCount state).internalCupCounts
      = (List.range (bottomCount + state.openWires.length)).map
          (internalEventCountAt state.links (List.range bottomCount ++ state.openWires) []) := by
    dsimp only [extractArc]
    rw [cupNil]
  have allZero : ∀ index,
      internalEventCountAt state.links (List.range bottomCount ++ state.openWires) [] index = 0 :=
    fun _ => rfl
  rw [expandMap, mapConst0EqReplicate _ allZero, rangeLength]

/-- ★ **A pure-cap spine's internal cup-counts vanish.**  Every atom is a cap, so the arc fold records no cup
events (`cupEventNodes = []`, via `cupAtomCount_ofAllCapArity` and the boundary-independent `cupCount`
reflection), and the per-port cup-turnback scan reads zero at every boundary port.  So the whole
`internalCupCounts` vector is `List.replicate total 0`.  The cap-block analog of the shipped
`pureCupSpine_internalCapCounts_eq_replicate`. -/
theorem pureCapSpine_internalCupCounts_eq_replicate
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCap : AllCapArity atoms) :
    (arcStructureOfSpineList bottomCount atoms).internalCupCounts
      = List.replicate
          (bottomCount
            + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                atoms).openWires.length)
          0 := by
  have cupZero : cupAtomCount atoms = 0 := cupAtomCount_ofAllCapArity atoms pureCap
  have cupNil :
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          atoms).cupEventNodes = [] := by
    apply listEqNilOfLengthZero
    rw [processArcSpine_cupEventNodes_length]
    show (0 : Nat) + cupAtomCount atoms = 0
    rw [Nat.zero_add]
    exact cupZero
  exact extractArc_internalCupCounts_eq_replicate_of_cupNil bottomCount
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms) cupNil

/-- The arc structure's `diagram.topCount` IS the final open-wire count — a definitional projection through
`extractDiagram`. -/
private theorem topCount_eq_openWiresLength
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    (arcStructureOfSpineList bottomCount atoms).diagram.topCount
      = (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          atoms).openWires.length := rfl

/-- ★ **Equal-diagram pure-cap spines have agreeing internal cup-counts.**  Both spines' `internalCupCounts`
vectors are `List.replicate total 0` (`pureCapSpine_internalCupCounts_eq_replicate`), and their `diagram`
agreement forces `topCount = openWires.length` agreement, hence equal `total` — so the two vectors coincide.
This is the cap block's cup-count free leg, phrased on the block `diagram` datum the valley hypothesis carries. -/
theorem pureCapSpines_internalCupCountsAgree_ofDiagram
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (firstList secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstPureCap : AllCapArity firstList) (secondPureCap : AllCapArity secondList)
    (diagramAgree : (arcStructureOfSpineList bottomCount firstList).diagram
      = (arcStructureOfSpineList bottomCount secondList).diagram) :
    (arcStructureOfSpineList bottomCount firstList).internalCupCounts
      = (arcStructureOfSpineList bottomCount secondList).internalCupCounts := by
  have openWiresAgree :
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          firstList).openWires.length
        = (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          secondList).openWires.length := by
    rw [← topCount_eq_openWiresLength bottomCount firstList,
      ← topCount_eq_openWiresLength bottomCount secondList]
    exact congrArg DiagramType.topCount diagramAgree
  rw [pureCapSpine_internalCupCounts_eq_replicate bottomCount firstList firstPureCap,
    pureCapSpine_internalCupCounts_eq_replicate bottomCount secondList secondPureCap, openWiresAgree]

/-! ## The cap tails-cancel from its two genuine residuals (dual of the shipped cup tails-cancel) -/

/-- ★ **The pure-cap base-case peel from its two genuine residuals.**  For equal-length pure-cap spines, the
full arc equality `arc(firstList) = arc(secondList)` follows from just the boundary `diagram` agreement and the
`internalCapCounts` agreement: the two total count legs are supplied internally (`cupCount = 0` on both,
`capCount = length` on both, via the reflections and the pure-cap tallies) and the `internalCupCounts` leg by
`pureCapSpines_internalCupCountsAgree_ofDiagram` (a pure-cap spine has no cup events).  The cap dual of the
shipped `pureCupTailsCancel_ofDiagramAndInternalCup`. -/
theorem pureCapTailsCancel_ofDiagramAndInternalCap
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (firstList secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstPureCap : AllCapArity firstList) (secondPureCap : AllCapArity secondList)
    (lengthEq : firstList.length = secondList.length)
    (diagramAgree : (arcStructureOfSpineList bottomCount firstList).diagram
        = (arcStructureOfSpineList bottomCount secondList).diagram)
    (internalCapCountsAgree :
      (arcStructureOfSpineList bottomCount firstList).internalCapCounts
        = (arcStructureOfSpineList bottomCount secondList).internalCapCounts) :
    arcStructureOfSpineList bottomCount firstList
      = arcStructureOfSpineList bottomCount secondList := by
  refine fullArcStructure_eq_of_fields diagramAgree ?_ ?_ ?_ internalCapCountsAgree
  · rw [cupCountReflect bottomCount firstList, cupCountReflect bottomCount secondList,
      cupAtomCount_ofAllCapArity firstList firstPureCap,
      cupAtomCount_ofAllCapArity secondList secondPureCap]
  · rw [capCountReflect bottomCount firstList, capCountReflect bottomCount secondList,
      capAtomCount_ofAllCapArity firstList firstPureCap,
      capAtomCount_ofAllCapArity secondList secondPureCap, lengthEq]
  · exact pureCapSpines_internalCupCountsAgree_ofDiagram bottomCount firstList secondList
      firstPureCap secondPureCap diagramAgree

/-! ## ★ Piece II — the valley trace equivalence, assembled modulo the two 2a residuals -/

/-- ★ **Piece II (valley matching ⇒ trace equivalence), assembled.**  Two valleys `capBlock ++ cupBlock` with
per-block boundary `diagram` agreement and per-block length agreement — both consequences of block `matchingOf`
equality (`arcDiagram_eq_matching`) — are `SpineTraceEquiv`, GIVEN the two per-port internal-count agreements:
the cup block's `internalCupCounts` and the cap block's `internalCapCounts`.  Each of those two is the standing
"2a" characterization (on a pure block the internal count of the block's own turnback kind is a function of the
`diagram`).  Everything else is discharged: the cap block's cup-count free leg
(`pureCapSpines_internalCupCountsAgree_ofDiagram`), the cup/cap tails-cancels reconstructing the full block arc
equality, the two pure-block completeness sorts (`pureCupSpine_sort` / `pureCapSpine_sort`), and the two-sided
append congruence (`spineTraceEquiv_appendCongr`). -/
theorem sameMatchingValleys_spineTraceEquiv
    {overallSource overallTarget : adjunctionGraph.Mode}
    (capBottomCount cupBottomCount : Nat)
    (capBlockFirst capBlockSecond cupBlockFirst cupBlockSecond :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (capPureFirst : AllCapArity capBlockFirst) (capPureSecond : AllCapArity capBlockSecond)
    (cupPureFirst : AllCupArity cupBlockFirst) (cupPureSecond : AllCupArity cupBlockSecond)
    (capChainedFirst : SpineBoundaryChained capBottomCount capBlockFirst)
    (capChainedSecond : SpineBoundaryChained capBottomCount capBlockSecond)
    (cupChainedFirst : SpineBoundaryChained cupBottomCount cupBlockFirst)
    (cupChainedSecond : SpineBoundaryChained cupBottomCount cupBlockSecond)
    (cupBottomPositive : 0 < cupBottomCount)
    (capLengthEq : capBlockFirst.length = capBlockSecond.length)
    (cupLengthEq : cupBlockFirst.length = cupBlockSecond.length)
    (capDiagramAgree : (arcStructureOfSpineList capBottomCount capBlockFirst).diagram
      = (arcStructureOfSpineList capBottomCount capBlockSecond).diagram)
    (cupDiagramAgree : (arcStructureOfSpineList cupBottomCount cupBlockFirst).diagram
      = (arcStructureOfSpineList cupBottomCount cupBlockSecond).diagram)
    (capInternalCapCountsAgree :
      (arcStructureOfSpineList capBottomCount capBlockFirst).internalCapCounts
        = (arcStructureOfSpineList capBottomCount capBlockSecond).internalCapCounts)
    (cupInternalCupCountsAgree :
      (arcStructureOfSpineList cupBottomCount cupBlockFirst).internalCupCounts
        = (arcStructureOfSpineList cupBottomCount cupBlockSecond).internalCupCounts) :
    SpineTraceEquiv adjunctionModeSignature
      (capBlockFirst ++ cupBlockFirst) (capBlockSecond ++ cupBlockSecond) := by
  have capArcEqual : arcStructureOfSpineList capBottomCount capBlockFirst
      = arcStructureOfSpineList capBottomCount capBlockSecond :=
    pureCapTailsCancel_ofDiagramAndInternalCap capBottomCount capBlockFirst capBlockSecond
      capPureFirst capPureSecond capLengthEq capDiagramAgree capInternalCapCountsAgree
  have cupArcEqual : arcStructureOfSpineList cupBottomCount cupBlockFirst
      = arcStructureOfSpineList cupBottomCount cupBlockSecond :=
    pureCupTailsCancel_ofDiagramAndInternalCup cupBottomCount cupBlockFirst cupBlockSecond
      cupPureFirst cupPureSecond cupLengthEq cupDiagramAgree cupInternalCupCountsAgree
  have capTrace : SpineTraceEquiv adjunctionModeSignature capBlockFirst capBlockSecond :=
    pureCapSpine_sort capBottomCount capBlockFirst capBlockSecond capChainedFirst capChainedSecond
      capPureFirst capPureSecond capArcEqual
  have cupTrace : SpineTraceEquiv adjunctionModeSignature cupBlockFirst cupBlockSecond :=
    pureCupSpine_sort cupBottomCount cupBlockFirst cupBlockSecond cupChainedFirst cupChainedSecond
      cupPureFirst cupPureSecond cupBottomPositive cupArcEqual
  exact spineTraceEquiv_appendCongr capTrace cupTrace

/-! ## Honesty marker -/

/-- **Honesty marker — Piece II is ASSEMBLED modulo exactly the two 2a residuals.**
`sameMatchingValleys_spineTraceEquiv` proves that two valleys `capBlock ++ cupBlock` with block-level `diagram`
and length agreement are `SpineTraceEquiv`, GIVEN two residual inputs: the cup block's `internalCupCounts`
agreement and the cap block's `internalCapCounts` agreement.  Each is the standing "2a" per-port
characterization — on a pure block the internal count of the block's OWN turnback kind is a function of the
boundary `diagram` (`partner`).  The OPPOSITE internal count vanishes on a pure block and is discharged here
(cup side shipped in `ArcPureCupTransfer`, cap side `pureCapSpines_internalCupCountsAgree_ofDiagram`); the full
block arc equality is reconstructed by the tails-cancels; the pure-block completeness sorts and the append
congruence close the assembly.  What this marker does NOT claim: the two 2a characterizations themselves
(recovering `internalCupCounts` / `internalCapCounts` from `partner` on a pure block), nor the valley-append
`matchingOf`-split that would derive the per-block `diagram`/length agreements from a whole-valley `matchingOf`
equality.  No gate flag is flipped — Piece I (valley descent) remains open.  `= true`. -/
def fxMode_hasValleyMatchingSpineTraceEquivAssembly : Bool := true

end FX1Poly.Polygraph
