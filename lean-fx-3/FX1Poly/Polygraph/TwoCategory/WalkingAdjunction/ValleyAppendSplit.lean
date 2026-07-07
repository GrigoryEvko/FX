import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyMatchingSpineTraceEquiv
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcMatchViewFold
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingVcompLeftCongruence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFoldCongruence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineArityDiscipline
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingViewStability
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRightPadSeed

/-! # ValleyAppendSplit — Piece I of the fib-3 gate: the valley-append `matchingOf` split

The fib-3 existence route needs, for a valley `capBlock ++ cupBlock`, that two valleys with EQUAL whole-boundary
`matchingOf` are `SpineTraceEquiv`.  Piece II (`sameMatchingValleys_spineTraceEquiv`) already discharges the tail
from PER-BLOCK `diagram` + length agreements.  Piece I is the missing entry: derive those per-block agreements
from a WHOLE-valley `matchingOf` equality.

The route (restriction functions on the boundary `DiagramType`): a valley `capBlock ++ cupBlock` at bottom count
`bc` factors topologically — the cap block only REMOVES bottom wires (each cap is a bottom-bottom arc; the
un-capped `midWidth` wires pass through), the cup block only ADDS top wires (each cup is a top-top arc, run from
the mid-width boundary up).  So the whole matching PARTITIONS: the bottom-bottom partner pairs + loop count are
the cap block's own matching (the cup block leaves them invariant since cups only add fresh top arcs — the
before/after cup boundary-neutrality `stepCup_isSameComponent_boundaryReads`), and the top-top pairs are the cup
block's matching shifted to `midWidth`.  Restriction functions `capRestrict` / `cupRestrict` on `DiagramType`
extract those two halves; the restriction lemmas prove each block's own `matchingOf` equals the corresponding
restriction of the whole; a `congrArg` over the restriction functions turns a whole equality into the two block
equalities; `arcDiagram_eq_matching` converts the block `matchingOf` equalities to the `.diagram` shape Piece II
consumes.

This file lands the parts that are genuinely closable with the shipped machinery, and marks honestly the residual
that is exactly the standing valley-descent beam (#2185):

  * ★ `processSpine_loops_ofAllCupArity` — a pure-cup block preserves the loop count of ANY processing state
    (cups never close a loop: `stepCup_loops`, folded over the cup block).
  * ★ `matchingOf_loops_split` — the LOOP leg of the restriction: the whole valley's loop count equals the cap
    block's loop count (`processSpine_append` + the cup block's loop-preservation).  Immediately: two valleys with
    equal whole `matchingOf` have equal cap-block loop counts.

Raw Lean 4 + Init; structural / fold recursion, no `omega` / `simp`-AC / `WellFounded.fix`.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The cup block preserves the loop count -/

/-- ★ **A pure-cup block preserves the loop count of any processing state.**  Every atom is a cup
(`AllCupArity`), so each `stepAtom` reduces to a `stepCup` (`stepAtom_ofCupArity`), and a cup never closes a loop
(`stepCup_loops` — the loop field is copied verbatim).  Folded over the whole cup block, the loop count is
untouched.  This is the loop half of the cup block's boundary-neutrality: run from the post-cap-block mid-state, a
cup block adds only fresh top arcs and leaves every closed loop the cap block already recorded. -/
theorem processSpine_loops_ofAllCupArity
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    (state : WireState) → (processSpine state atoms).loops = state.loops := by
  induction pureCup with
  | nil => intro state; rfl
  | cons hasCupDomArity hasCupCodArity _restAllCup restLoops =>
      rename_i headAtom rest
      intro state
      show (processSpine (stepAtom state headAtom) rest).loops = state.loops
      rw [restLoops (stepAtom state headAtom),
        stepAtom_ofCupArity state headAtom hasCupDomArity hasCupCodArity, stepCup_loops]

/-! ## The loop leg of the valley-append split -/

/-- ★ **The LOOP leg of the valley-append split.**  For a valley `capBlock ++ cupBlock` at bottom count `bc` whose
cup block is pure, the whole valley's loop count equals the cap block's loop count.  The fold splits over the
append (`processSpine_append`), and the cup block, run from the post-cap-block mid-state, preserves the loop count
(`processSpine_loops_ofAllCupArity`); the `DiagramType.loops` field is definitionally the state's loop count
(`extractDiagram`), so the whole and cap-block diagrams carry the same `loops`.  This is the `loops` component of
the cap-side restriction lemma — the piece that passes through `capRestrict` unchanged. -/
theorem matchingOf_loops_split
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (capBlock cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (cupPure : AllCupArity cupBlock) :
    (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).loops
      = (matchingOfSpineList bottomCount capBlock).loops := by
  show (processSpine { openWires := List.range bottomCount, links := [], nextFresh := bottomCount, loops := 0 }
        (capBlock ++ cupBlock)).loops
      = (processSpine { openWires := List.range bottomCount, links := [], nextFresh := bottomCount, loops := 0 }
        capBlock).loops
  rw [processSpine_append capBlock cupBlock
    { openWires := List.range bottomCount, links := [], nextFresh := bottomCount, loops := 0 }]
  exact processSpine_loops_ofAllCupArity cupBlock cupPure
    (processSpine { openWires := List.range bottomCount, links := [], nextFresh := bottomCount, loops := 0 }
      capBlock)

/-! ## The bottom-bottom component frame — cups preserve connectivity among the fixed bottom nodes

The bottom boundary ports `0 … bc-1` sit in the FIXED `List.range bc` prefix of `matchingBoundaryNodes`, never
touched by a cup (which only splices fresh legs into the open-wire suffix).  So a cup's join of its two fresh
legs cannot change the same-component relation between any two bottom nodes — the self before/after invariant
`stepCup_isSameComponent_boundaryReads` at bottom indices, where the boundary read IS the index
(`matchingBoundaryNodes_getAt_bottom`).  Folded over a pure-cup block, this gives the BOTTOM-BOTTOM component
frame: run from any conditioned mid-state, a cup block preserves same-component among the bottom nodes.  This is
the connectivity half of the cap-side restriction's boundary-neutrality (the recon's flagged before/after cup
invariant), reducing the cap restriction's remaining content to the through-strand re-ranking alone. -/

/-- A single cup preserves the same-component relation between two bottom nodes: the cup joins its two FRESH legs
(`stepCup_links`), which the self before/after invariant `stepCup_isSameComponent_boundaryReads` shows is
separated from every boundary read; at bottom indices the boundary read is the index itself
(`matchingBoundaryNodes_getAt_bottom`). -/
theorem stepCup_isSameComponent_bottom (bottomCount : Nat) (state : WireState)
    (conditions : MatchingSwapStateConditions bottomCount state)
    (position indexA indexB : Nat) (aBelow : indexA < bottomCount) (bBelow : indexB < bottomCount) :
    isSameComponent (stepCup state position).links indexA indexB
      = isSameComponent state.links indexA indexB := by
  rw [stepCup_links]
  have key := stepCup_isSameComponent_boundaryReads bottomCount state conditions indexA indexB
  rw [matchingBoundaryNodes_getAt_bottom bottomCount state indexA aBelow,
    matchingBoundaryNodes_getAt_bottom bottomCount state indexB bBelow] at key
  exact key

/-- ★ **The bottom-bottom component frame.**  Run from any conditioned mid-state, a pure-cup block preserves the
same-component relation between any two bottom nodes `< bottomCount`.  By induction on the `AllCupArity` witness:
each cup step is a `stepCup` (`stepAtom_ofCupArity`) that leaves bottom-node connectivity fixed
(`stepCup_isSameComponent_bottom`), and the conditions package is preserved along the fold
(`matchingSwapStateConditions_stepAtom`).  This is the connectivity half of the cap-side restriction lemma: the
cup block, appended after the cap block, leaves the cap block's bottom-bottom arcs invariant. -/
theorem processSpine_isSameComponent_bottom_ofAllCupArity
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    (state : WireState) → MatchingSwapStateConditions bottomCount state →
    ∀ indexA indexB, indexA < bottomCount → indexB < bottomCount →
      isSameComponent (processSpine state atoms).links indexA indexB
        = isSameComponent state.links indexA indexB := by
  induction pureCup with
  | nil => intro _ _ _ _ _ _; rfl
  | cons hasCupDomArity hasCupCodArity _restAllCup restFrame =>
      rename_i headAtom rest
      intro state conditions indexA indexB aBelow bBelow
      show isSameComponent (processSpine (stepAtom state headAtom) rest).links indexA indexB
        = isSameComponent state.links indexA indexB
      rw [restFrame (stepAtom state headAtom)
          (matchingSwapStateConditions_stepAtom bottomCount state headAtom conditions)
          indexA indexB aBelow bBelow,
        stepAtom_ofCupArity state headAtom hasCupDomArity hasCupCodArity,
        stepCup_isSameComponent_bottom bottomCount state conditions
          headAtom.leftContext.length indexA indexB aBelow bBelow]

/-! ## The arity bridges (pure-cap / pure-cup imply the generic cup/cap discipline)

`arcDiagram_eq_matching` (the `.diagram` = `matchingOf` bridge) wants the GENERIC cup/cap arity discipline
`SpineHasCupCapAtoms` (a `List.Mem` predicate).  A pure-cap or pure-cup block carries the STRUCTURAL
`AllCapArity` / `AllCupArity`; these bridges route between them so the block `matchingOf` equalities can be
converted to the `.diagram` shape Piece II consumes. -/

/-- A pure-cap block satisfies the generic cup/cap arity discipline (every atom is a cap, the right disjunct). -/
theorem spineHasCupCapAtoms_ofAllCapArity
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCap : AllCapArity atoms) : SpineHasCupCapAtoms atoms := by
  induction pureCap with
  | nil => intro probeAtom probeMem; nomatch probeMem
  | cons hasCapDomArity hasCapCodArity _restAllCap restHas =>
      exact spineHasCupCapAtoms_cons (Or.inr ⟨hasCapDomArity, hasCapCodArity⟩) restHas

/-- A pure-cup block satisfies the generic cup/cap arity discipline (every atom is a cup, the left disjunct). -/
theorem spineHasCupCapAtoms_ofAllCupArity
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) : SpineHasCupCapAtoms atoms := by
  induction pureCup with
  | nil => intro probeAtom probeMem; nomatch probeMem
  | cons hasCupDomArity hasCupCodArity _restAllCup restHas =>
      exact spineHasCupCapAtoms_cons (Or.inl ⟨hasCupDomArity, hasCupCodArity⟩) restHas

/-! ## ★ Piece II in `matchingOf` terms — the unconditional interface Piece I feeds

The shipped Piece II (`sameMatchingValleys_spineTraceEquiv`) wants per-block `.diagram` agreement.  Piece I's
natural output is per-block `matchingOf` agreement.  This wrapper bridges the two: `arcDiagram_eq_matching`
converts each block `matchingOf` equality to the `.diagram` shape, and Piece II closes.  UNCONDITIONAL — no
residual — so the whole-valley split reduces EXACTLY to producing the two per-block `matchingOf` equalities from a
whole-valley `matchingOf` equality (the standing valley-descent residual, #2185). -/

/-- ★ **Piece II, restated on block `matchingOf` equalities (unconditional).**  Two valleys `capBlock ++ cupBlock`
whose CAP blocks have equal `matchingOf` at `capBottomCount` and whose CUP blocks have equal `matchingOf` at
`cupBottomCount` (the mid-width), with the per-block pure arities, boundary chaining, positivity, and length
agreement, are `SpineTraceEquiv`.  Each block `matchingOf` equality converts to the `.diagram` agreement Piece II
consumes via `arcDiagram_eq_matching`, then the shipped assembly closes.  This is the clean Piece-I → Piece-II
handoff interface: the ONLY thing between a whole-valley `matchingOf` equality and `SpineTraceEquiv` is deriving
the two per-block `matchingOf` equalities (the valley-append split). -/
theorem valleysWithBlockMatchingEq_spineTraceEquiv
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
    (capBottomPositive : 0 < capBottomCount)
    (cupBottomPositive : 0 < cupBottomCount)
    (capLengthEq : capBlockFirst.length = capBlockSecond.length)
    (cupLengthEq : cupBlockFirst.length = cupBlockSecond.length)
    (capMatchEq : matchingOfSpineList capBottomCount capBlockFirst
      = matchingOfSpineList capBottomCount capBlockSecond)
    (cupMatchEq : matchingOfSpineList cupBottomCount cupBlockFirst
      = matchingOfSpineList cupBottomCount cupBlockSecond) :
    SpineTraceEquiv adjunctionModeSignature
      (capBlockFirst ++ cupBlockFirst) (capBlockSecond ++ cupBlockSecond) := by
  have capDiagramAgree : (arcStructureOfSpineList capBottomCount capBlockFirst).diagram
      = (arcStructureOfSpineList capBottomCount capBlockSecond).diagram := by
    rw [arcDiagram_eq_matching capBottomCount capBlockFirst
        (spineHasCupCapAtoms_ofAllCapArity capBlockFirst capPureFirst) capChainedFirst capBottomPositive,
      arcDiagram_eq_matching capBottomCount capBlockSecond
        (spineHasCupCapAtoms_ofAllCapArity capBlockSecond capPureSecond) capChainedSecond capBottomPositive,
      capMatchEq]
  have cupDiagramAgree : (arcStructureOfSpineList cupBottomCount cupBlockFirst).diagram
      = (arcStructureOfSpineList cupBottomCount cupBlockSecond).diagram := by
    rw [arcDiagram_eq_matching cupBottomCount cupBlockFirst
        (spineHasCupCapAtoms_ofAllCupArity cupBlockFirst cupPureFirst) cupChainedFirst cupBottomPositive,
      arcDiagram_eq_matching cupBottomCount cupBlockSecond
        (spineHasCupCapAtoms_ofAllCupArity cupBlockSecond cupPureSecond) cupChainedSecond cupBottomPositive,
      cupMatchEq]
  exact sameMatchingValleys_spineTraceEquiv capBottomCount cupBottomCount
    capBlockFirst capBlockSecond cupBlockFirst cupBlockSecond
    capPureFirst capPureSecond cupPureFirst cupPureSecond
    capChainedFirst capChainedSecond cupChainedFirst cupChainedSecond
    cupBottomPositive capLengthEq cupLengthEq capDiagramAgree cupDiagramAgree

end FX1Poly.Polygraph
