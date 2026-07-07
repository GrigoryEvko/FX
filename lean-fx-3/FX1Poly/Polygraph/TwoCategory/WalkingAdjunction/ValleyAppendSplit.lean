import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyMatchingSpineTraceEquiv
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcMatchViewFold
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingVcompLeftCongruence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFoldCongruence

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

end FX1Poly.Polygraph
