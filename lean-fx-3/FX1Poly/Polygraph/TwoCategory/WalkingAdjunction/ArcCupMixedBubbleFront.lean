import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBubbleToFront
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapPeel
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPeelFoundations
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLocateBubble
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryChain

/-! # ArcCupMixedBubbleFront — cup-fronting is arc-preserving in the MIXED regime (no purity)

The pure-cup sort's multi-step bubble (`bubbleCupToFront`, `ArcCupSiblingSwap`) realizes a
witnessed `BubblesToFront` as an `AtomicTraceEquiv` that PRESERVES the arc structure — but it is
gated on `AllCupArity` (a pure-cup spine) and hands back a third conjunct, "the moved spine stays
pure cup".  That third conjunct is the ONLY thing that consumed the purity hypothesis; the two
load-bearing conjuncts — the realized `AtomicTraceEquiv` and the arc-preservation — are both
arity-GENERIC (`atomicTraceEquiv_of_bubblesToFront` moves any atom; `extractArc_eq_of_atomicTraceEquiv`
peels any walking-adjunction trace equivalence).  This brick drops the purity gate:

  * ★ `bubbleCupToFrontMixed` — a witnessed bubble carrying a target to the front is an
    `AtomicTraceEquiv` AND arc-structure-preserving, over an ARBITRARY (mixed cup/cap) boundary-chained
    spine.  Exactly `bubbleCupToFront` minus the `AllCupArity` hypothesis and the pure-cup conjunct.
  * ★ `arcCupMixedFrontsCup_ofCupCountPos` — a boundary-chained spine (mixed) with a positive cup
    total is `AtomicTraceEquiv` to one of its cups fronting the rest, arc-structure preserved, the
    fronted atom a cup (dom-arity `0`), the fronted list still chained at the same boundary.  This is
    the concrete "front SOME cup" object the re-selection consumes, produced across a mixed prefix
    (`arcCupLocateAndBubble_ofCupCountPos` + `bubbleCupToFrontMixed`) — the census-located cup carried
    to the front through a mixed cup/cap prefix, exactly the mixed `locateAux` REALIZE step.

This is the mixed analogue of the pure-cup `bubbleCupToFront`: the swap orbit (`AtomicTraceEquiv`,
length-preserving — the length-changing cup+cap snake is correctly NOT a swap step) carries the cup
to the front while the arc invariant is unchanged.  What it does NOT settle — and what the honest
marker names — is the leg-de-merge that the front-cup residual still owes: `windowPin` (the fronted
cup IS the head cup, seed rigidity once its window matches) and `tailsCancel` (the residual tails
arc-cancel), coupled into the recursive re-selection `arcCupReselection_exists`.  Prepending a cup is
NON-injective on the full arc structure (`not_arcCupHeadCancellationUnconditional`), so the tail
cancel is genuine planar content, not a consequence of fronting.

Raw Lean 4 + Init; STRUCTURAL (rides the shipped bubble recursion), zero-axiom; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Range length plumbing (private copy — the seed files' kits are file-private) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length
        = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

/-! ## The mixed cup-fronting realization -/

/-- ★ **Cup-fronting is arc-preserving in the mixed regime.**  A witnessed bubble
(`BubblesToFront`) carrying a target atom from position `prefixAtoms.length` to the front is an
`AtomicTraceEquiv` (the shipped `atomicTraceEquiv_of_bubblesToFront`, one disjoint-window swap per
step) AND preserves the arc structure (the shipped peel `extractArc_eq_of_atomicTraceEquiv` at the
initial arc state, window fit threaded by the witness's per-step chaining).  Unlike the pure-cup
`bubbleCupToFront`, NO `AllCupArity` hypothesis is consumed and NO pure-cup conjunct is produced —
both surviving conjuncts are arity-generic, so the fronting works across an arbitrary mixed cup/cap
prefix.  The seed state is fresh (`arcStateFresh_initial`), forest-rooted (`isUnionFindForest_nil`),
`nextFresh = bottomCount > 0`, boundary-bounded on the nose, open-wire count `bottomCount`
(`rangeLength`); the chain discipline supplies the peel's window fit. -/
theorem bubbleCupToFrontMixed
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    {target movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget}
    {prefixAtoms movedPrefixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (witness : BubblesToFront target prefixAtoms movedTarget movedPrefixAtoms)
    (suffixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount (prefixAtoms ++ target :: suffixAtoms))
    (bottomPositive : 0 < bottomCount) :
    AtomicTraceEquiv adjunctionModeSignature (prefixAtoms ++ target :: suffixAtoms)
          (movedTarget :: (movedPrefixAtoms ++ suffixAtoms))
      ∧ arcStructureOfSpineList bottomCount (prefixAtoms ++ target :: suffixAtoms)
          = arcStructureOfSpineList bottomCount
              (movedTarget :: (movedPrefixAtoms ++ suffixAtoms)) := by
  have atomicEquiv := atomicTraceEquiv_of_bubblesToFront witness suffixAtoms
  refine ⟨atomicEquiv, ?_⟩
  exact extractArc_eq_of_atomicTraceEquiv atomicEquiv
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomCount bottomCount
    (arcStateFresh_initial bottomCount) isUnionFindForest_nil bottomPositive
    (Nat.le_refl bottomCount) (rangeLength bottomCount) chained

/-- ★ **A positive cup total fronts one of its cups, arc-preserved, over a mixed spine.**  A
boundary-chained walking-adjunction spine (cup AND cap atoms allowed) with a positive cup total is
`AtomicTraceEquiv` to one of its cups fronting the rest, the arc structure unchanged, the fronted
atom a cup (`generatorDom.length = 0`), and the fronted list still chained at the same boundary.  The
census-located cup (`arcCupLocateAndBubble_ofCupCountPos`, from cup-total positivity) is carried to
the front by `bubbleCupToFrontMixed` through the mixed prefix, and its chainedness by
`spineBoundaryChained_of_bubblesToFront`.  This is the concrete cup-fronting object the re-selection
consumes — the mixed `locateAux` REALIZE step; it does NOT yet pin the fronted cup's window to the
head (`windowPin`) nor cancel the residual tails (`tailsCancel`). -/
theorem arcCupMixedFrontsCup_ofCupCountPos (bottomCount : Nat)
    {overallSource overallTarget : adjunctionGraph.Mode}
    (secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (secondChained : SpineBoundaryChained bottomCount secondList)
    (bottomPositive : 0 < bottomCount)
    (cupCountPos : 0 < (arcStructureOfSpineList bottomCount secondList).cupCount) :
    ∃ (movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget)
      (movedRest : List (SpineAtom adjunctionModeSignature overallSource overallTarget)),
      AtomicTraceEquiv adjunctionModeSignature secondList (movedTarget :: movedRest)
        ∧ arcStructureOfSpineList bottomCount secondList
            = arcStructureOfSpineList bottomCount (movedTarget :: movedRest)
        ∧ movedTarget.generatorDom.length = 0
        ∧ SpineBoundaryChained bottomCount (movedTarget :: movedRest) := by
  obtain ⟨prefixAtoms, toucherAtom, suffixAtoms, movedTarget, movedPrefixAtoms,
    doesSplitSpine, witness, movedIsCup⟩ :=
    arcCupLocateAndBubble_ofCupCountPos bottomCount secondList secondChained cupCountPos
  subst doesSplitSpine
  obtain ⟨atomicEquiv, arcPreserved⟩ :=
    bubbleCupToFrontMixed bottomCount witness suffixAtoms secondChained bottomPositive
  exact ⟨movedTarget, movedPrefixAtoms ++ suffixAtoms, atomicEquiv, arcPreserved, movedIsCup,
    spineBoundaryChained_of_bubblesToFront witness suffixAtoms secondChained⟩

/-! ## Honesty marker -/

/-- **Honesty marker — mixed cup-fronting is arc-preserving (the `locateAux` REALIZE step).**
`bubbleCupToFrontMixed` drops the pure-cup gate of `bubbleCupToFront`: a witnessed bubble is an
`AtomicTraceEquiv` and arc-structure-preserving over an ARBITRARY mixed cup/cap spine (both surviving
conjuncts are arity-generic).  `arcCupMixedFrontsCup_ofCupCountPos` chains it with the census locator
(`arcCupLocateAndBubble_ofCupCountPos`) to front one cup of any positive-cup-total mixed spine, arc
preserved and still chained — the concrete cup-fronting object the re-selection consumes, produced
across a mixed prefix.

What this marker does NOT claim: the fronted cup is the HEAD cup (`windowPin`, seed rigidity once its
window matches) nor that the residual tails arc-cancel (`tailsCancel`).  Those two are coupled into
the recursive re-selection `arcCupReselection_exists`, whose head-cup CANCEL is genuine planar content
— prepending a cup is NON-injective on the full arc structure
(`not_arcCupHeadCancellationUnconditional`), so the tail cancel is a leg-de-merge (the fresh-boundary
diagram leg + the two per-port internal-count legs, `ArcCupTailsCancelInterface`), NOT a consequence
of fronting.  The swap orbit realized here is length-preserving; the length-changing cup+cap snake is
correctly NOT an `AtomicTraceEquiv` step.  No gate flip; `fxMode_hasArcStructureReconstruction` stays
as is.  `= true`. -/
def fxMode_hasArcCupMixedBubbleFront : Bool := true

end FX1Poly.Polygraph
