import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLastCupReadoff
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # ValleyCupCapStatePromotion — the general in-valley cap seed carries every `diagramPartner_stepCupArc`
precondition (Piece II tail, sub-node (ii) of the two-run offset fold)

The two-run offset fold that closes `cupTopTopPartner` (`ValleyCupReconstruct`, cup case 3) runs the SAME
`cupBlock` through `diagramPartner_stepCupArc` at TWO seeds:

  * the cup-alone seed `arcInit midWidth := ArcWireState.mk (List.range midWidth) [] midWidth 0 [] []` — its four
    `diagramPartner_stepCupArc` preconditions are the trivial initial facts;
  * the in-valley seed `capState := processArcSpine (arcInit bc) capBlock` — a NON-trivial arc state (non-empty
    cap links, scattered survivor bottoms), whose four preconditions are FOLD facts.

This file lands the second bundle: for a boundary-chained cap block, the folded cap seed satisfies all four
`diagramPartner_stepCupArc` preconditions at floor `bottomCount` —

  * `ArcStateFresh capState` (`arcStateFresh_processArcSpine` from the fresh initial state),
  * `isUnionFindForest capState.links` (`isUnionFindForest_processArcSpine` from the empty forest),
  * `bottomCount ≤ capState.nextFresh` (`seedBottomCount_le_processArcSpine_nextFresh`),
  * `ArcBoundaryCensus bottomCount capState` (`arcBoundaryCensus_ofChainedSpineList`, the cap-general census).

Each is a direct instantiation of a shipped generic fold lemma; the value here is the SINGLE named bundle the
peel-last two-run fold consumes, and a machine-checked confirmation that the four preconditions DO compose for a
general cap seed (asserted-but-unverified in the two-run-fold plan).  This does NOT close `cupTopTopPartner` — the
peel-last offset-space induction over `diagramPartner_stepCupArc` at BOTH floors (sub-node (iii)) remains the
un-shipped multi-session brick.  No gate flag is flipped; fib-3 also carries the independent Piece-I beam
(`MatchingReductsShareSpineTrace`, #1996).

Raw Lean 4 + Init; the whole file is off-the-shelf instantiation, no new recursion / `omega` / `simp`-AC.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The four `diagramPartner_stepCupArc` preconditions for the folded cap seed -/

/-- ★ **`ArcStateFresh` at the folded cap seed.**  Folding a cap block from the fresh initial state preserves
freshness (`arcStateFresh_processArcSpine`), so `capState := processArcSpine (arcInit bc) capBlock` is fresh. -/
theorem arcCapState_arcStateFresh
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (capBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    ArcStateFresh (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock) :=
  arcStateFresh_processArcSpine capBlock (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
    (arcStateFresh_initial bottomCount)

/-- ★ **`isUnionFindForest` at the folded cap seed.**  The empty initial forest folds acyclically through every
cap step (`isUnionFindForest_processArcSpine`). -/
theorem arcCapState_isUnionFindForest
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (capBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    isUnionFindForest
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock).links :=
  isUnionFindForest_processArcSpine capBlock (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
    isUnionFindForest_nil

/-- ★ **`seedBelowFresh` at the folded cap seed.**  Fresh counters only grow, so the seed floor `bottomCount`
stays at-or-below the folded `nextFresh` (`seedBottomCount_le_processArcSpine_nextFresh`). -/
theorem arcCapState_seedBelowFresh
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (capBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    bottomCount
      ≤ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock).nextFresh :=
  seedBottomCount_le_processArcSpine_nextFresh bottomCount capBlock

/-- ★ **`ArcBoundaryCensus` at the folded cap seed.**  The cap-general census fold
(`arcBoundaryCensus_ofChainedSpineList`) certifies the folded cap seed satisfies the boundary-census invariant at
floor `bottomCount`, given the cap block is boundary-chained.  This is the ONE precondition that carries a genuine
side-hypothesis (`SpineBoundaryChained bottomCount capBlock`); the eventual valley caller supplies it because a
genuine valley's cap block is boundary-chained. -/
theorem arcCapState_arcBoundaryCensus
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (capBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (capChained : SpineBoundaryChained bottomCount capBlock) :
    ArcBoundaryCensus bottomCount
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock) :=
  arcBoundaryCensus_ofChainedSpineList bottomCount capBlock capChained

/-! ## The bundle -/

/-- ★ **The folded cap seed carries every `diagramPartner_stepCupArc` precondition (bundle).**  For a
boundary-chained cap block, the in-valley arc seed `capState := processArcSpine (arcInit bottomCount) capBlock`
satisfies — at floor `bottomCount` — the FOUR preconditions `diagramPartner_stepCupArc` demands on its input
state: `ArcStateFresh`, `isUnionFindForest … .links`, `bottomCount ≤ … .nextFresh`, and
`ArcBoundaryCensus bottomCount …`.  This is exactly the general-seed promotion sub-node (ii): the peel-last
two-run offset fold can now start the in-valley run from `capState` with every per-cup transport precondition in
hand, mirroring the trivial `arcInit`-seed run.  What remains un-shipped is the fold itself (sub-node (iii)). -/
theorem arcCapState_stepCupArc_preconditions
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (capBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (capChained : SpineBoundaryChained bottomCount capBlock) :
    ArcStateFresh (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock)
      ∧ isUnionFindForest
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock).links
      ∧ bottomCount
          ≤ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              capBlock).nextFresh
      ∧ ArcBoundaryCensus bottomCount
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock) :=
  ⟨arcCapState_arcStateFresh bottomCount capBlock,
    arcCapState_isUnionFindForest bottomCount capBlock,
    arcCapState_seedBelowFresh bottomCount capBlock,
    arcCapState_arcBoundaryCensus bottomCount capBlock capChained⟩

/-! ## Honesty marker -/

/-- **Honesty marker — sub-node (ii) of the top-top two-run offset fold is LANDED: the general in-valley cap seed
carries every `diagramPartner_stepCupArc` precondition.**

Landed here, all zero-axiom (pure instantiation of shipped fold lemmas):

  * `arcCapState_arcStateFresh` / `arcCapState_isUnionFindForest` / `arcCapState_seedBelowFresh` /
    `arcCapState_arcBoundaryCensus` — the four `diagramPartner_stepCupArc` preconditions at floor `bottomCount`
    for the folded cap seed `processArcSpine (arcInit bottomCount) capBlock`.
  * `arcCapState_stepCupArc_preconditions` — the single named bundle the peel-last two-run fold consumes.

This confirms (machine-checked, not merely asserted) that the four per-cup-transport preconditions DO compose for
a general, non-trivial cap seed — the second seed of the two-run offset fold that would close `cupTopTopPartner`
(`ValleyCupReconstruct`, cup case 3).  What this marker does NOT close: `cupTopTopPartner` itself, hence
`cupRestrict_reconstructs` (which keeps it as a hypothesis) and downstream `valleyAppend_split` /
`valleysWithEqualMatching_spineTraceEquiv`.  The remaining brick (sub-node (iii)) is the offset-space invariant
peel-last induction over `diagramPartner_stepCupArc` run at BOTH floors (`bottomCount` and `midWidth`), folding
`freshShiftAbove_floorEquivariant` (`ValleyCupTopTopFloorShift`) across the whole cup block — a genuine
multi-session brick (the shipped `dropLastCup_arc_injective` runs the same engine at a SINGLE shared seed).  No
gate flag is flipped; fib-3 also carries the independent Piece-I beam (`MatchingReductsShareSpineTrace`, #1996).
`= true`. -/
def fxMode_hasCupCapStatePromotion : Bool := true

end FX1Poly.Polygraph
