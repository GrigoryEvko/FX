import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcBoundaryCensusPerfectMatchingFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFreshDecision

/-! # WalkingString/StringValleyCupCapStatePromotion — the general in-valley cap seed carries every
`diagramPartner_stepCupArc` precondition, over the walking ADJOINT-TRIPLE (`F ⊣ G ⊣ H`) signature (FC-3 r34,
Piece-II tail, sub-node (ii) of the two-run offset fold)

The string clone of the walking-adjunction `ValleyCupCapStatePromotion`.  The two-run offset fold that closes
`stringCupTopTopPartner` runs the SAME `cupBlock` through `diagramPartner_stepCupArc` at TWO seeds: the cup-alone
seed `arcInit midWidth` (trivial preconditions) and the in-valley cap seed
`capState := processArcSpine (arcInit bottomCount) capBlock` (fold preconditions).  This file lands the second
bundle: for a boundary-chained cap block, the folded cap seed satisfies all four `diagramPartner_stepCupArc`
preconditions at floor `bottomCount` —

  * `ArcStateFresh capState` (`arcStateFresh_processArcSpine` from the fresh initial state, signature-generic),
  * `isUnionFindForest capState.links` (`isUnionFindForest_processArcSpine` from the empty forest, generic),
  * `bottomCount ≤ capState.nextFresh` (`processArcSpine_nextFresh_le` from the initial `nextFresh = bottomCount`,
    generic — the adjunction original's `seedBottomCount_le_processArcSpine_nextFresh` wrapper is itself signature
    specific, so we route through its generic core directly),
  * `ArcBoundaryCensus bottomCount capState` (`stringArcBoundaryCensus_ofChainedSpineList`, the shipped string
    cap-general census fold).

Each is a direct instantiation of a generic fold lemma or the shipped string census; the arc engine
(`processArcSpine`, `ArcStateFresh`, `isUnionFindForest`, `ArcBoundaryCensus`) is signature-blind and REUSED by
import.  This does NOT close `stringCupTopTopPartner` — the peel-last offset-space induction over
`diagramPartner_stepCupArc` at BOTH floors ships in `StringValleyCupTopTop{Fold,Seed}`.  No master flag is flipped.

Raw Lean 4 + Init; the whole file is off-the-shelf instantiation, no new recursion / `omega` / `simp`-AC.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The four `diagramPartner_stepCupArc` preconditions for the folded cap seed -/

/-- ★ **`ArcStateFresh` at the folded cap seed.**  Folding a cap block from the fresh initial state preserves
freshness (`arcStateFresh_processArcSpine`), so `capState := processArcSpine (arcInit bottomCount) capBlock` is
fresh. -/
theorem stringArcCapState_arcStateFresh
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (capBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    ArcStateFresh (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock) :=
  arcStateFresh_processArcSpine capBlock (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
    (arcStateFresh_initial bottomCount)

/-- ★ **`isUnionFindForest` at the folded cap seed.**  The empty initial forest folds acyclically through every
cap step (`isUnionFindForest_processArcSpine`). -/
theorem stringArcCapState_isUnionFindForest
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (capBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    isUnionFindForest
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock).links :=
  isUnionFindForest_processArcSpine capBlock (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
    isUnionFindForest_nil

/-- ★ **`seedBelowFresh` at the folded cap seed.**  Fresh counters only grow (`processArcSpine_nextFresh_le`), and
the initial `nextFresh` is `bottomCount` (defeq), so the seed floor `bottomCount` stays at-or-below the folded
`nextFresh`. -/
theorem stringArcCapState_seedBelowFresh
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (capBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    bottomCount
      ≤ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock).nextFresh :=
  processArcSpine_nextFresh_le capBlock (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])

/-- ★ **`ArcBoundaryCensus` at the folded cap seed.**  The shipped string cap-general census fold
(`stringArcBoundaryCensus_ofChainedSpineList`) certifies the folded cap seed satisfies the boundary-census
invariant at floor `bottomCount`, given the cap block is boundary-chained.  This is the ONE precondition that
carries a genuine side-hypothesis (`SpineBoundaryChained bottomCount capBlock`); the eventual valley caller
supplies it because a genuine valley's cap block is boundary-chained. -/
theorem stringArcCapState_arcBoundaryCensus
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (capBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (capChained : SpineBoundaryChained bottomCount capBlock) :
    ArcBoundaryCensus bottomCount
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock) :=
  stringArcBoundaryCensus_ofChainedSpineList bottomCount capBlock capChained

/-! ## The bundle -/

/-- ★ **The folded cap seed carries every `diagramPartner_stepCupArc` precondition (bundle).**  For a
boundary-chained cap block, the in-valley arc seed `capState := processArcSpine (arcInit bottomCount) capBlock`
satisfies — at floor `bottomCount` — the FOUR preconditions `diagramPartner_stepCupArc` demands on its input
state: `ArcStateFresh`, `isUnionFindForest … .links`, `bottomCount ≤ … .nextFresh`, and
`ArcBoundaryCensus bottomCount …`.  This is the general-seed promotion sub-node (ii): the peel-last two-run offset
fold (`StringValleyCupTopTopSeed`) starts the in-valley run from `capState` with every per-cup transport
precondition in hand, mirroring the trivial `arcInit`-seed run. -/
theorem stringArcCapState_stepCupArc_preconditions
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (capBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (capChained : SpineBoundaryChained bottomCount capBlock) :
    ArcStateFresh (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock)
      ∧ isUnionFindForest
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock).links
      ∧ bottomCount
          ≤ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              capBlock).nextFresh
      ∧ ArcBoundaryCensus bottomCount
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock) :=
  ⟨stringArcCapState_arcStateFresh bottomCount capBlock,
    stringArcCapState_isUnionFindForest bottomCount capBlock,
    stringArcCapState_seedBelowFresh bottomCount capBlock,
    stringArcCapState_arcBoundaryCensus bottomCount capBlock capChained⟩

/-! ## Concrete truth-probe — the census precondition FIRES on the non-degenerate wide cap block -/

/-- The wide cap block `[ε]` is boundary-chained at `bottomCount = 4`: the cap fires at width `4` (its
`domBoundaryLength`), dropping to mid-width `2` (its `codBoundaryLength`). -/
theorem stringWideProbeCapBlock_chainedAtFour :
    SpineBoundaryChained 4 [stringWideProbeCapAtom] :=
  SpineBoundaryChained.cons stringWideProbeCapAtom rfl (SpineBoundaryChained.nil 2)

/-- ★ **The cap-seed census precondition FIRES on the genuine non-degenerate wide valley.**  On the wide cap block
`[ε]` at `bottomCount = 4` (mid-width `2`, `stringWideProbe_midWidth_isTwo`), the folded cap seed satisfies the
boundary-census invariant — the load-bearing precondition (the one carrying a genuine chained side-hypothesis) for
the two-run offset fold, inhabited over a valley with non-zero mid content, NOT vacuous. -/
theorem stringArcCapState_arcBoundaryCensus_firesOnWideValley :
    ArcBoundaryCensus 4
      (processArcSpine (ArcWireState.mk (List.range 4) [] 4 0 [] []) [stringWideProbeCapAtom]) :=
  stringArcCapState_arcBoundaryCensus 4 [stringWideProbeCapAtom] stringWideProbeCapBlock_chainedAtFour

/-! ## Marker -/

/-- **Marker — sub-node (ii) of the top-top two-run offset fold is LANDED on the STRING side: the general in-valley
cap seed carries every `diagramPartner_stepCupArc` precondition (FC-3 r34).**

Landed here, all zero-axiom (pure instantiation of shipped generic-fold / string-census lemmas):

  * `stringArcCapState_arcStateFresh` / `_isUnionFindForest` / `_seedBelowFresh` / `_arcBoundaryCensus` — the four
    `diagramPartner_stepCupArc` preconditions at floor `bottomCount` for the folded cap seed.
  * `stringArcCapState_stepCupArc_preconditions` — the single named bundle `StringValleyCupTopTopSeed` consumes.
  * `stringArcCapState_arcBoundaryCensus_firesOnWideValley` — the census precondition truth-probed on the wide
    (mid-width `2`) valley.

This does NOT close `stringCupTopTopPartner`, hence `stringCupRestrict_reconstructs` stays gated until
`StringValleyCupTopTopSeed` ships.  No master flag is flipped.  `= true`. -/
def fxString_hasCupCapStatePromotion : Bool := true

end FX1Poly.Polygraph
