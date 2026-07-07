import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.PureCapSurvivorReadoff
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.PureCapSurvivorUnlinked
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleySurvivorOrder

/-! # CupShiftReranking — the cup-shift re-ranking (Piece II tail, brick 1)

Brick (2b) (`partnerIndexOf_survivor_eq_rank`) read off a survivor bottom port's `partnerIndexOf` as
`bottomCount + rank` — but under the hypothesis `openAllUnlinked` that EVERY open wire is unlinked.  That
hypothesis holds for a pure-cap block's final state, but it FAILS for the WHOLE valley `capBlock ++ cupBlock`:
the cup block's top open wires are its fresh legs, which ARE linked (each cup joins its two legs).  So the
shipped read-off does not directly reach the whole valley.

This file closes the gap.  The survivor's partner scan does not actually need every open wire unlinked — it
only needs that no open wire before the survivor's own position roots to the survivor.  Because the survivor is
unlinked (its own root is itself), `unionFindRootOf_ne_ofUnlinked` shows every OTHER node's root avoids the
survivor — cup legs included (their root is a fresh id, above the survivor).  So the below-rank misses hold
regardless of whether the intervening wires are linked.

  * ★ `partnerIndexOf_survivorUnlinked_eq_rank` — the read-off with `openAllUnlinked` DROPPED: a survivor whose
    node sits at open-wire position `rank` has `partnerIndexOf = bottomCount + rank`, using only that the
    survivor is unlinked and the open wires are positionally distinct.  Strictly generalizes
    `partnerIndexOf_survivor_eq_rank`.
  * `stepCup_preservesArcNodeUnlinked` / `processSpine_preservesArcNodeUnlinked_ofAllCupArity` — a cup block
    keeps every below-fresh node unlinked (cups join only fresh legs, above every old node).
  * ★ `survivorPartner_throughCupBlock` — the CUP-SHIFT re-ranking (abstract mid-state form): a survivor at
    cap-state open-wire position `rankCap` has, in the whole valley `capState ++ cupBlock`, `partnerIndexOf =
    bottomCount + phi rankCap`, where `phi` is the cup block's order embedding (`WireOrderEmbedding`).  The
    survivor's whole-valley partner top port is its cap-state rank SHIFTED through the cup insertions.
  * ★ `survivorPartner_inWholeValley` — the seed-level wrapper: from the canonical seed, a bottom port that
    survives the cap block has its whole-valley `partnerIndexOf` pinned to `bottomCount + phi rankCap`, all
    mid-state hypotheses discharged by the shipped cap-survivor + seed-distinctness invariants.

Raw Lean 4 + Init; structural / `AllCupArity` recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The generic survivor read-off — `openAllUnlinked` dropped

An in-range positional read is a member (local copy — the seed files' `natListGetAt_mem_inRange` is
file-private). -/
private theorem getAt_mem_inRange : (wires : List Nat) → (index : Nat) →
    index < wires.length → natListGetAt wires index ∈ wires
  | [], _, indexInRange => absurd indexInRange (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, indexInRange =>
      List.Mem.tail _ (getAt_mem_inRange rest index (Nat.lt_of_succ_lt_succ indexInRange))

/-- ★ **The survivor partner read-off WITHOUT `openAllUnlinked`.**  A survivor bottom port `survivor`
(`< bottomCount`, unlinked) whose node id sits at position `rank` among the open wires has
`partnerIndexOf = bottomCount + rank` — proven using only that the survivor is unlinked and the open wires are
positionally distinct.  The scan drops to the top segment (`partnerIndexOf_survivor_dropsToTop`); on that
segment, every candidate below `rank` reads an open wire whose id differs from the survivor (distinctness), so
its root avoids the survivor's own root (`unionFindRootOf_ne_ofUnlinked` — the survivor is unlinked), failing
the root test regardless of whether that wire is itself linked; at `rank` the read IS the survivor, whose root
is itself, passing.  The first-hit combinator lands the partner at `bottomCount + rank`.  This strictly
generalizes `partnerIndexOf_survivor_eq_rank` (whose `openAllUnlinked` fails for a whole valley's cup-leg top
wires). -/
theorem partnerIndexOf_survivorUnlinked_eq_rank (links : List (Nat × Nat)) (bottomCount : Nat)
    (state : WireState) {survivor rank : Nat}
    (survivorBelow : survivor < bottomCount)
    (survivorUnlinked : ArcNodeUnlinked links survivor)
    (openDistinct : WireListDistinct state.openWires)
    (rankLt : rank < state.openWires.length)
    (survivorAtRank : natListGetAt state.openWires rank = survivor) :
    partnerIndexOf links (matchingBoundaryNodes bottomCount state)
        (bottomCount + state.openWires.length) survivor
      = bottomCount + rank := by
  rw [partnerIndexOf_survivor_dropsToTop links bottomCount state survivorBelow survivorUnlinked
    state.openWires.length]
  refine findPartnerScan_mapRange_firstHit links (matchingBoundaryNodes bottomCount state)
    survivor survivor state.openWires.length rank bottomCount rankLt ?_ ?_
  · intro offset offsetLt
    rw [matchingBoundaryNodes_getAt_top bottomCount state offset]
    have offsetLtLen : offset < state.openWires.length := Nat.lt_trans offsetLt rankLt
    have readNe : natListGetAt state.openWires offset ≠ survivor := by
      have distinctNe := distinctReadNe state.openWires openDistinct offset rank offsetLtLen rankLt
        (fun offsetEqRank => Nat.lt_irrefl rank (offsetEqRank ▸ offsetLt))
      exact survivorAtRank ▸ distinctNe
    have rootBeqFalse :
        (unionFindRootOf links (natListGetAt state.openWires offset) == survivor) = false := by
      cases probe : (unionFindRootOf links (natListGetAt state.openWires offset) == survivor) with
      | true =>
          exact absurd (of_decide_eq_true probe)
            (unionFindRootOf_ne_ofUnlinked links survivorUnlinked _ readNe)
      | false => rfl
    rw [rootBeqFalse]; exact Bool.and_false _
  · have survivorLt : survivor < bottomCount + rank :=
      Nat.lt_of_lt_of_le survivorBelow (Nat.le_add_right bottomCount rank)
    have excludeNeqTrue : (bottomCount + rank != survivor) = true := by
      show (!(bottomCount + rank == survivor)) = true
      cases sumIsSurvivor : (bottomCount + rank == survivor) with
      | true =>
          exact absurd (of_decide_eq_true sumIsSurvivor)
            (fun sumEq => Nat.lt_irrefl survivor (sumEq ▸ survivorLt))
      | false => rfl
    have selfBeq : (survivor == survivor) = true := by apply decide_eq_true; rfl
    rw [matchingBoundaryNodes_getAt_top bottomCount state rank, survivorAtRank,
      unionFindRootOf_eq_self_ofUnlinked links survivorUnlinked, selfBeq, Bool.and_true]
    exact excludeNeqTrue

/-! ## A cup block keeps every below-fresh node unlinked -/

/-- ★ **A cup step keeps a below-fresh node unlinked.**  A cup joins exactly its two fresh legs `nextFresh`
and `nextFresh + 1` (`stepCup_links`); a node strictly below `nextFresh` differs from both, so
`arcNodeUnlinked_unionFindJoin` preserves its unlinkedness. -/
theorem stepCup_preservesArcNodeUnlinked (state : WireState) (position node : Nat)
    (nodeBelowFresh : node < state.nextFresh) (unlinked : ArcNodeUnlinked state.links node) :
    ArcNodeUnlinked (stepCup state position).links node := by
  rw [stepCup_links]
  have missesLeg : state.nextFresh ≠ node := fun eq => Nat.lt_irrefl node (eq ▸ nodeBelowFresh)
  have belowUpper : node < state.nextFresh + 1 := Nat.lt_succ_of_lt nodeBelowFresh
  have missesUpperLeg : state.nextFresh + 1 ≠ node := fun eq => Nat.lt_irrefl node (eq ▸ belowUpper)
  exact arcNodeUnlinked_unionFindJoin state.links state.nextFresh (state.nextFresh + 1)
    unlinked missesLeg missesUpperLeg

/-- ★ **A pure-cup block keeps every below-fresh node unlinked.**  By induction on the `AllCupArity` witness:
each cup step is a `stepCup` (`stepAtom_ofCupArity`) that preserves unlinkedness of a below-fresh node
(`stepCup_preservesArcNodeUnlinked`), and the node stays below the (only ever raised) `nextFresh`.  So a survivor
bottom node, unlinked at the cap-block mid-state, remains unlinked through the whole cup block. -/
theorem processSpine_preservesArcNodeUnlinked_ofAllCupArity
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    (state : WireState) → (node : Nat) → node < state.nextFresh →
    ArcNodeUnlinked state.links node →
    ArcNodeUnlinked (processSpine state atoms).links node := by
  induction pureCup with
  | nil => intro _ _ _ unlinked; exact unlinked
  | cons hasCupDomArity hasCupCodArity _restAllCup restIH =>
      rename_i headAtom rest
      intro state node nodeBelowFresh unlinked
      show ArcNodeUnlinked (processSpine (stepAtom state headAtom) rest).links node
      rw [stepAtom_ofCupArity state headAtom hasCupDomArity hasCupCodArity]
      have newUnlinked : ArcNodeUnlinked (stepCup state headAtom.leftContext.length).links node :=
        stepCup_preservesArcNodeUnlinked state headAtom.leftContext.length node nodeBelowFresh unlinked
      have newBelowFresh : node < (stepCup state headAtom.leftContext.length).nextFresh := by
        rw [stepCup_nextFresh]
        exact Nat.lt_of_lt_of_le nodeBelowFresh (Nat.le_add_right state.nextFresh 2)
      exact restIH (stepCup state headAtom.leftContext.length) node newBelowFresh newUnlinked

/-! ## The cup-shift re-ranking (abstract mid-state form) -/

/-- ★ **The CUP-SHIFT re-ranking.**  Given a cap-block mid-state `capState` and a survivor bottom port
`survivor` that at the mid-state is unlinked and sits at open-wire position `rankCap`, the WHOLE valley
`capState ++ cupBlock` matches `survivor` to top boundary index `bottomCount + phi rankCap`, where `phi` is the
cup block's order embedding of the mid-state open wires into the final open wires
(`processSpine_wireOrderEmbedding_ofAllCupArity`).  Assembly: the cup block preserves the survivor's
unlinkedness (`processSpine_preservesArcNodeUnlinked_ofAllCupArity`) and — since the order embedding is
value-preserving — the survivor reappears at the SHIFTED position `phi rankCap` in the final open wires; the
generic read-off `partnerIndexOf_survivorUnlinked_eq_rank` (which tolerates the cup legs' linked top wires)
then pins the partner at `bottomCount + phi rankCap`.  This is the forward direction of the through-strand
re-ranking: a survivor's whole-valley partner top port is its cap-state rank pushed through the cup
insertions. -/
theorem survivorPartner_throughCupBlock
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount boundaryLength : Nat)
    (cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (cupPure : AllCupArity cupBlock) (capState : WireState)
    (bottomLeFresh : bottomCount ≤ capState.nextFresh)
    (capTracksBoundary : capState.openWires.length = boundaryLength)
    (cupChained : SpineBoundaryChained boundaryLength cupBlock)
    (wholeDistinct : WireListDistinct (processSpine capState cupBlock).openWires)
    {survivor rankCap : Nat}
    (survivorBelow : survivor < bottomCount)
    (survivorUnlinkedMid : ArcNodeUnlinked capState.links survivor)
    (rankCapLt : rankCap < capState.openWires.length)
    (survivorAtRankCap : natListGetAt capState.openWires rankCap = survivor) :
    ∃ phi, WireOrderEmbedding phi capState.openWires (processSpine capState cupBlock).openWires ∧
      partnerIndexOf (processSpine capState cupBlock).links
          (matchingBoundaryNodes bottomCount (processSpine capState cupBlock))
          (bottomCount + (processSpine capState cupBlock).openWires.length) survivor
        = bottomCount + phi rankCap := by
  obtain ⟨phi, embedding⟩ := processSpine_wireOrderEmbedding_ofAllCupArity cupBlock cupPure
    capState boundaryLength capTracksBoundary cupChained
  refine ⟨phi, embedding, ?_⟩
  have survivorUnlinkedWhole : ArcNodeUnlinked (processSpine capState cupBlock).links survivor :=
    processSpine_preservesArcNodeUnlinked_ofAllCupArity cupBlock cupPure capState survivor
      (Nat.lt_of_lt_of_le survivorBelow bottomLeFresh) survivorUnlinkedMid
  have rankWholeLt : phi rankCap < (processSpine capState cupBlock).openWires.length :=
    embedding.inRange rankCap rankCapLt
  have survivorAtRankWhole :
      natListGetAt (processSpine capState cupBlock).openWires (phi rankCap) = survivor := by
    rw [embedding.reads rankCap rankCapLt, survivorAtRankCap]
  exact partnerIndexOf_survivorUnlinked_eq_rank (processSpine capState cupBlock).links bottomCount
    (processSpine capState cupBlock) survivorBelow survivorUnlinkedWhole wholeDistinct
    rankWholeLt survivorAtRankWhole

/-! ## The seed-level wrapper -/

/-- ★ **The cup-shift re-ranking at the canonical seed.**  For a valley `capBlock ++ cupBlock` at bottom count
`bottomCount` (positive), a bottom port `survivor` that SURVIVES the cap block (still an open wire of the
cap-block mid-state) has its WHOLE-valley `partnerIndexOf` equal to `bottomCount + phi rankCap`, where `rankCap`
is its rank among the mid-state open wires and `phi` is the cup block's order embedding.  All mid-state
hypotheses of `survivorPartner_throughCupBlock` are discharged from the shipped seed invariants: the survivor
is below `bottomCount` (`processSpine_openWires_below_ofAllCapArity_seed`) and unlinked
(`processSpine_openWires_unlinked_ofAllCapArity_seed`) at the mid-state, its mid-state rank comes from
`mem_imp_getAt`, the mid-state `nextFresh` is `bottomCount` (`processSpine_nextFresh_ofAllCapArity_seed`), and
the whole valley's open wires are distinct (`processSpine_fromSeed_wireListDistinct`).  The whole-valley state is
the cup block run from the mid-state (`processSpine_append`).  This is the forward through-strand re-ranking for
the actual valley. -/
theorem survivorPartner_inWholeValley
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPos : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock)
    (capChained : SpineBoundaryChained bottomCount capBlock)
    (cupChained : SpineBoundaryChained
        (processSpine (canonicalMatchingSeed bottomCount) capBlock).openWires.length cupBlock)
    {survivor : Nat}
    (survivorMem : survivor ∈ (processSpine (canonicalMatchingSeed bottomCount) capBlock).openWires) :
    ∃ phi rankCap,
      rankCap < (processSpine (canonicalMatchingSeed bottomCount) capBlock).openWires.length ∧
      natListGetAt (processSpine (canonicalMatchingSeed bottomCount) capBlock).openWires rankCap = survivor ∧
      WireOrderEmbedding phi
        (processSpine (canonicalMatchingSeed bottomCount) capBlock).openWires
        (processSpine (canonicalMatchingSeed bottomCount) (capBlock ++ cupBlock)).openWires ∧
      partnerIndexOf
          (processSpine (canonicalMatchingSeed bottomCount) (capBlock ++ cupBlock)).links
          (matchingBoundaryNodes bottomCount
            (processSpine (canonicalMatchingSeed bottomCount) (capBlock ++ cupBlock)))
          (bottomCount
            + (processSpine (canonicalMatchingSeed bottomCount) (capBlock ++ cupBlock)).openWires.length)
          survivor
        = bottomCount + phi rankCap := by
  have splitEq : processSpine (canonicalMatchingSeed bottomCount) (capBlock ++ cupBlock)
      = processSpine (processSpine (canonicalMatchingSeed bottomCount) capBlock) cupBlock :=
    processSpine_append capBlock cupBlock (canonicalMatchingSeed bottomCount)
  have survivorBelow : survivor < bottomCount :=
    processSpine_openWires_below_ofAllCapArity_seed bottomCount bottomPos capBlock capPure
      survivor survivorMem
  have survivorUnlinkedMid :
      ArcNodeUnlinked (processSpine (canonicalMatchingSeed bottomCount) capBlock).links survivor :=
    processSpine_openWires_unlinked_ofAllCapArity_seed bottomCount capBlock capPure capChained
      survivor survivorMem
  obtain ⟨rankCap, rankCapLt, survivorAtRankCap⟩ :=
    mem_imp_getAt (processSpine (canonicalMatchingSeed bottomCount) capBlock).openWires survivorMem
  have bottomLeFresh :
      bottomCount ≤ (processSpine (canonicalMatchingSeed bottomCount) capBlock).nextFresh :=
    Nat.le_of_eq (processSpine_nextFresh_ofAllCapArity_seed bottomCount capBlock capPure).symm
  have wholeDistinct :
      WireListDistinct
        (processSpine (processSpine (canonicalMatchingSeed bottomCount) capBlock) cupBlock).openWires :=
    splitEq ▸ processSpine_fromSeed_wireListDistinct bottomCount bottomPos (capBlock ++ cupBlock)
  obtain ⟨phi, embedding, partnerEq⟩ := survivorPartner_throughCupBlock bottomCount
    (processSpine (canonicalMatchingSeed bottomCount) capBlock).openWires.length cupBlock cupPure
    (processSpine (canonicalMatchingSeed bottomCount) capBlock) bottomLeFresh rfl cupChained
    wholeDistinct survivorBelow survivorUnlinkedMid rankCapLt survivorAtRankCap
  refine ⟨phi, rankCap, rankCapLt, survivorAtRankCap, ?_, ?_⟩
  · rw [splitEq]; exact embedding
  · rw [splitEq]; exact partnerEq

/-! ## Honesty marker -/

/-- **Honesty marker — the cup-shift re-ranking (brick 1) is CLOSED.**  A survivor bottom port's WHOLE-valley
`partnerIndexOf` is `bottomCount + phi rankCap`, where `rankCap` is its cap-state rank and `phi` is the cup
block's order embedding — the forward through-strand re-ranking.  The crux was dropping the
`openAllUnlinked` hypothesis of the shipped read-off (`partnerIndexOf_survivorUnlinked_eq_rank`): the cup block's
top open wires ARE linked (cup legs), yet the survivor's partner scan still lands correctly because its below-rank
misses need only that no wire roots to the unlinked survivor — which `unionFindRootOf_ne_ofUnlinked` supplies for
cup legs and survivors alike.  The survivor's whole-valley unlinkedness comes from a cup-block fold
(`processSpine_preservesArcNodeUnlinked_ofAllCupArity`), its shifted position from the shipped order embedding
(`processSpine_wireOrderEmbedding_ofAllCupArity`), and the whole open-wire distinctness from the shipped
seed invariant.

What this brick does NOT yet do: the F-assembly (`matchingOf bottomCount capBlock = F(matchingOf bottomCount
V)`).  The cap-alone survivor partner is `bottomCount + rankCap`; the whole-valley one is `bottomCount + phi
rankCap` — they DIFFER by the cup shift `phi`.  Reconstructing the cap diagram from the V diagram must INVERT
`phi` — compress out the cup-inserted top wires purely from the V diagram (identify which top ports are cup legs
vs survivors) — which is the standing valley-descent residual (#2185).  No gate flag is flipped.  `= true`. -/
def fxMode_hasCupShiftReranking : Bool := true

end FX1Poly.Polygraph
