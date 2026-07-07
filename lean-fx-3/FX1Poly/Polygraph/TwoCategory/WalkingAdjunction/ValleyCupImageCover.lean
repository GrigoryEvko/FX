import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleySurvivorOrder
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # ValleyCupImageCover — the cup fold's value-surjectivity (image-complement half of #2185)

`ValleySurvivorOrder` produced the cup block's order embedding `phi` (`WireOrderEmbedding`, strictly
monotone / value-preserving / in-range) of a boundary-tracking mid-state's open wires into the whole
valley's final open wires.  The order embedding says the survivors keep their relative order — but it does
NOT say WHICH final positions are survivors and which are freshly-spliced cup legs.  The backward
re-ranking (the surjectivity residual #2185) needs exactly that split: every final open wire whose VALUE
is a survivor value (below the fresh floor `bc`) sits at a position IN THE IMAGE of `phi`; the positions
OUTSIDE the image are precisely the cup legs (values at or above the floor).

This file lands the IMAGE-COMPLEMENT (value-surjectivity) half.  It is a pure `natListInsertAt`-fold fact
about the OPEN-WIRE LIST — it never mentions `partnerIndexOf`, `monotoneMapOf`, or `SaturatedTwoCellConv`,
so it is structurally independent of the machine-refuted covariant-monotone reconstruction map (which was
refuted as a `SaturatedTwoCellConv` invariant on the cell carrier, not as an insert-fold's image
characterization on the open-wire list).

  * `shiftPastPosition_surjOffBlock` — the single-splice position map `shiftPastPosition position 2` hits
    every target position EXCEPT the two just-spliced positions `position`, `position + 1`.
  * ★ `processSpine_wireOrderImageCover_ofAllCupArity` — THE value-surjectivity leg: a pure-cup block
    order-embeds any boundary-tracking mid-state's open wires into the final open wires by a `phi`
    (`WireOrderEmbedding`) whose image COVERS every final position holding a below-floor value — every
    such position is `phi sourcePos` for an in-range source position, and every position OUTSIDE the image
    holds an at-or-above-floor value (a cup leg).  The floor `freshFloor ≤ state.nextFresh` bounds the
    fresh cup legs below.

Raw Lean 4 + Init; structural / `AllCupArity` recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The single-splice position map surjects off the two spliced positions -/

/-- ★ **The splice position map hits everything but its own two spliced positions.**  For a splice of a
length-2 block at `position` (with `position ≤ sourceLength`), any target position `targetPos` in range
(`< sourceLength + 2`) that is NEITHER of the two spliced positions `position`, `position + 1` is the image
`shiftPastPosition position 2 sourcePos` of an in-range source position: below `position` the map is the
identity, at or above `position + 2` it is `· + 2`.  This is the surjectivity witness the image-cover fold
needs at each cup step — the complement of the splice image is exactly the two fresh legs. -/
theorem shiftPastPosition_surjOffBlock (position sourceLength targetPos : Nat)
    (posLe : position ≤ sourceLength) (targetInRange : targetPos < sourceLength + 2)
    (notLeftLeg : targetPos ≠ position) (notRightLeg : targetPos ≠ position + 1) :
    ∃ sourcePos, sourcePos < sourceLength ∧ shiftPastPosition position 2 sourcePos = targetPos := by
  rcases Nat.lt_or_ge targetPos position with belowPos | atOrAbove
  · refine ⟨targetPos, Nat.lt_of_lt_of_le belowPos posLe, ?_⟩
    show (if targetPos < position then targetPos else targetPos + 2) = targetPos
    rw [if_pos belowPos]
  · have posLtTarget : position < targetPos := Nat.lt_of_le_of_ne atOrAbove (fun eq => notLeftLeg eq.symm)
    have succLtTarget : position + 1 < targetPos :=
      Nat.lt_of_le_of_ne posLtTarget (fun eq => notRightLeg eq.symm)
    obtain ⟨offset, offsetEq⟩ := Nat.le.dest succLtTarget
    -- offsetEq : position + 1 + 1 + offset = targetPos, i.e. position + 2 + offset = targetPos
    refine ⟨position + offset, ?_, ?_⟩
    · have sumLt : position + offset + 2 < sourceLength + 2 := by
        show position + offset + 2 < sourceLength + 2
        have rewriteSum : position + offset + 2 = targetPos := by
          rw [Nat.add_right_comm position offset 2]
          exact offsetEq
        rw [rewriteSum]; exact targetInRange
      exact Nat.lt_of_add_lt_add_right sumLt
    · have notBelow : ¬ position + offset < position :=
        Nat.not_lt.mpr (Nat.le_add_right position offset)
      show (if position + offset < position then position + offset else position + offset + 2) = targetPos
      rw [if_neg notBelow, Nat.add_right_comm position offset 2]
      exact offsetEq

/-! ## The value-surjectivity leg -/

/-- ★ **Value-surjectivity — a pure-cup block order-embeds any boundary-tracking mid-state's open wires so
that the image COVERS every below-floor final position.**  Run from a state whose open wires have length
exactly the running boundary (`tracks`), whose fresh counter sits at or above the floor
(`freshLe : freshFloor ≤ state.nextFresh`), and whose atoms are boundary-chained (`chained`), a pure-cup
block splices only fresh legs (values `≥ freshFloor`, the counter only rising).  The resulting `phi` is the
same strictly-monotone, value-preserving, in-range order embedding as
`processSpine_wireOrderEmbedding_ofAllCupArity`, and additionally its image COVERS the survivors: every
final position `targetPos` either is `phi sourcePos` for an in-range source position, or holds an
at-or-above-floor value (a cup leg).  By induction on the `AllCupArity` witness: each cup at
`leftContext.length` splices `[nextFresh, nextFresh + 1]` (both `≥ freshFloor`); the tail's cover pulls
back through `shiftPastPosition` — an image position that is one of the two just-spliced legs reads a
fresh value (right disjunct), any other tail-image position is `shiftPastPosition`-surjective onto a source
position (`shiftPastPosition_surjOffBlock`), and a tail cup leg stays a cup leg.  This is the
image-complement half of the surjectivity residual #2185, on the OPEN-WIRE list (independent of the refuted
partner-map reconstruction). -/
theorem processSpine_wireOrderImageCover_ofAllCupArity
    {overallSource overallTarget : adjunctionGraph.Mode} (freshFloor : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    (state : WireState) → (boundaryLength : Nat) →
    state.openWires.length = boundaryLength → freshFloor ≤ state.nextFresh →
    SpineBoundaryChained boundaryLength atoms →
    ∃ phi, WireOrderEmbedding phi state.openWires (processSpine state atoms).openWires ∧
      ∀ targetPos, targetPos < (processSpine state atoms).openWires.length →
        (∃ sourcePos, sourcePos < state.openWires.length ∧ phi sourcePos = targetPos)
          ∨ freshFloor ≤ natListGetAt (processSpine state atoms).openWires targetPos := by
  induction pureCup with
  | nil =>
      intro state _ _ _ _
      refine ⟨fun index => index, wireOrderEmbedding_id state.openWires, ?_⟩
      intro targetPos targetInRange
      exact Or.inl ⟨targetPos, targetInRange, rfl⟩
  | cons hasCupDomArity hasCupCodArity _restAllCup restCover =>
      rename_i headAtom rest
      intro state boundaryLength tracks freshLe chained
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have posLeBoundary : headAtom.leftContext.length ≤ boundaryLength := by
        rw [← headFires]
        show headAtom.leftContext.length
          ≤ headAtom.leftContext.length + headAtom.generatorDom.length + headAtom.rightContext.length
        rw [hasCupDomArity, Nat.add_zero]
        exact Nat.le_add_right headAtom.leftContext.length headAtom.rightContext.length
      have posInRange : headAtom.leftContext.length ≤ state.openWires.length := by
        rw [tracks]; exact posLeBoundary
      have newTracks : (stepCup state headAtom.leftContext.length).openWires.length
          = headAtom.codBoundaryLength := by
        rw [stepCup_openWires, natListInsertAt_length]
        show state.openWires.length + 2 = headAtom.codBoundaryLength
        rw [tracks, ← headFires]
        show headAtom.leftContext.length + headAtom.generatorDom.length + headAtom.rightContext.length + 2
          = headAtom.leftContext.length + headAtom.generatorCod.length + headAtom.rightContext.length
        rw [hasCupDomArity, hasCupCodArity, Nat.add_zero]
        exact Nat.add_right_comm headAtom.leftContext.length headAtom.rightContext.length 2
      have newFresh : freshFloor ≤ (stepCup state headAtom.leftContext.length).nextFresh := by
        rw [stepCup_nextFresh]
        exact Nat.le_trans freshLe (Nat.le_add_right state.nextFresh 2)
      obtain ⟨phiRest, embRest, coverRest⟩ :=
        restCover (stepCup state headAtom.leftContext.length) headAtom.codBoundaryLength newTracks
          newFresh tailChained
      have headEmbed := stepCup_wireOrderEmbedding state headAtom.leftContext.length posInRange
      have legValueLeft : natListGetAt (stepCup state headAtom.leftContext.length).openWires
          headAtom.leftContext.length = state.nextFresh := by
        rw [stepCup_openWires]
        have inside := natListGetAt_natListInsertAt_inside state.openWires headAtom.leftContext.length
          [state.nextFresh, state.nextFresh + 1] 0 (Nat.succ_pos 1) posInRange
        rw [Nat.add_zero] at inside
        exact inside
      have legValueRight : natListGetAt (stepCup state headAtom.leftContext.length).openWires
          (headAtom.leftContext.length + 1) = state.nextFresh + 1 := by
        rw [stepCup_openWires]
        exact natListGetAt_natListInsertAt_inside state.openWires headAtom.leftContext.length
          [state.nextFresh, state.nextFresh + 1] 1 (Nat.lt_succ_self 1) posInRange
      have stepLen : (stepCup state headAtom.leftContext.length).openWires.length
          = state.openWires.length + 2 := by
        rw [stepCup_openWires]
        exact natListInsertAt_length state.openWires headAtom.leftContext.length
          [state.nextFresh, state.nextFresh + 1]
      show ∃ phi, WireOrderEmbedding phi state.openWires
          (processSpine (stepAtom state headAtom) rest).openWires ∧
        ∀ targetPos, targetPos < (processSpine (stepAtom state headAtom) rest).openWires.length →
          (∃ sourcePos, sourcePos < state.openWires.length ∧ phi sourcePos = targetPos)
            ∨ freshFloor ≤ natListGetAt (processSpine (stepAtom state headAtom) rest).openWires targetPos
      rw [stepAtom_ofCupArity state headAtom hasCupDomArity hasCupCodArity]
      refine ⟨fun index => phiRest (shiftPastPosition headAtom.leftContext.length 2 index),
        wireOrderEmbedding_comp headEmbed embRest, ?_⟩
      intro targetPos targetInRange
      rcases coverRest targetPos targetInRange with ⟨midPos, midInRange, phiRestEq⟩ | freshVal
      · have midInRange' : midPos < state.openWires.length + 2 := stepLen ▸ midInRange
        match Nat.decEq midPos headAtom.leftContext.length with
        | isTrue midIsLeft =>
            have readEq := embRest.reads midPos midInRange
            rw [phiRestEq, midIsLeft, legValueLeft] at readEq
            exact Or.inr (by rw [readEq]; exact freshLe)
        | isFalse midNeLeft =>
            match Nat.decEq midPos (headAtom.leftContext.length + 1) with
            | isTrue midIsRight =>
                have readEq := embRest.reads midPos midInRange
                rw [phiRestEq, midIsRight, legValueRight] at readEq
                exact Or.inr (by rw [readEq]; exact Nat.le_trans freshLe (Nat.le_succ state.nextFresh))
            | isFalse midNeRight =>
                obtain ⟨sourcePos, sourceLt, shiftEq⟩ :=
                  shiftPastPosition_surjOffBlock headAtom.leftContext.length state.openWires.length
                    midPos posInRange midInRange' midNeLeft midNeRight
                refine Or.inl ⟨sourcePos, sourceLt, ?_⟩
                show phiRest (shiftPastPosition headAtom.leftContext.length 2 sourcePos) = targetPos
                rw [shiftEq]; exact phiRestEq
      · exact Or.inr freshVal

/-! ## Honesty marker -/

/-- **Honesty marker — the value-surjectivity (image-complement) leg of #2185 is SHIPPED; the union-find
CLASSIFICATION half and valley normalization remain.**

Landed here, all zero-axiom:

  * `processSpine_wireOrderImageCover_ofAllCupArity` — a pure-cup block's order embedding `phi` COVERS the
    survivors: every final open-wire position holding a below-floor value is `phi sourcePos` for an in-range
    source position, and every position outside `phi`'s image holds an at-or-above-floor value (a cup leg).
    A pure `natListInsertAt`-fold fact about the OPEN-WIRE list — the "final open wires = survivor images
    ⊔ cup legs" partition, in value terms.  Built from the single-splice surjectivity
    `shiftPastPosition_surjOffBlock` folded over the cup block through the order-embedding monoid.

    This is the half of the surjectivity residual #2185 that Route 1 flagged as most likely to close and
    structurally independent of the machine-refuted covariant-monotone reconstruction: that refutation
    indicted a `List Nat` covariant fold as a `SaturatedTwoCellConv` invariant on the CELL carrier; this
    lemma characterizes an insert-fold's image complement on the OPEN-WIRE carrier and never touches
    `partnerIndexOf` / `monotoneMapOf` / `SaturatedTwoCellConv`.

What this marker does NOT claim: the full surjectivity `isSurvivorTop (matchingOf bc V) (bc + p) = true ↔
(∃ r < midWidth, phi r = p)`.  Bridging the value-cover here to `isSurvivorTop` requires the union-find
CLASSIFICATION `isSurvivorTop (matchingOf bc V) (bc + p) = decide (natListGetAt wholeOpen p < bc)` — that a
below-floor top port is matched to a bottom (partner `< bc`) and a cup-leg top port to another top
(partner `≥ bc`), which needs the whole-valley fresh-root separation (a cup leg's root stays `≥ bc`,
disjoint from every bottom root) beyond the open-wire combinatorics landed here.  And even the full
surjectivity closes only `valleyAppend_split` over cells ALREADY in pure `capBlock ++ cupBlock` valley
form; the keystone `convOfMapEq` over ARBITRARY cells additionally needs valley normalization (a
matching-preserving saturated reduct of any cell to valley form — the spine-position-to-cell-subterm
bridge plus the well-founded termination assembly).  No gate flag is flipped.  `= true`. -/
def fxMode_hasValleyCupImageCover : Bool := true

end FX1Poly.Polygraph
