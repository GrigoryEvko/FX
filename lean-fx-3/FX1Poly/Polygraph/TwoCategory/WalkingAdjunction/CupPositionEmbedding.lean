import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupImageCover

/-! # CupPositionEmbedding — the seed-agnostic CONCRETE cup position embedding (Piece II tail keystone)

The two shipped cup order-embedding lemmas — `processSpine_wireOrderEmbedding_ofAllCupArity`
(`ValleySurvivorOrder`) and `processSpine_wireOrderImageCover_ofAllCupArity` (`ValleyCupImageCover`) — both
return an EXISTENTIAL witness `∃ phi, WireOrderEmbedding phi …`, and both build that witness by the SAME fold
`fun index => phiRest (shiftPastPosition headAtom.leftContext.length 2 index)`.  Read off that fold: the witness
depends ONLY on the cup atoms' firing positions (`leftContext.length`), NOT on the mid-state's open-wire VALUES,
links, or counter.  It is seed-agnostic.

That seed-agnosticism is the crux of the CUP-side reconstruction's twin-instantiation route.  The cup block's own
matching `matchingOf midWidth cupBlock` runs from the from-scratch seed `⟨range midWidth, [], midWidth, 0⟩`
(bottoms `0 … midWidth-1`), whereas its action inside the whole valley runs from `capState` (bottoms the SCATTERED
survivor values, cap links present).  The two runs are related by a composite survivor-scatter-plus-leg-shift seed
rename — but the ORDER EMBEDDING `phi` is manufactured identically for both, because the fold only reads firing
positions.  So both runs re-rank through the SAME `phi`, and the survivor scatter cancels: this is what lets the
standalone-cup partner values coincide with the in-valley reconstructed values WITHOUT building the multi-cup
scatter-rename component fold.

The two shipped lemmas can only assert "there EXISTS a phi" — two separate `∃`-eliminations yield two OPAQUE
witnesses with no proof they agree.  This file supplies the missing structural piece: a CONCRETE
`cupPositionEmbedding` function (the fold, named), and re-proves both order-embedding facts about THIS concrete
function, so any two instantiations share one literal `phi = cupPositionEmbedding cupBlock`.

  * ★ `cupPositionEmbedding` — the concrete, seed-agnostic cup position embedding: the composite of the
    per-cup single-splice shifts `shiftPastPosition (leftContext.length) 2`, folded over the cup block.
  * ★ `cupPositionEmbedding_isWireOrderEmbedding` — the concrete form of
    `processSpine_wireOrderEmbedding_ofAllCupArity`: a pure-cup block order-embeds any boundary-tracking mid-state's
    open wires into the final open wires VIA `cupPositionEmbedding cupBlock`.
  * ★ `cupPositionEmbedding_imageCover` — the concrete form of `processSpine_wireOrderImageCover_ofAllCupArity`:
    the SAME `cupPositionEmbedding cupBlock` both order-embeds AND covers the below-floor survivors.

This is the keystone the cup-side twin-instantiation route needs (the residual `partner`-field cases still stand;
see the honesty marker).  No gate flag is flipped.

Raw Lean 4 + Init; structural / `AllCupArity` recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The concrete cup position embedding -/

/-- ★ **The concrete, seed-agnostic cup position embedding.**  For a pure-cup block, the composite position map
that each cup's single fresh-leg splice induces on the pre-existing wires, folded over the block:
`[]` embeds by the identity, and `headAtom :: rest` first shifts past the head cup's firing position
(`shiftPastPosition headAtom.leftContext.length 2`) then applies the tail's embedding.  Reads ONLY the atoms'
`leftContext.length` firing positions — nothing about the mid-state's open-wire values, links, or counter — so it
is IDENTICAL for the from-scratch cup seed and the in-valley `capState` seed.  This is the named form of the fold
that both `processSpine_wireOrderEmbedding_ofAllCupArity` and `processSpine_wireOrderImageCover_ofAllCupArity`
build anonymously under an `∃`. -/
def cupPositionEmbedding
    {overallSource overallTarget : adjunctionGraph.Mode} :
    List (SpineAtom adjunctionModeSignature overallSource overallTarget) → Nat → Nat
  | [] => fun index => index
  | headAtom :: rest => fun index =>
      cupPositionEmbedding rest (shiftPastPosition headAtom.leftContext.length 2 index)

/-! ## The concrete order-embedding fact -/

/-- ★ **The concrete cup order embedding.**  A pure-cup block order-embeds any boundary-tracking mid-state's open
wires into its final open wires VIA the concrete `cupPositionEmbedding atoms`.  Same induction as the shipped
`processSpine_wireOrderEmbedding_ofAllCupArity`, but the witness is NAMED — so two instantiations (the from-scratch
cup seed and the in-valley `capState`) share ONE literal position map, and the survivor scatter between them cancels
under the shared embedding. -/
theorem cupPositionEmbedding_isWireOrderEmbedding
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    (state : WireState) → (boundaryLength : Nat) →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    WireOrderEmbedding (cupPositionEmbedding atoms) state.openWires (processSpine state atoms).openWires := by
  induction pureCup with
  | nil =>
      intro state _ _ _
      exact wireOrderEmbedding_id state.openWires
  | cons hasCupDomArity hasCupCodArity _restAllCup restEmbed =>
      rename_i headAtom rest
      intro state boundaryLength tracks chained
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
      have embRest := restEmbed (stepCup state headAtom.leftContext.length) headAtom.codBoundaryLength
        newTracks tailChained
      have headEmbed := stepCup_wireOrderEmbedding state headAtom.leftContext.length posInRange
      show WireOrderEmbedding (cupPositionEmbedding (headAtom :: rest)) state.openWires
        (processSpine (stepAtom state headAtom) rest).openWires
      rw [stepAtom_ofCupArity state headAtom hasCupDomArity hasCupCodArity]
      exact wireOrderEmbedding_comp (phiFirst := shiftPastPosition headAtom.leftContext.length 2)
        (phiSecond := cupPositionEmbedding rest) headEmbed embRest

/-! ## The concrete image-cover fact -/

/-- ★ **The concrete cup image cover.**  The SAME concrete `cupPositionEmbedding atoms` both order-embeds the
mid-state's open wires and COVERS the below-floor survivors: every final open-wire position either lies in the
embedding's image (a survivor) or holds an at-or-above-floor value (a cup leg).  Concrete form of the shipped
`processSpine_wireOrderImageCover_ofAllCupArity` — the witness is `cupPositionEmbedding atoms`, so the cover and
the order embedding share ONE literal position map. -/
theorem cupPositionEmbedding_imageCover
    {overallSource overallTarget : adjunctionGraph.Mode} (freshFloor : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    (state : WireState) → (boundaryLength : Nat) →
    state.openWires.length = boundaryLength → freshFloor ≤ state.nextFresh →
    SpineBoundaryChained boundaryLength atoms →
    WireOrderEmbedding (cupPositionEmbedding atoms) state.openWires (processSpine state atoms).openWires ∧
      ∀ targetPos, targetPos < (processSpine state atoms).openWires.length →
        (∃ sourcePos, sourcePos < state.openWires.length ∧ cupPositionEmbedding atoms sourcePos = targetPos)
          ∨ freshFloor ≤ natListGetAt (processSpine state atoms).openWires targetPos := by
  induction pureCup with
  | nil =>
      intro state _ _ _ _
      refine ⟨wireOrderEmbedding_id state.openWires, ?_⟩
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
      obtain ⟨embRest, coverRest⟩ :=
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
      show WireOrderEmbedding (cupPositionEmbedding (headAtom :: rest)) state.openWires
          (processSpine (stepAtom state headAtom) rest).openWires ∧
        ∀ targetPos, targetPos < (processSpine (stepAtom state headAtom) rest).openWires.length →
          (∃ sourcePos, sourcePos < state.openWires.length
              ∧ cupPositionEmbedding (headAtom :: rest) sourcePos = targetPos)
            ∨ freshFloor ≤ natListGetAt (processSpine (stepAtom state headAtom) rest).openWires targetPos
      rw [stepAtom_ofCupArity state headAtom hasCupDomArity hasCupCodArity]
      refine ⟨wireOrderEmbedding_comp (phiFirst := shiftPastPosition headAtom.leftContext.length 2)
        (phiSecond := cupPositionEmbedding rest) headEmbed embRest, ?_⟩
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
                show cupPositionEmbedding rest (shiftPastPosition headAtom.leftContext.length 2 sourcePos)
                  = targetPos
                rw [shiftEq]; exact phiRestEq
      · exact Or.inr freshVal

/-! ## Honesty marker -/

/-- **Honesty marker — the CONCRETE seed-agnostic cup position embedding is SHIPPED; the cup-side reconstruction's
`partner`-field cases remain.**

Landed here, all zero-axiom:

  * `cupPositionEmbedding` — the concrete cup position embedding: the fold of the per-cup single-splice shifts
    `shiftPastPosition (leftContext.length) 2`, reading ONLY the atoms' firing positions.

  * `cupPositionEmbedding_isWireOrderEmbedding` / `cupPositionEmbedding_imageCover` — the concrete forms of the two
    shipped anonymous-witness lemmas: the SAME `cupPositionEmbedding atoms` order-embeds any boundary-tracking
    mid-state's open wires into the final open wires AND covers the below-floor survivors.

Why this is the twin-instantiation keystone: the two shipped lemmas assert only `∃ phi, …`; two separate
`∃`-eliminations (one for the from-scratch cup seed, one for the in-valley `capState`) yield two OPAQUE witnesses
with no proof they agree.  These concrete forms pin BOTH runs to one literal `phi = cupPositionEmbedding cupBlock`,
so the survivor scatter between the two seeds cancels under the shared embedding.

What this marker does NOT close — the full `cupRestrict_reconstructs` `partner` field (hence `valleyAppend_split`
and `valleysWithEqualMatching_spineTraceEquiv` stay gated).  Three cup-boundary partner cases remain, each needing
more than the embedding alone:

  * cup-BOTTOM `s < midWidth` — the standalone-cup partner `midWidth + cupPositionEmbedding cupBlock s` vs the
    reconstructed `midWidth + (nthSurvivorTop V s − bottomCount)`; needs the cup-side `nthSurvivorTop`-correctness
    (the in-valley through-strand re-ranking, `survivorPartner_throughCupBlock` + `nthSurvivorTop_correct`) pinned
    to THIS concrete embedding on both runs;

  * cup-TOP survivor-top — the involution mirror of the cup-bottom case (through-strand tops), plus the standing
    survivor-top-rank surjectivity residual #2185;

  * cup-TOP top-top cup arc — the genuinely asymmetric case with NO cap analogue: the standalone-cup and in-valley
    top-top link structure differ by the composite survivor-scatter seed rename over a NON-EMPTY base link list,
    whose multi-cup component fold is un-shipped.

fib-3 also carries the independent Piece-I beam (`MatchingReductsShareSpineTrace`, #1996), so `convOfMapEq` stays
gated regardless.  No gate flag is flipped.  `= true`. -/
def fxMode_hasConcreteCupPositionEmbedding : Bool := true

end FX1Poly.Polygraph
