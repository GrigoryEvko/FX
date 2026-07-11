import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupImageCover
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSeed

/-! # WalkingString/StringCupPositionEmbedding — the seed-agnostic CONCRETE cup position embedding over the walking
ADJOINT-TRIPLE (`F ⊣ G ⊣ H`) signature (FC-3 r33, B5 keystone: the cup-side twin-instantiation position map)

The string clone of the walking-adjunction `CupPositionEmbedding` keystone.  The two cup order-embedding facts both
return an EXISTENTIAL witness `∃ phi, WireOrderEmbedding phi …`, built by the SAME fold
`fun index => phiRest (shiftPastPosition headAtom.leftContext.length 2 index)` — reading ONLY the cup atoms' firing
positions (`leftContext.length`), NOT the mid-state's open-wire VALUES, links, or counter.  That seed-agnosticism is
the crux of the CUP-side reconstruction's twin-instantiation route: the cup block's own matching runs from the
from-scratch seed `⟨range midWidth, [], midWidth, 0⟩`, whereas its action inside the whole valley runs from
`capState`, and the two runs re-rank through the SAME `stringCupPositionEmbedding cupBlock` so the survivor scatter
cancels.  This file supplies the missing structural piece: a CONCRETE named function and both order-embedding facts
about THIS function, so any two instantiations share one literal `phi = stringCupPositionEmbedding cupBlock`.

The order-embedding substrate (`stepCup_wireOrderEmbedding`, `wireOrderEmbedding_id` / `wireOrderEmbedding_comp`,
`shiftPastPosition_surjOffBlock`, `natListGetAt_natListInsertAt_inside`, `natListInsertAt_length`,
`spineBoundaryChained_tail`, `stepCup_openWires` / `stepCup_nextFresh`, `stepAtom_ofCupArity`) is signature-BLIND
(stated over bare `WireState` / `Nat` or `{signature}`-generic), so it is REUSED verbatim by import; every brick
below is a byte-identical token-swap of the walking-adjunction original, rerouting the signature token alone
`adjunctionModeSignature → adjointTripleModeSignature`.  No new mathematics, no unproven residual.

  * ★ `stringCupPositionEmbedding` — the concrete, seed-agnostic cup position embedding: the composite of the
    per-cup single-splice shifts `shiftPastPosition (leftContext.length) 2`, folded over the cup block.
  * ★ `stringCupPositionEmbedding_isWireOrderEmbedding` — the concrete form of the order embedding: a pure-cup block
    order-embeds any boundary-tracking mid-state's open wires into the final open wires VIA
    `stringCupPositionEmbedding cupBlock`.
  * ★ `stringCupPositionEmbedding_imageCover` — the concrete image cover: the SAME `stringCupPositionEmbedding
    cupBlock` both order-embeds AND covers the below-floor survivors.

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
is IDENTICAL for the from-scratch cup seed and the in-valley `capState` seed. -/
def stringCupPositionEmbedding
    {overallSource overallTarget : adjointTripleGraph.Mode} :
    List (SpineAtom adjointTripleModeSignature overallSource overallTarget) → Nat → Nat
  | [] => fun index => index
  | headAtom :: rest => fun index =>
      stringCupPositionEmbedding rest (shiftPastPosition headAtom.leftContext.length 2 index)

/-! ## The concrete order-embedding fact -/

/-- ★ **The concrete cup order embedding.**  A pure-cup block order-embeds any boundary-tracking mid-state's open
wires into its final open wires VIA the concrete `stringCupPositionEmbedding atoms`.  Same induction as the shipped
`processSpine_wireOrderEmbedding_ofAllCupArity`, but the witness is NAMED — so two instantiations (the from-scratch
cup seed and the in-valley `capState`) share ONE literal position map. -/
theorem stringCupPositionEmbedding_isWireOrderEmbedding
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    (state : WireState) → (boundaryLength : Nat) →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    WireOrderEmbedding (stringCupPositionEmbedding atoms) state.openWires (processSpine state atoms).openWires := by
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
      show WireOrderEmbedding (stringCupPositionEmbedding (headAtom :: rest)) state.openWires
        (processSpine (stepAtom state headAtom) rest).openWires
      rw [stepAtom_ofCupArity state headAtom hasCupDomArity hasCupCodArity]
      exact wireOrderEmbedding_comp (phiFirst := shiftPastPosition headAtom.leftContext.length 2)
        (phiSecond := stringCupPositionEmbedding rest) headEmbed embRest

/-! ## The concrete image-cover fact -/

/-- ★ **The concrete cup image cover.**  The SAME concrete `stringCupPositionEmbedding atoms` both order-embeds the
mid-state's open wires and COVERS the below-floor survivors: every final open-wire position either lies in the
embedding's image (a survivor) or holds an at-or-above-floor value (a cup leg).  Concrete form of the shipped
`processSpine_wireOrderImageCover_ofAllCupArity` — the witness is `stringCupPositionEmbedding atoms`, so the cover
and the order embedding share ONE literal position map. -/
theorem stringCupPositionEmbedding_imageCover
    {overallSource overallTarget : adjointTripleGraph.Mode} (freshFloor : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    (state : WireState) → (boundaryLength : Nat) →
    state.openWires.length = boundaryLength → freshFloor ≤ state.nextFresh →
    SpineBoundaryChained boundaryLength atoms →
    WireOrderEmbedding (stringCupPositionEmbedding atoms) state.openWires (processSpine state atoms).openWires ∧
      ∀ targetPos, targetPos < (processSpine state atoms).openWires.length →
        (∃ sourcePos, sourcePos < state.openWires.length ∧ stringCupPositionEmbedding atoms sourcePos = targetPos)
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
      show WireOrderEmbedding (stringCupPositionEmbedding (headAtom :: rest)) state.openWires
          (processSpine (stepAtom state headAtom) rest).openWires ∧
        ∀ targetPos, targetPos < (processSpine (stepAtom state headAtom) rest).openWires.length →
          (∃ sourcePos, sourcePos < state.openWires.length
              ∧ stringCupPositionEmbedding (headAtom :: rest) sourcePos = targetPos)
            ∨ freshFloor ≤ natListGetAt (processSpine (stepAtom state headAtom) rest).openWires targetPos
      rw [stepAtom_ofCupArity state headAtom hasCupDomArity hasCupCodArity]
      refine ⟨wireOrderEmbedding_comp (phiFirst := shiftPastPosition headAtom.leftContext.length 2)
        (phiSecond := stringCupPositionEmbedding rest) headEmbed embRest, ?_⟩
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
                show stringCupPositionEmbedding rest (shiftPastPosition headAtom.leftContext.length 2 sourcePos)
                  = targetPos
                rw [shiftEq]; exact phiRestEq
      · exact Or.inr freshVal

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the string CONCRETE seed-agnostic cup position embedding is SHIPPED, zero-axiom (FC-3 r33, B5
keystone).**  Landed here over the walking ADJOINT-TRIPLE signature as a byte-identical token-swap of the
walking-adjunction `CupPositionEmbedding`:

  * `stringCupPositionEmbedding` — the concrete cup position embedding: the fold of the per-cup single-splice shifts
    `shiftPastPosition (leftContext.length) 2`, reading ONLY the atoms' firing positions;
  * `stringCupPositionEmbedding_isWireOrderEmbedding` / `stringCupPositionEmbedding_imageCover` — the concrete forms
    of the two anonymous-witness order-embedding facts: the SAME `stringCupPositionEmbedding atoms` order-embeds any
    boundary-tracking mid-state's open wires into the final open wires AND covers the below-floor survivors.

The order-embedding substrate (`stepCup_wireOrderEmbedding` / `wireOrderEmbedding_{id,comp}` /
`shiftPastPosition_surjOffBlock` / `natListGetAt_natListInsertAt_inside` / `natListInsertAt_length` /
`spineBoundaryChained_tail` / `stepCup_{openWires,nextFresh}` / `stepAtom_ofCupArity`) is signature-BLIND — all
REUSED verbatim by import.  This is the twin-instantiation keystone the string cup-side reconstruction consumes: it
pins BOTH cup runs to one literal `phi = stringCupPositionEmbedding cupBlock`, so the survivor scatter between the
two seeds cancels under the shared embedding.  No gate flag is flipped.  `= true`. -/
def fxString_hasConcreteCupPositionEmbedding : Bool := true

end FX1Poly.Polygraph
