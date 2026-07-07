import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCapRestrict
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyMatchingSurjectivity
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyFloorHomogeneous
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingVcompLeftCongruence

/-! # ValleyTopCountTotal — the survivor-top total is the mid-width (Piece II tail, cap `topCount` field)

The full `DiagramType.ext` for `capRestrict` needs its `topCount` field: `survivorTopTotal V = midWidth`,
where `V = matchingOf bc (capBlock ++ cupBlock)` and `midWidth = capState.openWires.length` is the cap
block's own open-wire count (its number of through-strands).  Since the cup order embedding `phi` is
injective (strictly monotone) and the survivor-tops of `V` are EXACTLY its image (the shipped surjectivity
`survivorTop_iff_cupImage`), the total number of survivor-tops = `|image phi|` = `midWidth`.

This file lands:

  * ★ `countBelow_atStrictMonoImage_full_eq_sourceLength` — the abstract count identity: for a strictly-monotone
    `phi` whose image positions are EXACTLY the marked positions of `valBelow` (the same hypothesis bundle as the
    shipped `countBelow_atStrictMonoImage_eq_rank`), the count of ALL marked positions below `finalLength` is
    exactly `sourceLength`.  Counts up to and including the last image `phi (sourceLength-1)` by the shipped
    rank lemma, then slides an all-false window across the cup-leg tail `(phi (sourceLength-1), finalLength)`.

  * ★ `survivorTopTotal_eq_midWidth` — the concrete cap `topCount` field: the survivor-top total of the whole
    valley is the cap block's own open-wire count.  Every hypothesis of the abstract lemma is discharged from
    the SAME shipped seed-fact block as `capRestrict_partner_survivorBottom` (image cover, N1/N2 floor-separated
    roots, survivor bound), so it carries no residual.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local plumbing -/

/-- An in-range positional read is a member (local copy). -/
private theorem getAt_mem_of_lt : (wires : List Nat) → (index : Nat) →
    index < wires.length → natListGetAt wires index ∈ wires
  | [], _, indexInRange => absurd indexInRange (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, indexInRange =>
      List.Mem.tail _ (getAt_mem_of_lt rest index (Nat.lt_of_succ_lt_succ indexInRange))

/-! ## The abstract full-image count identity -/

/-- ★ **The full-image count identity.**  For a strictly-monotone `phi` marking EXACTLY the image positions of
`valBelow` (every source image `phi sourcePos` marked, every in-range unmarked position a non-image — the exact
hypothesis bundle of `countBelow_atStrictMonoImage_eq_rank`), the count of ALL marked positions strictly below
`finalLength` is exactly `sourceLength`.  When `sourceLength = 0` every position is a non-image, so the count is
zero; otherwise count up to and including the last image `phi (sourceLength-1)` (`= sourceLength` by the shipped
rank lemma plus the last image), then the tail window `(phi (sourceLength-1), finalLength)` is all non-image (by
the strict-monotone squeeze), contributing nothing. -/
theorem countBelow_atStrictMonoImage_full_eq_sourceLength {phi : Nat → Nat} {valBelow : Nat → Bool}
    {sourceLength finalLength : Nat}
    (strictMono : ∀ firstIndex secondIndex, firstIndex < secondIndex → phi firstIndex < phi secondIndex)
    (imageTrue : ∀ sourcePos, sourcePos < sourceLength → valBelow (phi sourcePos) = true)
    (rangeInv : ∀ sourcePos, sourcePos < sourceLength → phi sourcePos < finalLength)
    (nonImageFalse : ∀ offset, offset < finalLength →
        (∀ sourcePos, sourcePos < sourceLength → phi sourcePos ≠ offset) → valBelow offset = false) :
    countBelow valBelow finalLength = sourceLength := by
  cases sourceLength with
  | zero =>
      apply countBelow_eq_zero_of_allFalse
      intro offset offsetLt
      exact nonImageFalse offset offsetLt
        (fun sourcePos sourcePosLt _ => absurd sourcePosLt (Nat.not_lt_zero sourcePos))
  | succ lastRank =>
      have phiMono : ∀ {lowerIndex upperIndex : Nat}, lowerIndex ≤ upperIndex →
          phi lowerIndex ≤ phi upperIndex := by
        intro lowerIndex upperIndex leHyp
        rcases Nat.eq_or_lt_of_le leHyp with eqHyp | ltHyp
        · exact Nat.le_of_eq (congrArg phi eqHyp)
        · exact Nat.le_of_lt (strictMono lowerIndex upperIndex ltHyp)
      have lastImageLt : phi lastRank < finalLength := rangeInv lastRank (Nat.lt_succ_self lastRank)
      have countUpToLast : countBelow valBelow (phi lastRank) = lastRank :=
        countBelow_atStrictMonoImage_eq_rank strictMono imageTrue rangeInv nonImageFalse
          lastRank (Nat.lt_succ_self lastRank)
      have countInclLast : countBelow valBelow (phi lastRank + 1) = lastRank + 1 := by
        show countBelow valBelow (phi lastRank) + cond (valBelow (phi lastRank)) 1 0 = lastRank + 1
        rw [countUpToLast, imageTrue lastRank (Nat.lt_succ_self lastRank), cond_true_one]
      obtain ⟨width, widthEq⟩ := Nat.le.dest lastImageLt
      -- widthEq : phi lastRank + 1 + width = finalLength
      have windowZero : countBelow (fun offset => valBelow (phi lastRank + 1 + offset)) width = 0 := by
        apply countBelow_eq_zero_of_allFalse
        intro offset offsetLt
        have posLt : phi lastRank + 1 + offset < finalLength := by
          rw [← widthEq]; exact Nat.add_lt_add_left offsetLt (phi lastRank + 1)
        apply nonImageFalse _ posLt
        intro sourcePos sourcePosLt phiEq
        have srcLeLast : phi sourcePos ≤ phi lastRank :=
          phiMono (Nat.le_of_lt_succ sourcePosLt)
        have lastLtSrc : phi lastRank < phi sourcePos := by
          rw [phiEq]
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (phi lastRank))
            (Nat.le_add_right (phi lastRank + 1) offset)
        exact Nat.lt_irrefl (phi lastRank) (Nat.lt_of_lt_of_le lastLtSrc srcLeLast)
      rw [← widthEq, countBelow_add_eq valBelow (phi lastRank + 1) width, windowZero, Nat.add_zero,
        countInclLast]

/-! ## The concrete cap `topCount` field -/

/-- ★ **The survivor-top total is the mid-width.**  For a valley `capBlock ++ cupBlock` (pure cap block, pure
cup block, boundary-chained), the survivor-top total of the whole valley's `matchingOf` equals the cap block's
own open-wire count `midWidth` — the reconstructed `topCount` of `capRestrict`.  The count over the whole
boundary splits (`countBelow_add_eq`) into the bottom segment (never a survivor-top — all-false) and the top
offsets `[0, finalLen)`; over those the survivor-top predicate marks EXACTLY the cup-embedding images
(`survivorTop_iff_cupImage`, both directions), so `countBelow_atStrictMonoImage_full_eq_sourceLength` collapses
the count to `midWidth`.  Every hypothesis is discharged from the SAME shipped seed-fact block as
`capRestrict_partner_survivorBottom`. -/
theorem survivorTopTotal_eq_midWidth
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock)
    (cupChained : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock) :
    survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
      = (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length := by
  let capState := processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock
  let wholeState := processSpine capState cupBlock
  have wholeSplit : matchingOfSpineList bottomCount (capBlock ++ cupBlock)
      = extractDiagram bottomCount wholeState := by
    show extractDiagram bottomCount (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩
        (capBlock ++ cupBlock)) = extractDiagram bottomCount wholeState
    rw [processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩]
  rw [wholeSplit]
  -- survivorTopTotal (extractDiagram bc wholeState) = survivorTopCount … (bc + wholeState.openWires.length)
  show survivorTopCount (extractDiagram bottomCount wholeState)
      (bottomCount + wholeState.openWires.length) = capState.openWires.length
  rw [survivorTopCount_eq_countBelow,
    countBelow_add_eq (isSurvivorTop (extractDiagram bottomCount wholeState)) bottomCount
      wholeState.openWires.length]
  -- the bottom segment [0, bc) never passes isSurvivorTop
  have bottomZero :
      countBelow (isSurvivorTop (extractDiagram bottomCount wholeState)) bottomCount = 0 := by
    apply countBelow_eq_zero_of_allFalse
    intro index indexLt
    show (Nat.ble (extractDiagram bottomCount wholeState).bottomCount index
        && Nat.blt (natListGetAt (extractDiagram bottomCount wholeState).partner index)
            (extractDiagram bottomCount wholeState).bottomCount) = false
    have bleFalse : Nat.ble (extractDiagram bottomCount wholeState).bottomCount index = false := by
      cases hble : Nat.ble (extractDiagram bottomCount wholeState).bottomCount index with
      | false => rfl
      | true => exact absurd (Nat.le_of_ble_eq_true hble) (Nat.not_le.mpr indexLt)
    rw [bleFalse, Bool.false_and]
  rw [bottomZero, Nat.zero_add]
  -- assemble the cup embedding + cover from the same shipped seed facts as the survivor-bottom keystone
  have capNextFresh : capState.nextFresh = bottomCount :=
    processSpine_nextFresh_ofAllCapArity_seed bottomCount capBlock capPure
  obtain ⟨phi, embedding, cover⟩ := processSpine_wireOrderImageCover_ofAllCupArity bottomCount cupBlock cupPure
    capState capState.openWires.length rfl (Nat.le_of_eq capNextFresh.symm) cupChained
  have capFresh : WireStateFresh capState :=
    processSpine_wireStateFresh capBlock ⟨List.range bottomCount, [], bottomCount, 0⟩
      (wireStateFresh_initial bottomCount) bottomPositive
  have capEdgesBelow : ∀ edge ∈ capState.links, edge.1 < bottomCount ∧ edge.2 < bottomCount :=
    processSpine_links_below_ofAllCapArity_seed bottomCount bottomPositive capBlock capPure
  have capEdgesHomog : ∀ edge ∈ capState.links, edgeFloorHomogeneous bottomCount edge :=
    fun edge edgeIn =>
      ⟨fun floorLe => absurd floorLe (Nat.not_le.mpr (capEdgesBelow edge edgeIn).1),
       fun _ => (capEdgesBelow edge edgeIn).2⟩
  have wholeEdgesHomog : ∀ edge ∈ wholeState.links, edgeFloorHomogeneous bottomCount edge :=
    processSpine_edgesFloorHomogeneous_ofAllCupArity bottomCount cupBlock cupPure capState
      capFresh (Nat.le_of_eq capNextFresh.symm) capEdgesHomog
  have rootBelowFloor : ∀ node, node < bottomCount →
      unionFindRootOf wholeState.links node < bottomCount :=
    fun node nodeBelow =>
      unionFindRootOf_lt_of_edgesBelowFloor wholeState.links bottomCount
        (fun edge edgeIn => (wholeEdgesHomog edge edgeIn).2) node nodeBelow
  have rootAboveFloor : ∀ node, bottomCount ≤ node →
      bottomCount ≤ unionFindRootOf wholeState.links node :=
    fun node nodeAbove =>
      unionFindRootOf_ge_of_edgesPreserveFloor wholeState.links bottomCount
        (fun edge edgeIn => (wholeEdgesHomog edge edgeIn).1) node nodeAbove
  have survivorBelow : ∀ index, index < capState.openWires.length →
      natListGetAt capState.openWires index < bottomCount :=
    fun index indexLt =>
      processSpine_openWires_below_ofAllCapArity_seed bottomCount bottomPositive capBlock capPure
        (natListGetAt capState.openWires index) (getAt_mem_of_lt capState.openWires index indexLt)
  -- close by the abstract full-image count, marking positions via the shipped surjectivity
  exact countBelow_atStrictMonoImage_full_eq_sourceLength
    (sourceLength := capState.openWires.length) (finalLength := wholeState.openWires.length)
    embedding.strictMono
    (fun sourcePos sourceLt =>
      (survivorTop_iff_cupImage bottomCount wholeState capState.openWires (phi sourcePos)
        (embedding.inRange sourcePos sourceLt) rootBelowFloor rootAboveFloor embedding cover
        survivorBelow).mpr ⟨sourcePos, sourceLt, rfl⟩)
    (fun sourcePos sourceLt => embedding.inRange sourcePos sourceLt)
    (fun offset offsetLt noSrc => by
      cases hval : isSurvivorTop (extractDiagram bottomCount wholeState) (bottomCount + offset) with
      | false => rfl
      | true =>
          obtain ⟨sourcePos, sourceLt, phiEq⟩ :=
            (survivorTop_iff_cupImage bottomCount wholeState capState.openWires offset offsetLt
              rootBelowFloor rootAboveFloor embedding cover survivorBelow).mp hval
          exact absurd phiEq (noSrc sourcePos sourceLt))

/-! ## Honesty marker -/

/-- **Honesty marker — the cap `topCount` field `survivorTopTotal V = midWidth` is SHIPPED.**  Landed here,
zero-axiom:

  * `countBelow_atStrictMonoImage_full_eq_sourceLength` — for a strictly-monotone `phi` whose image is exactly
    the marked positions, the FULL count of marked positions below `finalLength` is `sourceLength` (`|image phi|`
    = domain size).  The full-window sibling of the shipped rank lemma `countBelow_atStrictMonoImage_eq_rank`.

  * `survivorTopTotal_eq_midWidth` — the concrete cap `topCount` field: the whole valley's survivor-top total is
    the cap block's own open-wire count.  All hypotheses discharged from the same shipped seed-fact block as the
    survivor-bottom keystone (image cover, floor-separated roots, survivor bound) — no residual.

This closes the `topCount` field of the full `capRestrict` `DiagramType.ext` (and, by the survivor-top total's
symmetry, the `bottomCount` field of the cup dual).  What this marker does NOT claim: the full field ext, the
cap-consumed partner leg, `valleyAppend_split`.  No gate flag is flipped.  `= true`. -/
def fxMode_hasValleyTopCountTotal : Bool := true

end FX1Poly.Polygraph
