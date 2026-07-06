import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingCupPositions
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLegSeparation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusCupPreservation
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommute
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowLocality
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # ArcNonCrossingCupPreservation — stepCupArc preserves ArcNonCrossing (cup rung D2a-iii)

The main preservation theorem's first ingredient: a boundary end token of the spliced state is
either an OLD-ZONE read (union-find node strictly below `nextFresh`, so invisible to the fresh cup
component) or one of the two new cup legs (`openSlot position` / `openSlot (position+1)`).  This is
the classification that lets the crossing argument split every same-component arc into "both legs"
(an adjacent innermost cup — nothing can interleave) or "both old-zone" (backmaps to an old
crossing).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private read-membership plumbing (per-file copy, following the codebase pattern) -/

private theorem natListGetAt_mem_inRange : (wires : List Nat) → (index : Nat) →
    index < wires.length → natListGetAt wires index ∈ wires
  | [], _, indexInRange => absurd indexInRange (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, indexInRange =>
      List.Mem.tail _ (natListGetAt_mem_inRange rest index (Nat.lt_of_succ_lt_succ indexInRange))

/-! ## Private clean Nat-subtraction plumbing (Init's cancel/pos lemmas leak propext) -/

/-- `(start + amount) - start = amount`, hand-rolled clean. -/
private theorem addSubCancelLeft : (start amount : Nat) → (start + amount) - start = amount
  | 0, amount => by rw [Nat.zero_add, Nat.sub_zero]
  | start + 1, amount => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact addSubCancelLeft start amount

/-- Non-strict antitone: `smaller ≤ larger → minuend - larger ≤ minuend - smaller`. -/
private theorem subMonotoneLe (minuend smaller larger : Nat) (order : smaller ≤ larger) :
    minuend - larger ≤ minuend - smaller := by
  obtain ⟨gap, gapEq⟩ := Nat.le.dest order
  rw [← gapEq]
  clear gapEq order
  induction gap with
  | zero => rw [Nat.add_zero]; exact Nat.le_refl _
  | succ gapPred inductiveHypothesis =>
      rw [Nat.add_succ, Nat.sub_succ]
      exact Nat.le_trans (Nat.pred_le (minuend - (smaller + gapPred))) inductiveHypothesis

/-- Strict antitone on the valid range: `smaller < larger ≤ minuend → minuend - larger < minuend
- smaller`. -/
private theorem subStrictAntitone (minuend smaller larger : Nat)
    (order : smaller < larger) (largerLe : larger ≤ minuend) :
    minuend - larger < minuend - smaller := by
  obtain ⟨rest, restEq⟩ := Nat.le.dest largerLe
  obtain ⟨diff, diffEq⟩ := Nat.le.dest (Nat.le_of_lt order)
  have diffPos : 0 < diff := Nat.pos_of_ne_zero (fun diffZero => by
    rw [diffZero, Nat.add_zero] at diffEq
    exact Nat.lt_irrefl smaller (diffEq.symm ▸ order))
  have lowSide : minuend - larger = rest := by
    rw [← restEq]; exact addSubCancelLeft larger rest
  have highSide : minuend - smaller = diff + rest := by
    have expand : minuend = smaller + (diff + rest) := by
      rw [← restEq, ← diffEq, Nat.add_assoc]
    rw [expand]; exact addSubCancelLeft smaller (diff + rest)
  rw [lowSide, highSide, Nat.add_comm diff rest]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self rest) (Nat.add_le_add_left diffPos rest)

/-- `index < bound → index ≤ bound - 1`, hand-rolled clean. -/
private theorem ltImpliesLePred : (index bound : Nat) → index < bound → index ≤ bound - 1
  | _, 0, indexLt => absurd indexLt (Nat.not_lt_zero _)
  | _, _ + 1, indexLt => Nat.le_of_lt_succ indexLt

/-- The cup splice backmap is strictly monotone on old-zone open-slot indices: below-window slots
map to themselves, past-window slots shift down by two, and both preserve strict order. -/
private theorem cupBackslotMonotone (position slotSmaller slotLarger : Nat)
    (zoneSmaller : slotSmaller < position ∨ position + 2 ≤ slotSmaller)
    (zoneLarger : slotLarger < position ∨ position + 2 ≤ slotLarger)
    (slotOrder : slotSmaller < slotLarger) :
    (if slotSmaller < position then slotSmaller else slotSmaller - 2)
      < (if slotLarger < position then slotLarger else slotLarger - 2) := by
  cases zoneSmaller with
  | inl smallerBelow =>
      rw [if_pos smallerBelow]
      cases zoneLarger with
      | inl largerBelow =>
          rw [if_pos largerBelow]; exact slotOrder
      | inr largerPast =>
          have notLargerBelow : ¬ slotLarger < position := fun largerBelow =>
            Nat.lt_irrefl position (Nat.lt_of_le_of_lt
              (Nat.le_trans (Nat.le_add_right position 2) largerPast) largerBelow)
          rw [if_neg notLargerBelow]
          obtain ⟨gap, gapEq⟩ := Nat.le.dest largerPast
          have slotForm : slotLarger = position + gap + 2 :=
            gapEq.symm.trans (Nat.add_right_comm position 2 gap)
          rw [slotForm]
          exact Nat.lt_of_lt_of_le smallerBelow (Nat.le_add_right position gap)
  | inr smallerPast =>
      have notSmallerBelow : ¬ slotSmaller < position := fun smallerBelow =>
        Nat.lt_irrefl position (Nat.lt_of_le_of_lt
          (Nat.le_trans (Nat.le_add_right position 2) smallerPast) smallerBelow)
      rw [if_neg notSmallerBelow]
      have notLargerBelow : ¬ slotLarger < position := fun largerBelow =>
        Nat.lt_irrefl position (Nat.lt_of_le_of_lt
          (Nat.le_trans (Nat.le_trans (Nat.le_add_right position 2) smallerPast)
            (Nat.le_of_lt slotOrder)) largerBelow)
      rw [if_neg notLargerBelow]
      obtain ⟨gapSmaller, gapSmallerEq⟩ := Nat.le.dest smallerPast
      have smallerForm : slotSmaller = position + gapSmaller + 2 :=
        gapSmallerEq.symm.trans (Nat.add_right_comm position 2 gapSmaller)
      obtain ⟨gapLarger, gapLargerEq⟩ :=
        Nat.le.dest (Nat.le_trans smallerPast (Nat.le_of_lt slotOrder))
      have largerForm : slotLarger = position + gapLarger + 2 :=
        gapLargerEq.symm.trans (Nat.add_right_comm position 2 gapLarger)
      rw [smallerForm, largerForm]
      exact Nat.lt_of_add_lt_add_right
        (show position + gapSmaller + 2 < position + gapLarger + 2 by
          rw [← smallerForm, ← largerForm]; exact slotOrder)

/-! ## The token node classification -/

/-- ★ **A valid boundary token of the spliced state is old-zone or a new leg.**  Bottom ports and
below/past-window open slots read a wire strictly below `nextFresh`; the two window slots ARE the
freshly allocated cup legs. -/
theorem arcCupTokenNodeClass (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (cupInRange : position ≤ state.openWires.length)
    (token : ArcEndToken)
    (valid : isValidArcEndToken seedBoundary (stepCupArc state position) token) :
    arcEndTokenNode (stepCupArc state position) token < state.nextFresh
      ∨ token = ArcEndToken.openSlot position
      ∨ token = ArcEndToken.openSlot (position + 1) := by
  cases token with
  | bottomPort portValue =>
      exact Or.inl (Nat.lt_of_lt_of_le valid seedBelowFresh)
  | openSlot slot =>
      rcases Nat.lt_or_ge slot position with slotBelow | slotAtLeast
      · have slotBelowLen : slot < state.openWires.length :=
          Nat.lt_of_lt_of_le slotBelow cupInRange
        have readEq : arcEndTokenNode (stepCupArc state position) (ArcEndToken.openSlot slot)
            = natListGetAt state.openWires slot :=
          natListGetAt_natListInsertAt_below state.openWires position
            [state.nextFresh, state.nextFresh + 1] slot slotBelow slotBelowLen
        exact Or.inl (by
          rw [readEq]
          exact fresh.1 (natListGetAt state.openWires slot)
            (natListGetAt_mem_inRange state.openWires slot slotBelowLen))
      · rcases Nat.lt_or_ge slot (position + 1) with slotAtPos | slotPastPos
        · have slotEqPos : slot = position :=
            Nat.le_antisymm (Nat.le_of_lt_succ slotAtPos) slotAtLeast
          exact Or.inr (Or.inl (by rw [slotEqPos]))
        · rcases Nat.lt_or_ge slot (position + 2) with slotAtPosOne | slotPast
          · have slotEqPosOne : slot = position + 1 :=
              Nat.le_antisymm (Nat.le_of_lt_succ slotAtPosOne) slotPastPos
            exact Or.inr (Or.inr (by rw [slotEqPosOne]))
          · obtain ⟨extra, extraEq⟩ := Nat.le.dest slotPast
            have slotForm : slot = position + extra + 2 := by
              rw [← extraEq, Nat.add_right_comm]
            have readEq : arcEndTokenNode (stepCupArc state position) (ArcEndToken.openSlot slot)
                = natListGetAt state.openWires (position + extra) := by
              show natListGetAt (natListInsertAt state.openWires position
                  [state.nextFresh, state.nextFresh + 1]) slot
                = natListGetAt state.openWires (position + extra)
              rw [slotForm]
              exact natListGetAt_natListInsertAt_pastBlock state.openWires position
                [state.nextFresh, state.nextFresh + 1] extra cupInRange
            have validLen : slot < (stepCupArc state position).openWires.length := valid
            rw [arcCupNewOpenLength, slotForm] at validLen
            have posExtraLen : position + extra < state.openWires.length :=
              Nat.lt_of_add_lt_add_right validLen
            exact Or.inl (by
              rw [readEq]
              exact fresh.1 (natListGetAt state.openWires (position + extra))
                (natListGetAt_mem_inRange state.openWires (position + extra) posExtraLen))

/-! ## The two cup-leg node values -/

/-- The left cup leg (window slot `position`) reads the freshly allocated node `nextFresh`. -/
theorem arcCupLeftLegNode (state : ArcWireState) (position : Nat)
    (cupInRange : position ≤ state.openWires.length) :
    arcEndTokenNode (stepCupArc state position) (ArcEndToken.openSlot position)
      = state.nextFresh :=
  natListGetAt_natListInsertAt_inside state.openWires position
    [state.nextFresh, state.nextFresh + 1] 0 (Nat.succ_pos 1) cupInRange

/-- The right cup leg (window slot `position+1`) reads the freshly allocated node `nextFresh+1`. -/
theorem arcCupRightLegNode (state : ArcWireState) (position : Nat)
    (cupInRange : position ≤ state.openWires.length) :
    arcEndTokenNode (stepCupArc state position) (ArcEndToken.openSlot (position + 1))
      = state.nextFresh + 1 :=
  natListGetAt_natListInsertAt_inside state.openWires position
    [state.nextFresh, state.nextFresh + 1] 1 (Nat.lt_succ_self 1) cupInRange

/-! ## The same-component dichotomy -/

/-- ★ **A same-component pair of spliced-state tokens is both old-zone or both cup legs.**  A leg
node roots in the fresh cup component, an old-zone node in an old component, and the two are never
joined (`isSameComponent_stepCupArc_{freshOld,oldFresh}Probes`) — so a same-component arc cannot
mix a leg with an old-zone token. -/
theorem arcCupSameComponentDichotomy (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (cupInRange : position ≤ state.openWires.length)
    (tokenLeft tokenRight : ArcEndToken)
    (validLeft : isValidArcEndToken seedBoundary (stepCupArc state position) tokenLeft)
    (validRight : isValidArcEndToken seedBoundary (stepCupArc state position) tokenRight)
    (same : isSameComponent (stepCupArc state position).links
      (arcEndTokenNode (stepCupArc state position) tokenLeft)
      (arcEndTokenNode (stepCupArc state position) tokenRight) = true) :
    (arcEndTokenNode (stepCupArc state position) tokenLeft < state.nextFresh
        ∧ arcEndTokenNode (stepCupArc state position) tokenRight < state.nextFresh)
      ∨ ((tokenLeft = ArcEndToken.openSlot position
            ∨ tokenLeft = ArcEndToken.openSlot (position + 1))
        ∧ (tokenRight = ArcEndToken.openSlot position
            ∨ tokenRight = ArcEndToken.openSlot (position + 1))) := by
  have legNodeAtLeast : ∀ tok : ArcEndToken,
      (tok = ArcEndToken.openSlot position ∨ tok = ArcEndToken.openSlot (position + 1)) →
      state.nextFresh ≤ arcEndTokenNode (stepCupArc state position) tok := by
    intro tok tokLeg
    cases tokLeg with
    | inl isLeft =>
        rw [isLeft]
        exact Nat.le_of_eq (arcCupLeftLegNode state position cupInRange).symm
    | inr isRight =>
        rw [isRight, arcCupRightLegNode state position cupInRange]
        exact Nat.le_succ state.nextFresh
  rcases arcCupTokenNodeClass seedBoundary state position fresh seedBelowFresh cupInRange
      tokenLeft validLeft with leftOld | leftLeg
  · rcases arcCupTokenNodeClass seedBoundary state position fresh seedBelowFresh cupInRange
        tokenRight validRight with rightOld | rightLeg
    · exact Or.inl ⟨leftOld, rightOld⟩
    · have separated := isSameComponent_stepCupArc_oldFreshProbes state position fresh forest
        (arcEndTokenNode (stepCupArc state position) tokenLeft)
        (arcEndTokenNode (stepCupArc state position) tokenRight) leftOld
        (legNodeAtLeast tokenRight rightLeg)
      exact Bool.noConfusion (separated.symm.trans same)
  · rcases arcCupTokenNodeClass seedBoundary state position fresh seedBelowFresh cupInRange
        tokenRight validRight with rightOld | rightLeg
    · have separated := isSameComponent_stepCupArc_freshOldProbes state position fresh forest
        (arcEndTokenNode (stepCupArc state position) tokenLeft)
        (arcEndTokenNode (stepCupArc state position) tokenRight)
        (legNodeAtLeast tokenLeft leftLeg) rightOld
      exact Bool.noConfusion (separated.symm.trans same)
    · exact Or.inr ⟨leftLeg, rightLeg⟩

/-! ## The both-legs branch: an adjacent cup admits no strand between its endpoints -/

/-- ★ **Two cup-leg tokens leave no room for a third at a strictly-between position.**  The two
legs sit at adjacent cyclic positions (`arcCupLegsAdjacent`); a token strictly between a
lower-then-higher leg pair would have to lie strictly between adjacent naturals, impossible.  This
is the "both legs" branch of the crossing argument — the new cup can never be one of two
interleaving arcs. -/
theorem arcCupBothLegsNoMiddle (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (cupInRange : position ≤ state.openWires.length)
    (tokenLow tokenMid tokenHigh : ArcEndToken)
    (lowLeg : tokenLow = ArcEndToken.openSlot position
      ∨ tokenLow = ArcEndToken.openSlot (position + 1))
    (highLeg : tokenHigh = ArcEndToken.openSlot position
      ∨ tokenHigh = ArcEndToken.openSlot (position + 1))
    (posLowMid : arcEndTokenPosition seedBoundary (stepCupArc state position) tokenLow
      < arcEndTokenPosition seedBoundary (stepCupArc state position) tokenMid)
    (posMidHigh : arcEndTokenPosition seedBoundary (stepCupArc state position) tokenMid
      < arcEndTokenPosition seedBoundary (stepCupArc state position) tokenHigh) :
    False := by
  have adjacency := arcCupLegsAdjacent seedBoundary state position cupInRange
  rcases lowLeg with lowLeft | lowRight
  · rcases highLeg with highLeft | highRight
    · subst lowLeft highLeft
      exact Nat.lt_irrefl _ (Nat.lt_trans posLowMid posMidHigh)
    · subst lowLeft highRight
      have highBelowLow : arcEndTokenPosition seedBoundary (stepCupArc state position)
            (ArcEndToken.openSlot (position + 1))
          < arcEndTokenPosition seedBoundary (stepCupArc state position)
            (ArcEndToken.openSlot position) := by
        rw [← adjacency]; exact Nat.lt_succ_self _
      exact Nat.lt_irrefl _
        (Nat.lt_trans (Nat.lt_trans posLowMid posMidHigh) highBelowLow)
  · rcases highLeg with highLeft | highRight
    · subst lowRight highLeft
      rw [← adjacency] at posMidHigh
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le posLowMid (Nat.le_of_lt_succ posMidHigh))
    · subst lowRight highRight
      exact Nat.lt_irrefl _ (Nat.lt_trans posLowMid posMidHigh)

/-! ## The old-zone monotone position remap -/

/-- A spliced-state token whose read node stays below `nextFresh` is a syntactic old-zone token:
a bottom port always is, and an open slot cannot be a window slot (those read the fresh legs
`nextFresh`/`nextFresh+1`, which are not below `nextFresh`). -/
private theorem arcCupNodeBelowImpliesZone (state : ArcWireState)
    (position : Nat) (cupInRange : position ≤ state.openWires.length) (token : ArcEndToken)
    (nodeBelow : arcEndTokenNode (stepCupArc state position) token < state.nextFresh) :
    isCupOldZoneToken position token := by
  cases token with
  | bottomPort portValue => exact True.intro
  | openSlot slot =>
      rcases Nat.lt_or_ge slot position with below | atLeast
      · exact Or.inl below
      · rcases Nat.lt_or_ge slot (position + 2) with inWindow | past
        · rcases Nat.lt_or_ge slot (position + 1) with belowSucc | succLe
          · have slotEq : slot = position :=
              Nat.le_antisymm (Nat.le_of_lt_succ belowSucc) atLeast
            rw [slotEq, arcCupLeftLegNode state position cupInRange] at nodeBelow
            exact absurd nodeBelow (Nat.lt_irrefl state.nextFresh)
          · have slotEq : slot = position + 1 :=
              Nat.le_antisymm (Nat.le_of_lt_succ inWindow) succLe
            rw [slotEq, arcCupRightLegNode state position cupInRange] at nodeBelow
            exact (Nat.lt_irrefl (state.nextFresh + 1)
              (Nat.lt_trans nodeBelow (Nat.lt_succ_self state.nextFresh))).elim
        · exact Or.inr past

/-- ★ **The old-zone position remap is strictly monotone.**  For two old-zone tokens whose cyclic
positions strictly increase in the spliced state, the backmapped tokens' positions strictly
increase in the old state.  Bottom ports keep their sub-`seedBoundary` value; open slots reverse
past the seed block, and the splice backmap preserves that order (below-window slots keep their
index, past-window slots shift down by two — both order-preserving). -/
theorem arcCupOldZoneMonotone (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (cupInRange : position ≤ state.openWires.length)
    (tokenLow tokenHigh : ArcEndToken)
    (zoneLow : isCupOldZoneToken position tokenLow)
    (zoneHigh : isCupOldZoneToken position tokenHigh)
    (validLow : isValidArcEndToken seedBoundary (stepCupArc state position) tokenLow)
    (validHigh : isValidArcEndToken seedBoundary (stepCupArc state position) tokenHigh)
    (newPosLt : arcEndTokenPosition seedBoundary (stepCupArc state position) tokenLow
      < arcEndTokenPosition seedBoundary (stepCupArc state position) tokenHigh) :
    arcEndTokenPosition seedBoundary state (cupEndTokenBackmap position tokenLow)
      < arcEndTokenPosition seedBoundary state (cupEndTokenBackmap position tokenHigh) := by
  cases tokenLow with
  | bottomPort valueLow =>
      cases tokenHigh with
      | bottomPort valueHigh => exact newPosLt
      | openSlot slotHigh =>
          exact Nat.lt_of_lt_of_le validLow (Nat.le_add_right seedBoundary _)
  | openSlot slotLow =>
      cases tokenHigh with
      | bottomPort valueHigh =>
          exact absurd
            (Nat.lt_of_le_of_lt (Nat.le_add_right seedBoundary _)
              (Nat.lt_trans newPosLt validHigh))
            (Nat.lt_irrefl seedBoundary)
      | openSlot slotHigh =>
          have innerLt : (stepCupArc state position).openWires.length - 1 - slotLow
              < (stepCupArc state position).openWires.length - 1 - slotHigh :=
            Nat.lt_of_add_lt_add_left newPosLt
          have slotHighLtLow : slotHigh < slotLow := by
            rcases Nat.lt_or_ge slotHigh slotLow with below | atLeast
            · exact below
            · exact absurd (Nat.lt_of_lt_of_le innerLt
                (subMonotoneLe ((stepCupArc state position).openWires.length - 1)
                  slotLow slotHigh atLeast))
                (Nat.lt_irrefl _)
          have backLowValid : (if slotLow < position then slotLow else slotLow - 2)
              < state.openWires.length :=
            cupEndTokenBackmap_isValid seedBoundary state position (ArcEndToken.openSlot slotLow)
              zoneLow cupInRange validLow
          show seedBoundary + (state.openWires.length - 1
              - (if slotLow < position then slotLow else slotLow - 2))
            < seedBoundary + (state.openWires.length - 1
              - (if slotHigh < position then slotHigh else slotHigh - 2))
          exact Nat.add_lt_add_left
            (subStrictAntitone (state.openWires.length - 1)
              (if slotHigh < position then slotHigh else slotHigh - 2)
              (if slotLow < position then slotLow else slotLow - 2)
              (cupBackslotMonotone position slotHigh slotLow zoneHigh zoneLow slotHighLtLow)
              (ltImpliesLePred _ state.openWires.length backLowValid))
            seedBoundary

/-! ## The stepCupArc preservation of ArcNonCrossing -/

/-- ★ **A CUP step preserves the non-crossing (planarity) invariant.**  Given four valid tokens
of the spliced state at strictly increasing cyclic positions with the first paired to the third
and the second to the fourth, the same-component dichotomy classifies each arc as both cup legs
or both old-zone.  A legs arc admits no third token strictly between its adjacent endpoints
(`arcCupBothLegsNoMiddle`), so both arcs must be old-zone; then the splice backmap carries the
quadruple to a strictly-increasing old crossing (via the monotone remap and the cup's
component transparency), contradicting the old invariant. -/
theorem arcNonCrossing_stepCupArc (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (cupInRange : position ≤ state.openWires.length)
    (oldNonCrossing : ArcNonCrossing seedBoundary state) :
    ArcNonCrossing seedBoundary (stepCupArc state position) := by
  intro tokenA tokenB tokenC tokenD validA validB validC validD
    positionsAB positionsBC positionsCD sameAC sameBD
  rcases arcCupSameComponentDichotomy seedBoundary state position fresh forest seedBelowFresh
      cupInRange tokenA tokenC validA validC sameAC with ⟨nodeABelow, nodeCBelow⟩ | ⟨legA, legC⟩
  · rcases arcCupSameComponentDichotomy seedBoundary state position fresh forest seedBelowFresh
        cupInRange tokenB tokenD validB validD sameBD with ⟨nodeBBelow, nodeDBelow⟩ | ⟨legB, legD⟩
    · have zoneA : isCupOldZoneToken position tokenA :=
        arcCupNodeBelowImpliesZone state position cupInRange tokenA nodeABelow
      have zoneB : isCupOldZoneToken position tokenB :=
        arcCupNodeBelowImpliesZone state position cupInRange tokenB nodeBBelow
      have zoneC : isCupOldZoneToken position tokenC :=
        arcCupNodeBelowImpliesZone state position cupInRange tokenC nodeCBelow
      have zoneD : isCupOldZoneToken position tokenD :=
        arcCupNodeBelowImpliesZone state position cupInRange tokenD nodeDBelow
      have oldSameAC : isSameComponent state.links
          (arcEndTokenNode state (cupEndTokenBackmap position tokenA))
          (arcEndTokenNode state (cupEndTokenBackmap position tokenC)) = true := by
        rw [← cupEndTokenBackmap_node state position cupInRange tokenA zoneA,
          ← cupEndTokenBackmap_node state position cupInRange tokenC zoneC,
          ← isSameComponent_stepCupArc_oldProbes state position fresh forest
            (arcEndTokenNode (stepCupArc state position) tokenA)
            (arcEndTokenNode (stepCupArc state position) tokenC) nodeABelow nodeCBelow]
        exact sameAC
      have oldSameBD : isSameComponent state.links
          (arcEndTokenNode state (cupEndTokenBackmap position tokenB))
          (arcEndTokenNode state (cupEndTokenBackmap position tokenD)) = true := by
        rw [← cupEndTokenBackmap_node state position cupInRange tokenB zoneB,
          ← cupEndTokenBackmap_node state position cupInRange tokenD zoneD,
          ← isSameComponent_stepCupArc_oldProbes state position fresh forest
            (arcEndTokenNode (stepCupArc state position) tokenB)
            (arcEndTokenNode (stepCupArc state position) tokenD) nodeBBelow nodeDBelow]
        exact sameBD
      exact oldNonCrossing (cupEndTokenBackmap position tokenA)
        (cupEndTokenBackmap position tokenB) (cupEndTokenBackmap position tokenC)
        (cupEndTokenBackmap position tokenD)
        (cupEndTokenBackmap_isValid seedBoundary state position tokenA zoneA cupInRange validA)
        (cupEndTokenBackmap_isValid seedBoundary state position tokenB zoneB cupInRange validB)
        (cupEndTokenBackmap_isValid seedBoundary state position tokenC zoneC cupInRange validC)
        (cupEndTokenBackmap_isValid seedBoundary state position tokenD zoneD cupInRange validD)
        (arcCupOldZoneMonotone seedBoundary state position cupInRange tokenA tokenB zoneA zoneB
          validA validB positionsAB)
        (arcCupOldZoneMonotone seedBoundary state position cupInRange tokenB tokenC zoneB zoneC
          validB validC positionsBC)
        (arcCupOldZoneMonotone seedBoundary state position cupInRange tokenC tokenD zoneC zoneD
          validC validD positionsCD)
        oldSameAC oldSameBD
    · exact arcCupBothLegsNoMiddle seedBoundary state position cupInRange tokenB tokenC tokenD
        legB legD positionsBC positionsCD
  · exact arcCupBothLegsNoMiddle seedBoundary state position cupInRange tokenA tokenB tokenC
      legA legC positionsAB positionsBC

/-! ## Honesty marker -/

/-- **Honesty marker — a CUP step preserves the non-crossing invariant (cup rung D2a-iii,
COMPLETE).**  `arcCupTokenNodeClass`, `arcCupLeftLegNode`/`arcCupRightLegNode`, and
`arcCupSameComponentDichotomy` (the leg/old-zone classification), `arcCupBothLegsNoMiddle` (an
adjacent cup admits no strand between its legs), `arcCupOldZoneMonotone` (the old-zone position
remap is strictly monotone), and `arcNonCrossing_stepCupArc` (the full preservation:
`ArcNonCrossing seedBoundary state → ArcNonCrossing seedBoundary (stepCupArc state position)` for
an in-range cup step over a fresh forest).  What this marker does NOT claim: the DUAL stepCapArc
preservation, the whole-spine fold, and the extract translation to `IsNonCrossing bottomCount
(…).diagram.partner` (cup rung D2a-iv).  `= true`. -/
def fxMode_hasArcCupNonCrossingPreservation : Bool := true

end FX1Poly.Polygraph
