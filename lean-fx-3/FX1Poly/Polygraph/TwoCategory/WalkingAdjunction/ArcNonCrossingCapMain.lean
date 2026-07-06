import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingCapPreservation

/-! # ArcNonCrossingCapMain — a cap step preserves ArcNonCrossing (cap rung D2a-iv, main theorem)

The dual of the cup preservation, and genuinely harder: a cap FUSES two old components (rather than
adding a fresh isolated one), so the same-component relation is NOT transparent — the two window
ends `capLeft` (at cyclic position `Q+1`) and `capRight` (at `Q`, adjacent) get joined.  The proof
threads the boundary CENSUS alongside `ArcNonCrossing`, because the census is load-bearing: after
backmapping the four offending tokens to the old state, each of the two paired components' join
membership dispatches three ways, and the combos where two backmapped tokens reach the SAME window
end are census violations (that end's component would carry three boundary ends).  The five
surviving combos each exhibit a genuine old crossing quadruple — chosen from the six tokens
`{A',B',C',D', capLeft, capRight}` by a position split, using `arcCapBackmapPositionOffWindow` to
place the backmapped tokens strictly off the two-slot window gap.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **A CAP step preserves the non-crossing (planarity) invariant.**  Threading the boundary
census (which bounds every component at two ends), the wire-join dispatch on the two paired
components reduces to five surviving combos, each producing an old interleaved quadruple that the
old non-crossing invariant forbids — the cup's dual, with the window's two adjacent consumed ends
playing the role the cup's two fresh legs played. -/
theorem arcNonCrossing_stepCapArc (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (capInRange : position + 2 ≤ state.openWires.length)
    (oldCensus : ArcBoundaryCensus seedBoundary state)
    (oldNonCrossing : ArcNonCrossing seedBoundary state) :
    ArcNonCrossing seedBoundary (stepCapArc state position) := by
  intro tokenA tokenB tokenC tokenD validA validB validC validD
    positionsAB positionsBC positionsCD sameAC sameBD
  let bmA := capEndTokenBackmap position tokenA
  let bmB := capEndTokenBackmap position tokenB
  let bmC := capEndTokenBackmap position tokenC
  let bmD := capEndTokenBackmap position tokenD
  let capL := ArcEndToken.openSlot position
  let capR := ArcEndToken.openSlot (position + 1)
  -- backmap validity
  have validBmA : isValidArcEndToken seedBoundary state bmA :=
    capEndTokenBackmap_isValid seedBoundary state position capInRange tokenA validA
  have validBmB : isValidArcEndToken seedBoundary state bmB :=
    capEndTokenBackmap_isValid seedBoundary state position capInRange tokenB validB
  have validBmC : isValidArcEndToken seedBoundary state bmC :=
    capEndTokenBackmap_isValid seedBoundary state position capInRange tokenC validC
  have validBmD : isValidArcEndToken seedBoundary state bmD :=
    capEndTokenBackmap_isValid seedBoundary state position capInRange tokenD validD
  have capLValid : isValidArcEndToken seedBoundary state capL :=
    Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) capInRange
  have capRValid : isValidArcEndToken seedBoundary state capR :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) position) capInRange
  -- old positions strictly increasing
  have posAB : arcEndTokenPosition seedBoundary state bmA
      < arcEndTokenPosition seedBoundary state bmB :=
    arcCapOldPositionMonotone seedBoundary state position capInRange tokenA tokenB
      validA validB positionsAB
  have posBC : arcEndTokenPosition seedBoundary state bmB
      < arcEndTokenPosition seedBoundary state bmC :=
    arcCapOldPositionMonotone seedBoundary state position capInRange tokenB tokenC
      validB validC positionsBC
  have posCD : arcEndTokenPosition seedBoundary state bmC
      < arcEndTokenPosition seedBoundary state bmD :=
    arcCapOldPositionMonotone seedBoundary state position capInRange tokenC tokenD
      validC validD positionsCD
  -- the two consumed window slots at adjacent positions Q < Q+1
  have windowAdj : arcEndTokenPosition seedBoundary state capR + 1
      = arcEndTokenPosition seedBoundary state capL :=
    arcCapWindowAdjacent seedBoundary state position capInRange
  have capRLtL : arcEndTokenPosition seedBoundary state capR
      < arcEndTokenPosition seedBoundary state capL := by
    rw [← windowAdj]; exact Nat.lt_succ_self _
  -- backmap distinctness (injective) and misses of the window slots
  have neAB : bmA ≠ bmB := fun eq => by
    exact absurd (capEndTokenBackmap_injective position tokenA tokenB eq)
      (fun tokEq => Nat.lt_irrefl _ (tokEq ▸ positionsAB))
  have neAC : bmA ≠ bmC := fun eq =>
    absurd (capEndTokenBackmap_injective position tokenA tokenC eq)
      (fun tokEq => Nat.lt_irrefl _ (tokEq ▸ Nat.lt_trans positionsAB positionsBC))
  have neAD : bmA ≠ bmD := fun eq =>
    absurd (capEndTokenBackmap_injective position tokenA tokenD eq)
      (fun tokEq => Nat.lt_irrefl _ (tokEq ▸ Nat.lt_trans positionsAB (Nat.lt_trans positionsBC positionsCD)))
  have neBC : bmB ≠ bmC := fun eq =>
    absurd (capEndTokenBackmap_injective position tokenB tokenC eq)
      (fun tokEq => Nat.lt_irrefl _ (tokEq ▸ positionsBC))
  have neBD : bmB ≠ bmD := fun eq =>
    absurd (capEndTokenBackmap_injective position tokenB tokenD eq)
      (fun tokEq => Nat.lt_irrefl _ (tokEq ▸ Nat.lt_trans positionsBC positionsCD))
  have neCD : bmC ≠ bmD := fun eq =>
    absurd (capEndTokenBackmap_injective position tokenC tokenD eq)
      (fun tokEq => Nat.lt_irrefl _ (tokEq ▸ positionsCD))
  have capLNeA : capL ≠ bmA := Ne.symm (capEndTokenBackmap_missesLeftWindow position tokenA)
  have capLNeB : capL ≠ bmB := Ne.symm (capEndTokenBackmap_missesLeftWindow position tokenB)
  have capLNeC : capL ≠ bmC := Ne.symm (capEndTokenBackmap_missesLeftWindow position tokenC)
  have capLNeD : capL ≠ bmD := Ne.symm (capEndTokenBackmap_missesLeftWindow position tokenD)
  -- node-below-fresh for the backmapped reads
  have nodeBmBelow : ∀ tok : ArcEndToken,
      isValidArcEndToken seedBoundary (stepCapArc state position) tok →
      arcEndTokenNode state (capEndTokenBackmap position tok) < state.nextFresh := by
    intro tok tokValid
    rw [← capEndTokenBackmap_node state position capInRange tok]
    exact arcCapNodeBelow seedBoundary state position fresh seedBelowFresh capInRange tok tokValid
  -- the join-relative membership at the two paired components
  have joinedAC : isSameComponent
      (unionFindJoin state.links (natListGetAt state.openWires position)
        (natListGetAt state.openWires (position + 1)))
      (arcEndTokenNode state bmA) (arcEndTokenNode state bmC) = true := by
    rw [← isSameComponent_stepCapArc_oldProbes state position fresh forest
        (arcEndTokenNode state bmA) (arcEndTokenNode state bmC)
        (nodeBmBelow tokenA validA) (nodeBmBelow tokenC validC),
      ← capEndTokenBackmap_node state position capInRange tokenA,
      ← capEndTokenBackmap_node state position capInRange tokenC]
    exact sameAC
  have joinedBD : isSameComponent
      (unionFindJoin state.links (natListGetAt state.openWires position)
        (natListGetAt state.openWires (position + 1)))
      (arcEndTokenNode state bmB) (arcEndTokenNode state bmD) = true := by
    rw [← isSameComponent_stepCapArc_oldProbes state position fresh forest
        (arcEndTokenNode state bmB) (arcEndTokenNode state bmD)
        (nodeBmBelow tokenB validB) (nodeBmBelow tokenD validD),
      ← capEndTokenBackmap_node state position capInRange tokenB,
      ← capEndTokenBackmap_node state position capInRange tokenD]
    exact sameBD
  have dispatchAC := sameComponent_unionFindJoin_dispatch state.links forest
    (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1))
    (arcEndTokenNode state bmA) (arcEndTokenNode state bmC) joinedAC
  have dispatchBD := sameComponent_unionFindJoin_dispatch state.links forest
    (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1))
    (arcEndTokenNode state bmB) (arcEndTokenNode state bmD) joinedBD
  rcases dispatchAC with acFree | acLeft | acRight
  · -- A'~C' free
    rcases dispatchBD with bdFree | bdLeft | bdRight
    · -- (1,1'): direct old crossing on A',B',C',D'
      exact oldNonCrossing bmA bmB bmC bmD validBmA validBmB validBmC validBmD
        posAB posBC posCD acFree bdFree
    · -- (1,2'): B'~capLeft, D'~capRight
      obtain ⟨leftReachesB, rightReachesD⟩ := bdLeft
      rcases Nat.lt_or_ge (arcEndTokenPosition seedBoundary state bmC)
          (arcEndTokenPosition seedBoundary state capL) with cLtLeft | cGeLeft
      · -- (a) posC' < pos capLeft: quad (A',B',C',capLeft)
        exact oldNonCrossing bmA bmB bmC capL validBmA validBmB validBmC capLValid
          posAB posBC cLtLeft acFree (isSameComponent_flip state.links _ _ leftReachesB)
      · rcases Nat.lt_or_ge (arcEndTokenPosition seedBoundary state capL)
            (arcEndTokenPosition seedBoundary state bmA) with leftLtA | aLeLeft
        · -- (b) pos capLeft < posA': quad (capLeft,A',B',C')
          exact oldNonCrossing capL bmA bmB bmC capLValid validBmA validBmB validBmC
            leftLtA posAB posBC leftReachesB acFree
        · -- (c) INSIDE: posA' < pos capRight; quad (A',capRight,C',D')
          have aLtRight : arcEndTokenPosition seedBoundary state bmA
              < arcEndTokenPosition seedBoundary state capR := by
            rcases arcCapBackmapPositionOffWindow seedBoundary state position capInRange
                tokenA validA with below | above
            · exact below
            · exact absurd (Nat.lt_of_le_of_lt aLeLeft above) (Nat.lt_irrefl _)
          have rightLtC : arcEndTokenPosition seedBoundary state capR
              < arcEndTokenPosition seedBoundary state bmC :=
            Nat.lt_of_lt_of_le capRLtL cGeLeft
          exact oldNonCrossing bmA capR bmC bmD validBmA capRValid validBmC validBmD
            aLtRight rightLtC posCD acFree rightReachesD
    · -- (1,3'): D'~capLeft, B'~capRight
      obtain ⟨leftReachesD, rightReachesB⟩ := bdRight
      rcases Nat.lt_or_ge (arcEndTokenPosition seedBoundary state bmC)
          (arcEndTokenPosition seedBoundary state capR) with cLtRight | cGeRight
      · -- (a) posC' < pos capRight: quad (A',B',C',capRight)
        exact oldNonCrossing bmA bmB bmC capR validBmA validBmB validBmC capRValid
          posAB posBC cLtRight acFree rightReachesB
      · rcases Nat.lt_or_ge (arcEndTokenPosition seedBoundary state capL)
            (arcEndTokenPosition seedBoundary state bmA) with leftLtA | aLeLeft
        · -- (b) pos capLeft < posA': quad (capRight,A',B',C')
          have rightLtA : arcEndTokenPosition seedBoundary state capR
              < arcEndTokenPosition seedBoundary state bmA :=
            Nat.lt_trans capRLtL leftLtA
          exact oldNonCrossing capR bmA bmB bmC capRValid validBmA validBmB validBmC
            rightLtA posAB posBC (isSameComponent_flip state.links _ _ rightReachesB) acFree
        · -- (c) INSIDE: posA' < pos capLeft; quad (A',capLeft,C',D')
          have aLtLeft : arcEndTokenPosition seedBoundary state bmA
              < arcEndTokenPosition seedBoundary state capL := by
            rcases arcCapBackmapPositionOffWindow seedBoundary state position capInRange
                tokenA validA with below | above
            · exact Nat.lt_of_lt_of_le below (Nat.le_of_lt capRLtL)
            · exact absurd (Nat.lt_of_le_of_lt aLeLeft above) (Nat.lt_irrefl _)
          have leftLtC : arcEndTokenPosition seedBoundary state capL
              < arcEndTokenPosition seedBoundary state bmC := by
            rcases arcCapBackmapPositionOffWindow seedBoundary state position capInRange
                tokenC validC with below | above
            · exact absurd (Nat.lt_of_lt_of_le below cGeRight) (Nat.lt_irrefl _)
            · exact above
          exact oldNonCrossing bmA capL bmC bmD validBmA capLValid validBmC validBmD
            aLtLeft leftLtC posCD acFree leftReachesD
  · -- A'~capLeft, C'~capRight
    obtain ⟨leftReachesA, rightReachesC⟩ := acLeft
    rcases dispatchBD with bdFree | bdLeft | bdRight
    · -- (2,1'): B'~D'
      rcases Nat.lt_or_ge (arcEndTokenPosition seedBoundary state bmD)
          (arcEndTokenPosition seedBoundary state capR) with dLtRight | dGeRight
      · -- (a) posD' < pos capRight: quad (B',C',D',capRight)
        exact oldNonCrossing bmB bmC bmD capR validBmB validBmC validBmD capRValid
          posBC posCD dLtRight bdFree (isSameComponent_flip state.links _ _ rightReachesC)
      · rcases Nat.lt_or_ge (arcEndTokenPosition seedBoundary state capL)
            (arcEndTokenPosition seedBoundary state bmB) with leftLtB | bLeLeft
        · -- (b) pos capLeft < posB': quad (capRight,B',C',D')
          have rightLtB : arcEndTokenPosition seedBoundary state capR
              < arcEndTokenPosition seedBoundary state bmB :=
            Nat.lt_trans capRLtL leftLtB
          exact oldNonCrossing capR bmB bmC bmD capRValid validBmB validBmC validBmD
            rightLtB posBC posCD rightReachesC bdFree
        · -- (c) INSIDE: posB' < pos capLeft; quad (A',B',capLeft,D')
          have bLtLeft : arcEndTokenPosition seedBoundary state bmB
              < arcEndTokenPosition seedBoundary state capL := by
            rcases arcCapBackmapPositionOffWindow seedBoundary state position capInRange
                tokenB validB with below | above
            · exact Nat.lt_of_lt_of_le below (Nat.le_of_lt capRLtL)
            · exact absurd (Nat.lt_of_le_of_lt bLeLeft above) (Nat.lt_irrefl _)
          have leftLtD : arcEndTokenPosition seedBoundary state capL
              < arcEndTokenPosition seedBoundary state bmD := by
            rcases arcCapBackmapPositionOffWindow seedBoundary state position capInRange
                tokenD validD with below | above
            · exact absurd (Nat.lt_of_lt_of_le below dGeRight) (Nat.lt_irrefl _)
            · exact above
          exact oldNonCrossing bmA bmB capL bmD validBmA validBmB capLValid validBmD
            posAB bLtLeft leftLtD (isSameComponent_flip state.links _ _ leftReachesA) bdFree
    · -- (2,2'): A'~capLeft and B'~capLeft — census violation
      obtain ⟨leftReachesB, _⟩ := bdLeft
      exact oldCensus capL bmA bmB capLValid validBmA validBmB capLNeA capLNeB neAB
        leftReachesA leftReachesB
    · -- (2,3'): A'~capLeft and D'~capLeft — census violation
      obtain ⟨leftReachesD, _⟩ := bdRight
      exact oldCensus capL bmA bmD capLValid validBmA validBmD capLNeA capLNeD neAD
        leftReachesA leftReachesD
  · -- C'~capLeft, A'~capRight
    obtain ⟨leftReachesC, rightReachesA⟩ := acRight
    rcases dispatchBD with bdFree | bdLeft | bdRight
    · -- (3,1'): B'~D'
      rcases Nat.lt_or_ge (arcEndTokenPosition seedBoundary state bmD)
          (arcEndTokenPosition seedBoundary state capL) with dLtLeft | dGeLeft
      · -- (a) posD' < pos capLeft: quad (B',C',D',capLeft)
        exact oldNonCrossing bmB bmC bmD capL validBmB validBmC validBmD capLValid
          posBC posCD dLtLeft bdFree (isSameComponent_flip state.links _ _ leftReachesC)
      · rcases Nat.lt_or_ge (arcEndTokenPosition seedBoundary state capL)
            (arcEndTokenPosition seedBoundary state bmB) with leftLtB | bLeLeft
        · -- (b) pos capLeft < posB': quad (capLeft,B',C',D')
          exact oldNonCrossing capL bmB bmC bmD capLValid validBmB validBmC validBmD
            leftLtB posBC posCD leftReachesC bdFree
        · -- (c) INSIDE: posB' < pos capRight; quad (A',B',capRight,D')
          have bLtRight : arcEndTokenPosition seedBoundary state bmB
              < arcEndTokenPosition seedBoundary state capR := by
            rcases arcCapBackmapPositionOffWindow seedBoundary state position capInRange
                tokenB validB with below | above
            · exact below
            · exact absurd (Nat.lt_of_le_of_lt bLeLeft above) (Nat.lt_irrefl _)
          have rightLtD : arcEndTokenPosition seedBoundary state capR
              < arcEndTokenPosition seedBoundary state bmD :=
            Nat.lt_of_lt_of_le capRLtL dGeLeft
          exact oldNonCrossing bmA bmB capR bmD validBmA validBmB capRValid validBmD
            posAB bLtRight rightLtD rightReachesA bdFree
    · -- (3,2'): C'~capLeft and B'~capLeft — census violation
      obtain ⟨leftReachesB, _⟩ := bdLeft
      exact oldCensus capL bmB bmC capLValid validBmB validBmC capLNeB capLNeC neBC
        leftReachesB leftReachesC
    · -- (3,3'): C'~capLeft and D'~capLeft — census violation
      obtain ⟨leftReachesD, _⟩ := bdRight
      exact oldCensus capL bmC bmD capLValid validBmC validBmD capLNeC capLNeD neCD
        leftReachesC leftReachesD

/-- **Honesty marker — a CAP step preserves the non-crossing invariant (cap rung D2a-iv, main
theorem).**  `arcNonCrossing_stepCapArc`: threading the boundary census, a fresh-forest in-range
cap step carries `ArcNonCrossing` forward.  What this marker does NOT claim: the whole-spine fold
of the census-and-non-crossing pair and the extract translation to `IsNonCrossing bottomCount
(…).diagram.partner` (cap rung D2a-iv fold + extract).  `= true`. -/
def fxMode_hasArcCapNonCrossingPreservation : Bool := true

end FX1Poly.Polygraph
