import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupRootAtlas

/-! # ArcCupCupSwapSimulation — the CUP x CUP two-step core simulation (ARC-2b brick iii-1d-alpha2)

The two run orders of a CUP x CUP disjoint-window swap: order S fires the low cup at
`positionLow` then the high cup at `gap + 2 + positionLow` (the low cup produced two wires, so
the high window slid up by two); order T fires the high cup first at `gap + positionLow` (the
low cup consumed nothing, so the high window in the PRE state sits at the bare gap) then the
low cup at `positionLow`.  The renaming reconciling the swapped fresh allocations is the
iii-1b fresh-block transposition at widths `3, 3` (each cup allocates two legs and one event
node).

Because `stepCupArc`'s joins and event pushes read only `nextFresh` — never the position — the
two orders produce IDENTICAL link lists and event lists (the alpha1 key fact), so:

  * `nfEq` / `loopsEq` are `rfl`;
  * `rootComm` / `cupCorr` / `capCorr` reduce to the alpha1 root atlas plus the iii-1b block
    value laws — proved here position-GENERICALLY (four arbitrary positions), since the links
    never see them;
  * the whole positional content concentrates in `openMap`, discharged by the iii-1a
    insert-above-insert commutation kit.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- `List.map` on a two-element literal, exposed as a rewrite (definitional). -/
private theorem mapPairValues (rename : Nat → Nat) (firstValue secondValue : Nat) :
    List.map rename [firstValue, secondValue] = [rename firstValue, rename secondValue] := rfl

/-- ★ **The transposition root-commutes between any two double-cup states.**  The links of a
double-cup state do not depend on the splice positions, so the statement holds for FOUR
arbitrary positions: below `nextFresh` everything is fixed and old roots are local; on the six
fresh identifiers the two cups' components are exact `sigma`-images of each other (first triple
roots at `nextFresh + 1`, second at `nextFresh + 4`, and the transposition swaps the triples);
at or above both triples everything is parentless and fixed. -/
theorem cupPair_rootComm_transposition (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (positionSourceFirst positionSourceSecond positionTargetFirst positionTargetSecond : Nat)
    (node : Nat) :
    unionFindRootOf
        (stepCupArc (stepCupArc state positionTargetFirst) positionTargetSecond).links
        (arcFreshBlockTransposition state.nextFresh 3 3 node)
      = arcFreshBlockTransposition state.nextFresh 3 3
          (unionFindRootOf
            (stepCupArc (stepCupArc state positionSourceFirst) positionSourceSecond).links
            node) := by
  cases Nat.lt_or_ge node state.nextFresh with
  | inl nodeBelow =>
      have rootBelow : unionFindRootOf state.links node < state.nextFresh :=
        unionFindRootOf_lt_of_fresh state.links state.nextFresh
          (fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2) node nodeBelow
      rw [arcFreshBlockTransposition_ofBelow state.nextFresh 3 3 node nodeBelow,
        cupPair_root_old state positionTargetFirst positionTargetSecond fresh forest node
          rootBelow,
        cupPair_root_old state positionSourceFirst positionSourceSecond fresh forest node
          rootBelow,
        arcFreshBlockTransposition_ofBelow state.nextFresh 3 3
          (unionFindRootOf state.links node) rootBelow]
  | inr nodeAtOrAbove =>
      obtain ⟨offset, offsetEquation⟩ := Nat.le.dest nodeAtOrAbove
      subst offsetEquation
      have sigmaFirstZero : arcFreshBlockTransposition state.nextFresh 3 3 state.nextFresh
          = state.nextFresh + 3 :=
        arcFreshBlockTransposition_onFirstBlock state.nextFresh 3 3 0 (by decide)
      have sigmaFirstOne :
          arcFreshBlockTransposition state.nextFresh 3 3 (state.nextFresh + 1)
            = state.nextFresh + 4 :=
        arcFreshBlockTransposition_onFirstBlock state.nextFresh 3 3 1 (by decide)
      have sigmaFirstTwo :
          arcFreshBlockTransposition state.nextFresh 3 3 (state.nextFresh + 2)
            = state.nextFresh + 5 :=
        arcFreshBlockTransposition_onFirstBlock state.nextFresh 3 3 2 (by decide)
      have sigmaSecondZero :
          arcFreshBlockTransposition state.nextFresh 3 3 (state.nextFresh + 3)
            = state.nextFresh :=
        arcFreshBlockTransposition_onSecondBlock state.nextFresh 3 3 0 (by decide)
      have sigmaSecondOne :
          arcFreshBlockTransposition state.nextFresh 3 3 (state.nextFresh + 4)
            = state.nextFresh + 1 :=
        arcFreshBlockTransposition_onSecondBlock state.nextFresh 3 3 1 (by decide)
      have sigmaSecondTwo :
          arcFreshBlockTransposition state.nextFresh 3 3 (state.nextFresh + 5)
            = state.nextFresh + 2 :=
        arcFreshBlockTransposition_onSecondBlock state.nextFresh 3 3 2 (by decide)
      have rootTargetFirstZero :
          unionFindRootOf
              (stepCupArc (stepCupArc state positionTargetFirst) positionTargetSecond).links
              state.nextFresh
            = state.nextFresh + 1 :=
        cupPair_root_firstBlock state positionTargetFirst positionTargetSecond fresh forest
          0 (by decide)
      have rootTargetFirstOne :
          unionFindRootOf
              (stepCupArc (stepCupArc state positionTargetFirst) positionTargetSecond).links
              (state.nextFresh + 1)
            = state.nextFresh + 1 :=
        cupPair_root_firstBlock state positionTargetFirst positionTargetSecond fresh forest
          1 (by decide)
      have rootTargetFirstTwo :
          unionFindRootOf
              (stepCupArc (stepCupArc state positionTargetFirst) positionTargetSecond).links
              (state.nextFresh + 2)
            = state.nextFresh + 1 :=
        cupPair_root_firstBlock state positionTargetFirst positionTargetSecond fresh forest
          2 (by decide)
      have rootTargetSecondZero :
          unionFindRootOf
              (stepCupArc (stepCupArc state positionTargetFirst) positionTargetSecond).links
              (state.nextFresh + 3)
            = state.nextFresh + 4 :=
        cupPair_root_secondBlock state positionTargetFirst positionTargetSecond fresh forest
          0 (by decide)
      have rootTargetSecondOne :
          unionFindRootOf
              (stepCupArc (stepCupArc state positionTargetFirst) positionTargetSecond).links
              (state.nextFresh + 4)
            = state.nextFresh + 4 :=
        cupPair_root_secondBlock state positionTargetFirst positionTargetSecond fresh forest
          1 (by decide)
      have rootTargetSecondTwo :
          unionFindRootOf
              (stepCupArc (stepCupArc state positionTargetFirst) positionTargetSecond).links
              (state.nextFresh + 5)
            = state.nextFresh + 4 :=
        cupPair_root_secondBlock state positionTargetFirst positionTargetSecond fresh forest
          2 (by decide)
      have rootSourceFirstZero :
          unionFindRootOf
              (stepCupArc (stepCupArc state positionSourceFirst) positionSourceSecond).links
              state.nextFresh
            = state.nextFresh + 1 :=
        cupPair_root_firstBlock state positionSourceFirst positionSourceSecond fresh forest
          0 (by decide)
      have rootSourceFirstOne :
          unionFindRootOf
              (stepCupArc (stepCupArc state positionSourceFirst) positionSourceSecond).links
              (state.nextFresh + 1)
            = state.nextFresh + 1 :=
        cupPair_root_firstBlock state positionSourceFirst positionSourceSecond fresh forest
          1 (by decide)
      have rootSourceFirstTwo :
          unionFindRootOf
              (stepCupArc (stepCupArc state positionSourceFirst) positionSourceSecond).links
              (state.nextFresh + 2)
            = state.nextFresh + 1 :=
        cupPair_root_firstBlock state positionSourceFirst positionSourceSecond fresh forest
          2 (by decide)
      have rootSourceSecondZero :
          unionFindRootOf
              (stepCupArc (stepCupArc state positionSourceFirst) positionSourceSecond).links
              (state.nextFresh + 3)
            = state.nextFresh + 4 :=
        cupPair_root_secondBlock state positionSourceFirst positionSourceSecond fresh forest
          0 (by decide)
      have rootSourceSecondOne :
          unionFindRootOf
              (stepCupArc (stepCupArc state positionSourceFirst) positionSourceSecond).links
              (state.nextFresh + 4)
            = state.nextFresh + 4 :=
        cupPair_root_secondBlock state positionSourceFirst positionSourceSecond fresh forest
          1 (by decide)
      have rootSourceSecondTwo :
          unionFindRootOf
              (stepCupArc (stepCupArc state positionSourceFirst) positionSourceSecond).links
              (state.nextFresh + 5)
            = state.nextFresh + 4 :=
        cupPair_root_secondBlock state positionSourceFirst positionSourceSecond fresh forest
          2 (by decide)
      match offset with
      | 0 =>
          rw [Nat.add_zero, sigmaFirstZero, rootTargetSecondZero, rootSourceFirstZero,
            sigmaFirstOne]
      | 1 => rw [sigmaFirstOne, rootTargetSecondOne, rootSourceFirstOne, sigmaFirstOne]
      | 2 => rw [sigmaFirstTwo, rootTargetSecondTwo, rootSourceFirstTwo, sigmaFirstOne]
      | 3 => rw [sigmaSecondZero, rootTargetFirstZero, rootSourceSecondZero, sigmaSecondOne]
      | 4 => rw [sigmaSecondOne, rootTargetFirstOne, rootSourceSecondOne, sigmaSecondOne]
      | 5 => rw [sigmaSecondTwo, rootTargetFirstTwo, rootSourceSecondTwo, sigmaSecondOne]
      | offsetRest + 6 =>
          have farAbove : state.nextFresh + 6 ≤ state.nextFresh + (offsetRest + 6) :=
            Nat.add_le_add_left (Nat.le_add_left 6 offsetRest) state.nextFresh
          have sigmaFixed : arcFreshBlockTransposition state.nextFresh 3 3
              (state.nextFresh + (offsetRest + 6)) = state.nextFresh + (offsetRest + 6) :=
            arcFreshBlockTransposition_ofAtOrAbove state.nextFresh 3 3
              (state.nextFresh + (offsetRest + 6)) farAbove
          rw [sigmaFixed,
            cupPair_root_aboveBlocks state positionTargetFirst positionTargetSecond fresh
              (state.nextFresh + (offsetRest + 6)) farAbove,
            cupPair_root_aboveBlocks state positionSourceFirst positionSourceSecond fresh
              (state.nextFresh + (offsetRest + 6)) farAbove,
            sigmaFixed]

/-- ★ **The per-root cup-event counts correspond across the transposition.**  Both orders push
the SAME two cup events (`nextFresh + 2` from the first-fired cup, `nextFresh + 5` from the
second), rooting at `nextFresh + 1` and `nextFresh + 4` respectively.  The transposition swaps
those two roots, so on the fresh range the two head guards SWAP while their SUM is preserved;
old counts collapse to the original links on both sides; fresh tails vanish. -/
theorem cupPair_cupCorr_transposition (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (positionSourceFirst positionSourceSecond positionTargetFirst positionTargetSecond : Nat)
    (countRoot : Nat) :
    countEventsInRoot
        (stepCupArc (stepCupArc state positionTargetFirst) positionTargetSecond).links
        (arcFreshBlockTransposition state.nextFresh 3 3 countRoot)
        (stepCupArc (stepCupArc state positionTargetFirst) positionTargetSecond).cupEventNodes
      = countEventsInRoot
          (stepCupArc (stepCupArc state positionSourceFirst) positionSourceSecond).links
          countRoot
          (stepCupArc (stepCupArc state positionSourceFirst) positionSourceSecond).cupEventNodes
    := by
  have linkParentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2
  have rootTargetHeadHigh :
      unionFindRootOf
          (stepCupArc (stepCupArc state positionTargetFirst) positionTargetSecond).links
          (state.nextFresh + 5)
        = state.nextFresh + 4 :=
    cupPair_root_secondBlock state positionTargetFirst positionTargetSecond fresh forest
      2 (by decide)
  have rootTargetHeadLow :
      unionFindRootOf
          (stepCupArc (stepCupArc state positionTargetFirst) positionTargetSecond).links
          (state.nextFresh + 2)
        = state.nextFresh + 1 :=
    cupPair_root_firstBlock state positionTargetFirst positionTargetSecond fresh forest
      2 (by decide)
  have rootSourceHeadHigh :
      unionFindRootOf
          (stepCupArc (stepCupArc state positionSourceFirst) positionSourceSecond).links
          (state.nextFresh + 5)
        = state.nextFresh + 4 :=
    cupPair_root_secondBlock state positionSourceFirst positionSourceSecond fresh forest
      2 (by decide)
  have rootSourceHeadLow :
      unionFindRootOf
          (stepCupArc (stepCupArc state positionSourceFirst) positionSourceSecond).links
          (state.nextFresh + 2)
        = state.nextFresh + 1 :=
    cupPair_root_firstBlock state positionSourceFirst positionSourceSecond fresh forest
      2 (by decide)
  show (if unionFindRootOf
          (stepCupArc (stepCupArc state positionTargetFirst) positionTargetSecond).links
          (state.nextFresh + 5)
        == arcFreshBlockTransposition state.nextFresh 3 3 countRoot then (1 : Nat) else 0)
      + ((if unionFindRootOf
            (stepCupArc (stepCupArc state positionTargetFirst) positionTargetSecond).links
            (state.nextFresh + 2)
          == arcFreshBlockTransposition state.nextFresh 3 3 countRoot then (1 : Nat) else 0)
        + countEventsInRoot
            (stepCupArc (stepCupArc state positionTargetFirst) positionTargetSecond).links
            (arcFreshBlockTransposition state.nextFresh 3 3 countRoot) state.cupEventNodes)
    = (if unionFindRootOf
          (stepCupArc (stepCupArc state positionSourceFirst) positionSourceSecond).links
          (state.nextFresh + 5)
        == countRoot then (1 : Nat) else 0)
      + ((if unionFindRootOf
            (stepCupArc (stepCupArc state positionSourceFirst) positionSourceSecond).links
            (state.nextFresh + 2)
          == countRoot then (1 : Nat) else 0)
        + countEventsInRoot
            (stepCupArc (stepCupArc state positionSourceFirst) positionSourceSecond).links
            countRoot state.cupEventNodes)
  rw [rootTargetHeadHigh, rootTargetHeadLow, rootSourceHeadHigh, rootSourceHeadLow]
  cases Nat.lt_or_ge countRoot state.nextFresh with
  | inl rootBelow =>
      rw [arcFreshBlockTransposition_ofBelow state.nextFresh 3 3 countRoot rootBelow,
        cupPair_countOldEvents_congr state positionTargetFirst positionTargetSecond fresh forest
          countRoot state.cupEventNodes fresh.2.2.1,
        cupPair_countOldEvents_congr state positionSourceFirst positionSourceSecond fresh forest
          countRoot state.cupEventNodes fresh.2.2.1]
  | inr rootAtLeastBase =>
      have baseBelowOne : state.nextFresh < state.nextFresh + 1 :=
        Nat.lt_add_of_pos_right (by decide)
      have baseBelowFour : state.nextFresh < state.nextFresh + 4 :=
        Nat.lt_add_of_pos_right (by decide)
      have oneBelowTwo : state.nextFresh + 1 < state.nextFresh + 2 :=
        Nat.add_lt_add_left (by decide) state.nextFresh
      have oneBelowThree : state.nextFresh + 1 < state.nextFresh + 3 :=
        Nat.add_lt_add_left (by decide) state.nextFresh
      have oneBelowFour : state.nextFresh + 1 < state.nextFresh + 4 :=
        Nat.add_lt_add_left (by decide) state.nextFresh
      have oneBelowFive : state.nextFresh + 1 < state.nextFresh + 5 :=
        Nat.add_lt_add_left (by decide) state.nextFresh
      have twoBelowFour : state.nextFresh + 2 < state.nextFresh + 4 :=
        Nat.add_lt_add_left (by decide) state.nextFresh
      have threeBelowFour : state.nextFresh + 3 < state.nextFresh + 4 :=
        Nat.add_lt_add_left (by decide) state.nextFresh
      have fourBelowFive : state.nextFresh + 4 < state.nextFresh + 5 :=
        Nat.add_lt_add_left (by decide) state.nextFresh
      have guardFourThree : ¬ (state.nextFresh + 4 == state.nextFresh + 3) = true :=
        fun isTrue => Bool.noConfusion (beq_false_of_lt threeBelowFour ▸ isTrue)
      have guardOneThree : ¬ (state.nextFresh + 1 == state.nextFresh + 3) = true :=
        fun isTrue => Bool.noConfusion (beq_false_of_lt_left oneBelowThree ▸ isTrue)
      have guardFourBase : ¬ (state.nextFresh + 4 == state.nextFresh) = true :=
        fun isTrue => Bool.noConfusion (beq_false_of_lt baseBelowFour ▸ isTrue)
      have guardOneBase : ¬ (state.nextFresh + 1 == state.nextFresh) = true :=
        fun isTrue => Bool.noConfusion (beq_false_of_lt baseBelowOne ▸ isTrue)
      have guardOneFour : ¬ (state.nextFresh + 1 == state.nextFresh + 4) = true :=
        fun isTrue => Bool.noConfusion (beq_false_of_lt_left oneBelowFour ▸ isTrue)
      have guardFourOne : ¬ (state.nextFresh + 4 == state.nextFresh + 1) = true :=
        fun isTrue => Bool.noConfusion (beq_false_of_lt oneBelowFour ▸ isTrue)
      have guardFourFive : ¬ (state.nextFresh + 4 == state.nextFresh + 5) = true :=
        fun isTrue => Bool.noConfusion (beq_false_of_lt_left fourBelowFive ▸ isTrue)
      have guardOneFive : ¬ (state.nextFresh + 1 == state.nextFresh + 5) = true :=
        fun isTrue => Bool.noConfusion (beq_false_of_lt_left oneBelowFive ▸ isTrue)
      have guardFourTwo : ¬ (state.nextFresh + 4 == state.nextFresh + 2) = true :=
        fun isTrue => Bool.noConfusion (beq_false_of_lt twoBelowFour ▸ isTrue)
      have guardOneTwo : ¬ (state.nextFresh + 1 == state.nextFresh + 2) = true :=
        fun isTrue => Bool.noConfusion (beq_false_of_lt_left oneBelowTwo ▸ isTrue)
      have trueFourFour : (state.nextFresh + 4 == state.nextFresh + 4) = true :=
        decide_eq_true rfl
      have trueOneOne : (state.nextFresh + 1 == state.nextFresh + 1) = true :=
        decide_eq_true rfl
      have sigmaFirstZero : arcFreshBlockTransposition state.nextFresh 3 3 state.nextFresh
          = state.nextFresh + 3 :=
        arcFreshBlockTransposition_onFirstBlock state.nextFresh 3 3 0 (by decide)
      have sigmaFirstOne :
          arcFreshBlockTransposition state.nextFresh 3 3 (state.nextFresh + 1)
            = state.nextFresh + 4 :=
        arcFreshBlockTransposition_onFirstBlock state.nextFresh 3 3 1 (by decide)
      have sigmaFirstTwo :
          arcFreshBlockTransposition state.nextFresh 3 3 (state.nextFresh + 2)
            = state.nextFresh + 5 :=
        arcFreshBlockTransposition_onFirstBlock state.nextFresh 3 3 2 (by decide)
      have sigmaSecondZero :
          arcFreshBlockTransposition state.nextFresh 3 3 (state.nextFresh + 3)
            = state.nextFresh :=
        arcFreshBlockTransposition_onSecondBlock state.nextFresh 3 3 0 (by decide)
      have sigmaSecondOne :
          arcFreshBlockTransposition state.nextFresh 3 3 (state.nextFresh + 4)
            = state.nextFresh + 1 :=
        arcFreshBlockTransposition_onSecondBlock state.nextFresh 3 3 1 (by decide)
      have sigmaSecondTwo :
          arcFreshBlockTransposition state.nextFresh 3 3 (state.nextFresh + 5)
            = state.nextFresh + 2 :=
        arcFreshBlockTransposition_onSecondBlock state.nextFresh 3 3 2 (by decide)
      have countLinksZeroAt : ∀ rootHere, state.nextFresh ≤ rootHere →
          countEventsInRoot state.links rootHere state.cupEventNodes = 0 :=
        fun rootHere isAtOrAbove =>
          countEventsInRoot_eq_zero_of_freshRoot state.links state.nextFresh linkParentsBelow
            rootHere isAtOrAbove state.cupEventNodes fresh.2.2.1
      cases Nat.lt_or_ge countRoot (state.nextFresh + 1) with
      | inl belowOne =>
          have rootIsBase : countRoot = state.nextFresh :=
            Nat.le_antisymm (Nat.le_of_lt_succ belowOne) rootAtLeastBase
          subst rootIsBase
          rw [sigmaFirstZero,
            if_neg guardFourThree, if_neg guardOneThree, if_neg guardFourBase,
            if_neg guardOneBase,
            cupPair_countOldEvents_congr state positionTargetFirst positionTargetSecond fresh
              forest (state.nextFresh + 3) state.cupEventNodes fresh.2.2.1,
            cupPair_countOldEvents_congr state positionSourceFirst positionSourceSecond fresh
              forest state.nextFresh state.cupEventNodes fresh.2.2.1,
            countLinksZeroAt (state.nextFresh + 3) (Nat.le_add_right state.nextFresh 3),
            countLinksZeroAt state.nextFresh (Nat.le_refl state.nextFresh)]
      | inr rootAtLeastOne =>
      cases Nat.lt_or_ge countRoot (state.nextFresh + 2) with
      | inl belowTwo =>
          have rootIsOne : countRoot = state.nextFresh + 1 :=
            Nat.le_antisymm (Nat.le_of_lt_succ belowTwo) rootAtLeastOne
          subst rootIsOne
          rw [sigmaFirstOne,
            if_pos trueFourFour, if_neg guardOneFour, if_neg guardFourOne, if_pos trueOneOne,
            cupPair_countOldEvents_congr state positionTargetFirst positionTargetSecond fresh
              forest (state.nextFresh + 4) state.cupEventNodes fresh.2.2.1,
            cupPair_countOldEvents_congr state positionSourceFirst positionSourceSecond fresh
              forest (state.nextFresh + 1) state.cupEventNodes fresh.2.2.1,
            countLinksZeroAt (state.nextFresh + 4) (Nat.le_add_right state.nextFresh 4),
            countLinksZeroAt (state.nextFresh + 1) (Nat.le_add_right state.nextFresh 1)]
      | inr rootAtLeastTwo =>
      cases Nat.lt_or_ge countRoot (state.nextFresh + 3) with
      | inl belowThree =>
          have rootIsTwo : countRoot = state.nextFresh + 2 :=
            Nat.le_antisymm (Nat.le_of_lt_succ belowThree) rootAtLeastTwo
          subst rootIsTwo
          rw [sigmaFirstTwo,
            if_neg guardFourFive, if_neg guardOneFive, if_neg guardFourTwo, if_neg guardOneTwo,
            cupPair_countOldEvents_congr state positionTargetFirst positionTargetSecond fresh
              forest (state.nextFresh + 5) state.cupEventNodes fresh.2.2.1,
            cupPair_countOldEvents_congr state positionSourceFirst positionSourceSecond fresh
              forest (state.nextFresh + 2) state.cupEventNodes fresh.2.2.1,
            countLinksZeroAt (state.nextFresh + 5) (Nat.le_add_right state.nextFresh 5),
            countLinksZeroAt (state.nextFresh + 2) (Nat.le_add_right state.nextFresh 2)]
      | inr rootAtLeastThree =>
      cases Nat.lt_or_ge countRoot (state.nextFresh + 4) with
      | inl belowFour =>
          have rootIsThree : countRoot = state.nextFresh + 3 :=
            Nat.le_antisymm (Nat.le_of_lt_succ belowFour) rootAtLeastThree
          subst rootIsThree
          rw [sigmaSecondZero,
            if_neg guardFourBase, if_neg guardOneBase, if_neg guardFourThree,
            if_neg guardOneThree,
            cupPair_countOldEvents_congr state positionTargetFirst positionTargetSecond fresh
              forest state.nextFresh state.cupEventNodes fresh.2.2.1,
            cupPair_countOldEvents_congr state positionSourceFirst positionSourceSecond fresh
              forest (state.nextFresh + 3) state.cupEventNodes fresh.2.2.1,
            countLinksZeroAt state.nextFresh (Nat.le_refl state.nextFresh),
            countLinksZeroAt (state.nextFresh + 3) (Nat.le_add_right state.nextFresh 3)]
      | inr rootAtLeastFour =>
      cases Nat.lt_or_ge countRoot (state.nextFresh + 5) with
      | inl belowFive =>
          have rootIsFour : countRoot = state.nextFresh + 4 :=
            Nat.le_antisymm (Nat.le_of_lt_succ belowFive) rootAtLeastFour
          subst rootIsFour
          rw [sigmaSecondOne,
            if_neg guardFourOne, if_pos trueOneOne, if_pos trueFourFour, if_neg guardOneFour,
            cupPair_countOldEvents_congr state positionTargetFirst positionTargetSecond fresh
              forest (state.nextFresh + 1) state.cupEventNodes fresh.2.2.1,
            cupPair_countOldEvents_congr state positionSourceFirst positionSourceSecond fresh
              forest (state.nextFresh + 4) state.cupEventNodes fresh.2.2.1,
            countLinksZeroAt (state.nextFresh + 1) (Nat.le_add_right state.nextFresh 1),
            countLinksZeroAt (state.nextFresh + 4) (Nat.le_add_right state.nextFresh 4)]
      | inr rootAtLeastFive =>
      cases Nat.lt_or_ge countRoot (state.nextFresh + 6) with
      | inl belowSix =>
          have rootIsFive : countRoot = state.nextFresh + 5 :=
            Nat.le_antisymm (Nat.le_of_lt_succ belowSix) rootAtLeastFive
          subst rootIsFive
          rw [sigmaSecondTwo,
            if_neg guardFourTwo, if_neg guardOneTwo, if_neg guardFourFive, if_neg guardOneFive,
            cupPair_countOldEvents_congr state positionTargetFirst positionTargetSecond fresh
              forest (state.nextFresh + 2) state.cupEventNodes fresh.2.2.1,
            cupPair_countOldEvents_congr state positionSourceFirst positionSourceSecond fresh
              forest (state.nextFresh + 5) state.cupEventNodes fresh.2.2.1,
            countLinksZeroAt (state.nextFresh + 2) (Nat.le_add_right state.nextFresh 2),
            countLinksZeroAt (state.nextFresh + 5) (Nat.le_add_right state.nextFresh 5)]
      | inr rootAtLeastSix =>
          have sigmaFixed : arcFreshBlockTransposition state.nextFresh 3 3 countRoot
              = countRoot :=
            arcFreshBlockTransposition_ofAtOrAbove state.nextFresh 3 3 countRoot rootAtLeastSix
          rw [sigmaFixed,
            cupPair_countOldEvents_congr state positionTargetFirst positionTargetSecond fresh
              forest countRoot state.cupEventNodes fresh.2.2.1,
            cupPair_countOldEvents_congr state positionSourceFirst positionSourceSecond fresh
              forest countRoot state.cupEventNodes fresh.2.2.1]

/-- ★ **The per-root cap-event counts correspond across the transposition.**  Cups push no cap
events, so both sides count the ORIGINAL cap events: below `nextFresh` the transposition is the
identity and old roots collapse to the original links; at or above, both sides count a fresh
root over old events — zero (the transposition maps the at-or-above range into itself). -/
theorem cupPair_capCorr_transposition (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (positionSourceFirst positionSourceSecond positionTargetFirst positionTargetSecond : Nat)
    (countRoot : Nat) :
    countEventsInRoot
        (stepCupArc (stepCupArc state positionTargetFirst) positionTargetSecond).links
        (arcFreshBlockTransposition state.nextFresh 3 3 countRoot)
        (stepCupArc (stepCupArc state positionTargetFirst) positionTargetSecond).capEventNodes
      = countEventsInRoot
          (stepCupArc (stepCupArc state positionSourceFirst) positionSourceSecond).links
          countRoot
          (stepCupArc (stepCupArc state positionSourceFirst) positionSourceSecond).capEventNodes
    := by
  have linkParentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2
  show countEventsInRoot
      (stepCupArc (stepCupArc state positionTargetFirst) positionTargetSecond).links
      (arcFreshBlockTransposition state.nextFresh 3 3 countRoot) state.capEventNodes
    = countEventsInRoot
        (stepCupArc (stepCupArc state positionSourceFirst) positionSourceSecond).links
        countRoot state.capEventNodes
  cases Nat.lt_or_ge countRoot state.nextFresh with
  | inl rootBelow =>
      rw [arcFreshBlockTransposition_ofBelow state.nextFresh 3 3 countRoot rootBelow,
        cupPair_countOldEvents_congr state positionTargetFirst positionTargetSecond fresh forest
          countRoot state.capEventNodes fresh.2.2.2,
        cupPair_countOldEvents_congr state positionSourceFirst positionSourceSecond fresh forest
          countRoot state.capEventNodes fresh.2.2.2]
  | inr rootAtOrAbove =>
      have sigmaImageAtOrAbove :
          state.nextFresh ≤ arcFreshBlockTransposition state.nextFresh 3 3 countRoot :=
        sigmaAtOrAbove_of_fixesBelow (arcFreshBlockTransposition state.nextFresh 3 3)
          (fun firstId secondId imagesEqual =>
            arcFreshBlockTransposition_injective state.nextFresh 3 3 firstId secondId
              imagesEqual)
          state.nextFresh
          (fun identifier isBelow =>
            arcFreshBlockTransposition_ofBelow state.nextFresh 3 3 identifier isBelow)
          countRoot rootAtOrAbove
      rw [cupPair_countOldEvents_congr state positionTargetFirst positionTargetSecond fresh
          forest (arcFreshBlockTransposition state.nextFresh 3 3 countRoot)
          state.capEventNodes fresh.2.2.2,
        cupPair_countOldEvents_congr state positionSourceFirst positionSourceSecond fresh
          forest countRoot state.capEventNodes fresh.2.2.2,
        countEventsInRoot_eq_zero_of_freshRoot state.links state.nextFresh linkParentsBelow
          (arcFreshBlockTransposition state.nextFresh 3 3 countRoot) sigmaImageAtOrAbove
          state.capEventNodes fresh.2.2.2,
        countEventsInRoot_eq_zero_of_freshRoot state.links state.nextFresh linkParentsBelow
          countRoot rootAtOrAbove state.capEventNodes fresh.2.2.2]

/-- ★ **The CUP x CUP two-step core simulation.**  Order S fires the low cup at `positionLow`
then the high cup at `gap + 2 + positionLow`; order T fires the high cup at
`gap + positionLow` then the low cup at `positionLow`.  The fresh-block transposition at
widths `3, 3` is an `ArcStepSimCount` between the results: the wire lists commute through the
iii-1a insert-above-insert kit with the blocks exchanged by the transposition's value laws;
links, event lists, `nextFresh`, and `loops` are position-blind, so the remaining fields are
the three atlas lemmas above and two `rfl`s. -/
theorem arcStepSimCount_cupCupSwap (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (gap positionLow : Nat)
    (positionBound : gap + positionLow ≤ state.openWires.length) :
    ArcStepSimCount (arcFreshBlockTransposition state.nextFresh 3 3)
      (stepCupArc (stepCupArc state positionLow) (gap + 2 + positionLow))
      (stepCupArc (stepCupArc state (gap + positionLow)) positionLow) where
  openMap := by
    have sigmaFirstZero : arcFreshBlockTransposition state.nextFresh 3 3 state.nextFresh
        = state.nextFresh + 3 :=
      arcFreshBlockTransposition_onFirstBlock state.nextFresh 3 3 0 (by decide)
    have sigmaFirstOne :
        arcFreshBlockTransposition state.nextFresh 3 3 (state.nextFresh + 1)
          = state.nextFresh + 4 :=
      arcFreshBlockTransposition_onFirstBlock state.nextFresh 3 3 1 (by decide)
    have sigmaSecondZero :
        arcFreshBlockTransposition state.nextFresh 3 3 (state.nextFresh + 3)
          = state.nextFresh :=
      arcFreshBlockTransposition_onSecondBlock state.nextFresh 3 3 0 (by decide)
    have sigmaSecondOne :
        arcFreshBlockTransposition state.nextFresh 3 3 (state.nextFresh + 4)
          = state.nextFresh + 1 :=
      arcFreshBlockTransposition_onSecondBlock state.nextFresh 3 3 1 (by decide)
    show natListInsertAt
        (natListInsertAt state.openWires (gap + positionLow)
          [state.nextFresh, state.nextFresh + 1])
        positionLow [state.nextFresh + 3, state.nextFresh + 4]
      = (natListInsertAt
          (natListInsertAt state.openWires positionLow
            [state.nextFresh, state.nextFresh + 1])
          (gap + 2 + positionLow) [state.nextFresh + 3, state.nextFresh + 4]).map
          (arcFreshBlockTransposition state.nextFresh 3 3)
    rw [natListInsertAt_map (arcFreshBlockTransposition state.nextFresh 3 3)
        (natListInsertAt state.openWires positionLow [state.nextFresh, state.nextFresh + 1])
        (gap + 2 + positionLow) [state.nextFresh + 3, state.nextFresh + 4],
      natListInsertAt_map (arcFreshBlockTransposition state.nextFresh 3 3)
        state.openWires positionLow [state.nextFresh, state.nextFresh + 1],
      mapPairValues (arcFreshBlockTransposition state.nextFresh 3 3)
        (state.nextFresh + 3) (state.nextFresh + 4),
      mapPairValues (arcFreshBlockTransposition state.nextFresh 3 3)
        state.nextFresh (state.nextFresh + 1),
      sigmaSecondZero, sigmaSecondOne, sigmaFirstZero, sigmaFirstOne,
      mapFixedOn (arcFreshBlockTransposition state.nextFresh 3 3) state.openWires
        (fun wire wireInList =>
          arcFreshBlockTransposition_ofBelow state.nextFresh 3 3 wire
            (fresh.1 wire wireInList)),
      natListInsertAt_insertAbove_commute state.openWires positionLow gap
        [state.nextFresh + 3, state.nextFresh + 4] [state.nextFresh, state.nextFresh + 1]
        positionBound]
    exact rfl
  nfEq := rfl
  rootComm := fun node =>
    cupPair_rootComm_transposition state fresh forest
      positionLow (gap + 2 + positionLow) (gap + positionLow) positionLow node
  loopsEq := rfl
  cupCorr := fun countRoot =>
    cupPair_cupCorr_transposition state fresh forest
      positionLow (gap + 2 + positionLow) (gap + positionLow) positionLow countRoot
  capCorr := fun countRoot =>
    cupPair_capCorr_transposition state fresh forest
      positionLow (gap + 2 + positionLow) (gap + positionLow) positionLow countRoot
  forestS :=
    isUnionFindForest_stepCupArc (stepCupArc state positionLow) (gap + 2 + positionLow)
      (isUnionFindForest_stepCupArc state positionLow forest)
  forestT :=
    isUnionFindForest_stepCupArc (stepCupArc state (gap + positionLow)) positionLow
      (isUnionFindForest_stepCupArc state (gap + positionLow) forest)

/-! ## Honesty marker -/

/-- **Honesty marker — the CUP x CUP two-step core simulation is SHIPPED (ARC-2b brick
iii-1d-alpha2).**  `arcStepSimCount_cupCupSwap`: the two run orders of a cup-cup
disjoint-window swap are `ArcStepSimCount`-related by the fresh-block transposition at widths
`3, 3` — openMap through the iii-1a insert-above-insert kit, rootComm/cupCorr/capCorr through
the alpha1 root atlas (position-generic, since cup links never read positions), nfEq/loopsEq
definitional.  NOT yet shipped: the arity cases involving a CAP (cup-cap, cap-cup, cap-cap —
these need the cap-side root atlas, where the consumed wire VALUES agree between the orders
but loops can TRANSFER between the two atoms in the crossing case), and the dispatcher that
reads the realized ii-b swap pair into these position forms.  `= true`. -/
def fxMode_hasCupCupSwapSimulation : Bool := true

end FX1Poly.Polygraph
