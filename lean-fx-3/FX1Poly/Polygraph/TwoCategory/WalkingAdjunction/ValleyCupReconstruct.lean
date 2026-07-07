import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupBottomPartner

/-! # ValleyCupReconstruct — the full `DiagramType.ext` for `cupRestrict` (Piece II tail, cup assembly)

The cup-side reconstruction `cupRestrict_reconstructs` — the DUAL of the shipped `capRestrict_reconstructs`
(`ValleyCapTopPartner`) — states that the cup block's OWN diagram is `cupRestrict` of the whole valley's
diagram: `matchingOf midWidth cupBlock = cupRestrict (matchingOf bc (capBlock ++ cupBlock))`.  Its three
non-partner fields close unconditionally (`cupRestrict_bottomCount_eq` / `cupRestrict_topCount_eq` /
`cupRestrict_loops_eq`); its `partner` field is a three-way pointwise dispatch:

  * a CUP-BOTTOM port `index < midWidth` — SHIPPED (`cupRestrict_partner_cupBottom`, cup case 1);
  * a CUP-TOP port `midWidth + topOffset` whose whole-valley top `bc + topOffset` is a SURVIVOR-TOP
    (`V.partner[bc + topOffset] < bc`) — SHIPPED (`cupRestrict_partner_survivorTop`, cup case 2);
  * a CUP-TOP port whose whole-valley top is a TOP-TOP CUP ARC (`V.partner[bc + topOffset] ≥ bc`) — the
    genuine cup-specific hard node (cup case 3), the ONLY residual.

This file assembles the full `DiagramType.ext` from the two shipped cases plus a single, precisely-typed
case-3 partner hypothesis `cupTopTopPartner` — the top-top cup-arc partner agreement.  Everything above that
one equation is verified WIRING (a structural mirror of `capRestrict_reconstructs`), so the entire cup
reconstruction — hence `cupRestrict_reconstructs`, and downstream `valleyAppend_split` /
`valleysWithEqualMatching_spineTraceEquiv` — is reduced to exactly the top-top cup-arc partner offset.

## The one residual — case 3 (`cupTopTopPartner`)

A top-top cup arc's two endpoints are BOTH cup legs (the two legs of a single cup — a connectivity-rigid
2-element union-find component; no cap merges cup legs, no other cup merges into them).  The partner VALUE is
therefore always the sibling leg; but its OFFSET in the final open-wire list is fixed by the cup NESTING (how
many cups fired inside), which is a fold over the cup-block window positions — NOT a short chord for nested
cups.  Relating the cup-alone run (from-scratch seed `⟨range midWidth, [], midWidth, 0⟩`, legs `midWidth + k`)
to the in-valley run (from `capState`, legs `bc + k`) at top-top ports is a two-run / general-seed top-top
partner-offset agreement (offset-space floor-shift: `freshShiftAbove (floor + w) 2` on a value `≥ floor` is
`floor +` the floor-independent `freshShiftAbove w 2` in offset space).  The single-run pointwise arc
machinery (`pureCup_internalCupCounts_pointwise`) computes only the top-top INDICATOR, not the partner value,
and is fresh-seed; the two-run offset fold with a general (capState) seed is un-shipped — a multi-session
brick.  No gate flag is flipped; fib-3 also carries the independent Piece-I beam
(`MatchingReductsShareSpineTrace`, #1996).

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local range / map / arithmetic plumbing (propext-free copies) -/

private theorem rangeLoopLenLocal : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLenLocal count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLenLocal (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLenLocal count []]
  exact Nat.add_zero count

private theorem rangeLoopGetAtPastLocal : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAtPastLocal count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAtBelowLocal : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAtBelowLocal count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAtPastLocal count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAtBelowLocal (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAtBelowLocal count [] index indexBelow

private theorem listMapLenLocal {carrier : Type} (mapFn : Nat → carrier) :
    (values : List Nat) → (values.map mapFn).length = values.length
  | [] => rfl
  | _ :: rest => congrArg (· + 1) (listMapLenLocal mapFn rest)

/-- `base + (extra - base) = extra` for `base ≤ extra` (hand-rolled; `Nat.add_sub_cancel'` leaks `propext`). -/
private theorem addSubCancelLocal : (base extra : Nat) → base ≤ extra → base + (extra - base) = extra
  | 0, extra, _ => by rw [Nat.zero_add, Nat.sub_zero]
  | base + 1, 0, atMost => absurd atMost (Nat.not_succ_le_zero base)
  | base + 1, extra + 1, atMost => by
      have inner := addSubCancelLocal base extra (Nat.le_of_succ_le_succ atMost)
      rw [Nat.succ_sub_succ, Nat.succ_add, inner]

/-- `Nat.blt smaller larger = true` when `smaller < larger` (propext-free). -/
private theorem bltTrueOfLt {smaller larger : Nat} (isLess : smaller < larger) :
    Nat.blt smaller larger = true := Nat.ble_eq_true_of_le isLess

/-- `Nat.blt value bound = false` when `bound ≤ value` (propext-free). -/
private theorem bltFalseOfGe {value bound : Nat} (isGe : bound ≤ value) :
    Nat.blt value bound = false := by
  cases probe : Nat.blt value bound with
  | false => rfl
  | true =>
      exact absurd (Nat.lt_of_lt_of_le (Nat.le_of_ble_eq_true probe) isGe) (Nat.lt_irrefl value)

private theorem neTrueOfEqFalse {flag : Bool} (isFalse : flag = false) : ¬ (flag = true) :=
  fun isTrue => Bool.noConfusion (isFalse.symm.trans isTrue)

/-! ## The cup-side reconstruction — the full `DiagramType.ext` (gated on cup case 3) -/

/-- ★ **The cup-side reconstruction (G-assembly), reduced to case 3.**  The cup block's OWN diagram is
`cupRestrict` of the whole valley's diagram: `matchingOf midWidth cupBlock = cupRestrict (matchingOf bc
(capBlock ++ cupBlock))`, where `midWidth = capState.openWires.length`.  Componentwise via
`diagramType_eq_of_fields`: `bottomCount` is the survivor-top total (`cupRestrict_bottomCount_eq`), `topCount`
copies (`cupRestrict_topCount_eq`), `loops` is `0` (`cupRestrict_loops_eq`), and the `partner` list agrees
pointwise (`natListEqOfPointwiseGetAt`) by the three cup partner cases — cup-bottom
(`cupRestrict_partner_cupBottom`, SHIPPED), cup-top survivor (`cupRestrict_partner_survivorTop`, SHIPPED), and
cup-top top-top (`cupTopTopPartner`, the single case-3 hypothesis; see the file header).  The DUAL of the
shipped `capRestrict_reconstructs`. -/
theorem cupRestrict_reconstructs
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock)
    (cupChained : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock)
    (cupTopTopPartner : ∀ {topOffset : Nat},
        topOffset < (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock)
            cupBlock).openWires.length →
        bottomCount ≤ natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
            (bottomCount + topOffset) →
        natListGetAt (matchingOfSpineList
            (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock).partner
            ((processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length + topOffset)
          = (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length
            + (natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
                 (bottomCount + topOffset) - bottomCount)) :
    matchingOfSpineList
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock
      = cupRestrict (matchingOfSpineList bottomCount (capBlock ++ cupBlock)) := by
  let capState := processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock
  have midEq : survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
      = capState.openWires.length :=
    survivorTopTotal_eq_midWidth bottomCount bottomPositive capBlock cupBlock capPure cupPure cupChained
  -- the cup-alone top count equals the whole valley's (the `cupRestrict` copy, unfolded defeq)
  have topCountEq : (matchingOfSpineList capState.openWires.length cupBlock).topCount
      = (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).topCount :=
    cupRestrict_topCount_eq bottomCount capBlock cupBlock cupPure
  apply diagramType_eq_of_fields
  · -- bottomCount
    exact cupRestrict_bottomCount_eq bottomCount bottomPositive capBlock cupBlock capPure cupPure cupChained
  · -- topCount
    exact cupRestrict_topCount_eq bottomCount capBlock cupBlock cupPure
  · -- partner : pointwise
    apply natListEqOfPointwiseGetAt
    · -- lengths
      show ((List.range (capState.openWires.length
          + (matchingOfSpineList capState.openWires.length cupBlock).topCount)).map _).length
        = ((List.range (survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
            + (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).topCount)).map _).length
      rw [listMapLenLocal, listMapLenLocal, rangeLenLocal, rangeLenLocal, midEq, ← topCountEq]
    · -- pointwise agreement
      intro index indexRaw
      have indexLt : index < capState.openWires.length
          + (matchingOfSpineList capState.openWires.length cupBlock).topCount := by
        have lenLHS : (matchingOfSpineList capState.openWires.length cupBlock).partner.length
            = capState.openWires.length
              + (matchingOfSpineList capState.openWires.length cupBlock).topCount := by
          show ((List.range (capState.openWires.length
              + (matchingOfSpineList capState.openWires.length cupBlock).topCount)).map _).length
            = capState.openWires.length
              + (matchingOfSpineList capState.openWires.length cupBlock).topCount
          rw [listMapLenLocal, rangeLenLocal]
        rw [lenLHS] at indexRaw
        exact indexRaw
      -- the RHS range length, in `survivorTopTotal` form
      have indexLtRHS : index < survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
          + (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).topCount := by
        rw [midEq, ← topCountEq]
        exact indexLt
      -- read the reconstructed partner value at `index`, then align `survivorTopTotal V` to `midWidth`
      have mapRead : natListGetAt
            (cupRestrict (matchingOfSpineList bottomCount (capBlock ++ cupBlock))).partner index
          = (if Nat.blt index capState.openWires.length then
              capState.openWires.length
                + (nthSurvivorTop (matchingOfSpineList bottomCount (capBlock ++ cupBlock)) index - bottomCount)
            else
              (if Nat.blt (natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
                      (bottomCount + (index - capState.openWires.length))) bottomCount
                then survivorTopRank (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
                       (bottomCount + (index - capState.openWires.length))
                else capState.openWires.length
                       + (natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
                            (bottomCount + (index - capState.openWires.length)) - bottomCount))) := by
        show natListGetAt ((List.range (survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
              + (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).topCount)).map
            (fun idx =>
              if Nat.blt idx (survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock))) then
                survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
                  + (nthSurvivorTop (matchingOfSpineList bottomCount (capBlock ++ cupBlock)) idx - bottomCount)
              else
                (if Nat.blt (natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
                        (bottomCount + (idx
                          - survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock))))) bottomCount
                  then survivorTopRank (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
                         (bottomCount + (idx
                           - survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock))))
                  else survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
                         + (natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
                              (bottomCount + (idx
                                - survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock))))
                              - bottomCount)))) index = _
        rw [natListGetAt_map_inRange _ _ index (by rw [rangeLenLocal]; exact indexLtRHS),
          rangeGetAtBelowLocal _ index indexLtRHS, midEq]
      rw [mapRead]
      rcases Nat.lt_or_ge index capState.openWires.length with indexBelow | indexAtLeast
      · -- cup-BOTTOM port (case 1)
        rw [if_pos (bltTrueOfLt indexBelow)]
        exact cupRestrict_partner_cupBottom bottomCount bottomPositive capBlock cupBlock capPure cupPure
          cupChained indexBelow
      · -- cup-TOP port
        rw [if_neg (neTrueOfEqFalse (bltFalseOfGe indexAtLeast))]
        have idxEq : capState.openWires.length + (index - capState.openWires.length) = index :=
          addSubCancelLocal capState.openWires.length index indexAtLeast
        have topLt : index - capState.openWires.length
            < (processSpine capState cupBlock).openWires.length := by
          have step : capState.openWires.length + (index - capState.openWires.length)
              < capState.openWires.length + (matchingOfSpineList capState.openWires.length cupBlock).topCount := by
            rw [idxEq]; exact indexLt
          have topEq : (matchingOfSpineList capState.openWires.length cupBlock).topCount
              = (processSpine capState cupBlock).openWires.length := by
            show (processSpine ⟨List.range capState.openWires.length, [], capState.openWires.length, 0⟩
                cupBlock).openWires.length = (processSpine capState cupBlock).openWires.length
            exact processSpine_openWiresLength_congr_ofAllCupArity cupBlock cupPure
              ⟨List.range capState.openWires.length, [], capState.openWires.length, 0⟩ capState
              (rangeLenLocal capState.openWires.length)
          rw [topEq] at step
          exact Nat.lt_of_add_lt_add_left step
        rcases Nat.lt_or_ge
            (natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
              (bottomCount + (index - capState.openWires.length))) bottomCount with wpBelow | wpAbove
        · -- cup-TOP survivor-top port (case 2)
          rw [if_pos (bltTrueOfLt wpBelow)]
          have survivorTop := cupRestrict_partner_survivorTop bottomCount bottomPositive capBlock cupBlock
            capPure cupPure cupChained (topOffset := index - capState.openWires.length) topLt wpBelow
          rw [idxEq] at survivorTop
          exact survivorTop
        · -- cup-TOP top-top cup-arc port (case 3, the hypothesis)
          rw [if_neg (neTrueOfEqFalse (bltFalseOfGe wpAbove))]
          have topTop := cupTopTopPartner (topOffset := index - capState.openWires.length) topLt wpAbove
          rw [idxEq] at topTop
          exact topTop
  · -- loops
    exact cupRestrict_loops_eq bottomCount capBlock cupBlock cupPure

/-! ## Honesty marker -/

/-- **Honesty marker — the full cup-side `DiagramType.ext` (`cupRestrict_reconstructs`) is ASSEMBLED, reduced
to exactly cup case 3 (the top-top cup-arc partner).**

Landed here, zero-axiom:

  * `cupRestrict_reconstructs` — the DUAL of the shipped `capRestrict_reconstructs`: `matchingOf midWidth
    cupBlock = cupRestrict (matchingOf bc (capBlock ++ cupBlock))`, assembled via `diagramType_eq_of_fields`
    from the three unconditional fields (`cupRestrict_bottomCount_eq` / `cupRestrict_topCount_eq` /
    `cupRestrict_loops_eq`) plus the pointwise partner dispatch — cup-bottom (`cupRestrict_partner_cupBottom`,
    SHIPPED), cup-top survivor (`cupRestrict_partner_survivorTop`, SHIPPED), and the SINGLE case-3 hypothesis
    `cupTopTopPartner` (top-top cup-arc partner offset).

This isolates the ENTIRE cup reconstruction — hence `valleyAppend_split` /
`valleysWithEqualMatching_spineTraceEquiv` — to exactly the top-top cup-arc partner offset: a two-run /
general-seed offset-space agreement (both cup runs share the cup block's window fold; the sibling-leg partner
offset shifts floor-independently in offset space).  The single-run pointwise arc characterization
(`pureCup_internalCupCounts_pointwise`) supplies only the top-top INDICATOR, not the partner value, and is
fresh-seed; the two-run offset fold with a general (capState) seed is the un-shipped multi-session brick.  No
gate flag is flipped; fib-3 also carries the independent Piece-I beam (`MatchingReductsShareSpineTrace`,
#1996).  `= true`. -/
def fxMode_hasCupReconstructAssembledToCase3 : Bool := true

end FX1Poly.Polygraph
