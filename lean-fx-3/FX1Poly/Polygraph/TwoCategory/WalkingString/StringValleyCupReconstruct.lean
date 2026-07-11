import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCupBottomPartner

/-! # WalkingString/StringValleyCupReconstruct — the cup-side `DiagramType.ext` `cupRestrict_reconstructs` (GATED on
the top-top cup-arc case) + the cup-block splitter, over the walking ADJOINT-TRIPLE (`F ⊣ G ⊣ H`) signature
(FC-3 r33, B5: Piece-II cup assembly)

The string clone of the walking-adjunction `ValleyCupRestrict` field agreements + `ValleyCupReconstruct` +
`ValleyCupAssembly`'s cup splitter.  `cupRestrict` (the `def`), the `survivorTopTotal` / `nthSurvivorTop` /
`survivorTopRank` machinery, `diagramType_eq_of_fields`, `natListEqOfPointwiseGetAt`, `natListGetAt_map_inRange`,
`processSpine_append`, `extractDiagram`, `stepCup_openWiresLength` are signature-BLIND — REUSED verbatim by import.
The keyed field/leg lemmas route to their shipped string clones (`stringSurvivorTopTotal_eq_midWidth` r29;
`stringProcessSpine_loops_ofAllCupArity` r32; `stringCupRestrict_partner_cupBottom` / `_partner_survivorTop` r33).

  * ★ `stringProcessSpine_openWiresLength_congr_ofAllCupArity` — a pure-cup block preserves open-wire length across
    equal-length seeds (the two cup runs end at equal top counts).
  * ★ `stringCupRestrict_{loops,bottomCount,topCount}_eq` — the three `cupRestrict` fields that close WITHOUT the
    two-run bridge.
  * ★ `stringCupRestrict_reconstructs` — the cup-side `DiagramType.ext`
    `matchingOf midWidth cupBlock = cupRestrict (matchingOf bc (capBlock ++ cupBlock))`, assembled from the three
    unconditional fields + the cup-bottom (case 1) and cup-top survivor (case 2) partner legs, and GATED on a single
    case-3 hypothesis `stringCupTopTopPartner` — the top-top cup-arc partner agreement, the genuinely asymmetric node
    whose multi-cup component fold over a non-empty base link list is UN-SHIPPED (the string port of `cupTopTopPartner`
    and its `ValleyCupTopTop*`/Arc cluster is a distinct multi-session bill; see the honesty marker).
  * ★ `stringSameWholeMatching_cupBlockMatchingEq` — the cup-block half of the valley-append split (UNCONDITIONAL:
    pure `congrArg cupRestrict` sandwich, taking the two cup reconstruction equations as hypotheses).

The gated reconstruct cannot fire non-vacuously on a concrete cup valley (every cup arc IS a top-top arc, so case 3
is reached, and its ∀-quantified case-3 hypothesis is not `decide`-dischargeable); its constituent partner legs and
the three fields are instead truth-probed on the genuine non-degenerate WIDE valley `[ε] ++ [η']` at
`bottomCount = 4` (mid-width `2`) here and in `StringValleyCupBottomPartner`.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local range / map / arithmetic plumbing (distinct `SCUR` suffix, propext-free copies) -/

private theorem rangeLoopLenSCUR : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLenSCUR count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLenSCUR (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLenSCUR count []]
  exact Nat.add_zero count

private theorem rangeLoopGetAtPastSCUR : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAtPastSCUR count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAtBelowSCUR : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAtBelowSCUR count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAtPastSCUR count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAtBelowSCUR (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAtBelowSCUR count [] index indexBelow

private theorem listMapLenSCUR {carrier : Type} (mapFn : Nat → carrier) :
    (values : List Nat) → (values.map mapFn).length = values.length
  | [] => rfl
  | _ :: rest => congrArg (· + 1) (listMapLenSCUR mapFn rest)

/-- `base + (extra - base) = extra` for `base ≤ extra` (hand-rolled; `Nat.add_sub_cancel'` leaks `propext`). -/
private theorem addSubCancelSCUR : (base extra : Nat) → base ≤ extra → base + (extra - base) = extra
  | 0, extra, _ => by rw [Nat.zero_add, Nat.sub_zero]
  | base + 1, 0, atMost => absurd atMost (Nat.not_succ_le_zero base)
  | base + 1, extra + 1, atMost => by
      have inner := addSubCancelSCUR base extra (Nat.le_of_succ_le_succ atMost)
      rw [Nat.succ_sub_succ, Nat.succ_add, inner]

private theorem bltTrueOfLtSCUR {smaller larger : Nat} (isLess : smaller < larger) :
    Nat.blt smaller larger = true := Nat.ble_eq_true_of_le isLess

private theorem bltFalseOfGeSCUR {value bound : Nat} (isGe : bound ≤ value) :
    Nat.blt value bound = false := by
  cases probe : Nat.blt value bound with
  | false => rfl
  | true =>
      exact absurd (Nat.lt_of_lt_of_le (Nat.le_of_ble_eq_true probe) isGe) (Nat.lt_irrefl value)

private theorem neTrueOfEqFalseSCUR {flag : Bool} (isFalse : flag = false) : ¬ (flag = true) :=
  fun isTrue => Bool.noConfusion (isFalse.symm.trans isTrue)

/-! ## The pure-cup open-wire-length congruence -/

/-- ★ **A pure-cup block preserves open-wire length across equal-length seeds.**  Each cup step adds exactly two
wires regardless of the seed's values, so two runs starting from open-wire states of equal length end at equal
lengths.  The length-only slice of the two-run correspondence — no connectivity bridge. -/
theorem stringProcessSpine_openWiresLength_congr_ofAllCupArity
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    (stateA stateB : WireState) →
    stateA.openWires.length = stateB.openWires.length →
    (processSpine stateA atoms).openWires.length = (processSpine stateB atoms).openWires.length := by
  induction pureCup with
  | nil => intro _ _ lenEq; exact lenEq
  | cons hasCupDomArity hasCupCodArity _restAllCup restCongr =>
      rename_i headAtom rest
      intro stateA stateB lenEq
      show (processSpine (stepAtom stateA headAtom) rest).openWires.length
        = (processSpine (stepAtom stateB headAtom) rest).openWires.length
      rw [stepAtom_ofCupArity stateA headAtom hasCupDomArity hasCupCodArity,
        stepAtom_ofCupArity stateB headAtom hasCupDomArity hasCupCodArity]
      exact restCongr (stepCup stateA headAtom.leftContext.length)
        (stepCup stateB headAtom.leftContext.length)
        (by rw [stepCup_openWiresLength, stepCup_openWiresLength, lenEq])

/-! ## The three cup-field agreements that close WITHOUT the two-run bridge -/

/-- ★ **The `loops` field agrees.**  Both sides are `0`: the cup block from the from-scratch seed closes NO loops
(`stringProcessSpine_loops_ofAllCupArity`, seed loops `0`), and `cupRestrict` hard-sets `loops := 0`. -/
theorem stringCupRestrict_loops_eq
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (capBlock cupBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (cupPure : AllCupArity cupBlock) :
    (matchingOfSpineList
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock).loops
      = (cupRestrict (matchingOfSpineList bottomCount (capBlock ++ cupBlock))).loops :=
  stringProcessSpine_loops_ofAllCupArity cupBlock cupPure
    ⟨List.range (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length, [],
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length, 0⟩

/-- ★ **The `bottomCount` field agrees.**  The cup block's own bottom count is `midWidth`
(`= capState.openWires.length`), and `cupRestrict`'s reconstructed `bottomCount` is `survivorTopTotal V`, which
`stringSurvivorTopTotal_eq_midWidth` proves is exactly `midWidth`. -/
theorem stringCupRestrict_bottomCount_eq
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock)
    (cupChained : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock) :
    (matchingOfSpineList
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock).bottomCount
      = (cupRestrict (matchingOfSpineList bottomCount (capBlock ++ cupBlock))).bottomCount :=
  (stringSurvivorTopTotal_eq_midWidth bottomCount bottomPositive capBlock cupBlock capPure cupPure cupChained).symm

/-- ★ **The `topCount` field agrees.**  Both cup runs — the cup-alone run from `⟨range midWidth, …⟩` and the whole
valley's cup part from `capState` — start from open-wire states of EQUAL length `midWidth` (`rangeLenSCUR`), and each
cup adds exactly two, so they end at equal open-wire lengths
(`stringProcessSpine_openWiresLength_congr_ofAllCupArity`). -/
theorem stringCupRestrict_topCount_eq
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (capBlock cupBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (cupPure : AllCupArity cupBlock) :
    (matchingOfSpineList
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock).topCount
      = (cupRestrict (matchingOfSpineList bottomCount (capBlock ++ cupBlock))).topCount := by
  let capState := processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock
  have wholeSplit : matchingOfSpineList bottomCount (capBlock ++ cupBlock)
      = extractDiagram bottomCount (processSpine capState cupBlock) := by
    show extractDiagram bottomCount (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩
        (capBlock ++ cupBlock)) = extractDiagram bottomCount (processSpine capState cupBlock)
    rw [processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩]
  show (processSpine ⟨List.range capState.openWires.length, [], capState.openWires.length, 0⟩ cupBlock).openWires.length
      = (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).topCount
  rw [wholeSplit]
  show (processSpine ⟨List.range capState.openWires.length, [], capState.openWires.length, 0⟩ cupBlock).openWires.length
      = (processSpine capState cupBlock).openWires.length
  exact stringProcessSpine_openWiresLength_congr_ofAllCupArity cupBlock cupPure
    ⟨List.range capState.openWires.length, [], capState.openWires.length, 0⟩ capState
    (rangeLenSCUR capState.openWires.length)

/-! ## The cup-side reconstruction — the full `DiagramType.ext` (gated on the top-top cup-arc case 3) -/

/-- ★ **The cup-side reconstruction (G-assembly), gated on case 3.**  The cup block's OWN diagram is `cupRestrict`
of the whole valley's diagram: `matchingOf midWidth cupBlock = cupRestrict (matchingOf bc (capBlock ++ cupBlock))`,
where `midWidth = capState.openWires.length`.  Componentwise via `diagramType_eq_of_fields`: `bottomCount` is the
survivor-top total (`stringCupRestrict_bottomCount_eq`), `topCount` copies (`stringCupRestrict_topCount_eq`), `loops`
is `0` (`stringCupRestrict_loops_eq`), and the `partner` list agrees pointwise by the three cup partner cases —
cup-bottom (`stringCupRestrict_partner_cupBottom`), cup-top survivor (`stringCupRestrict_partner_survivorTop`), and
cup-top top-top (the single case-3 hypothesis `stringCupTopTopPartner`, whose string port is un-shipped). -/
theorem stringCupRestrict_reconstructs
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock)
    (cupChained : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock)
    (wholeChained : SpineBoundaryChained bottomCount (capBlock ++ cupBlock))
    (midPositive : 0 <
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length)
    (stringCupTopTopPartner :
      ∀ {topOffset : Nat},
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
    stringSurvivorTopTotal_eq_midWidth bottomCount bottomPositive capBlock cupBlock capPure cupPure cupChained
  have topCountEq : (matchingOfSpineList capState.openWires.length cupBlock).topCount
      = (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).topCount :=
    stringCupRestrict_topCount_eq bottomCount capBlock cupBlock cupPure
  apply diagramType_eq_of_fields
  · exact stringCupRestrict_bottomCount_eq bottomCount bottomPositive capBlock cupBlock capPure cupPure cupChained
  · exact stringCupRestrict_topCount_eq bottomCount capBlock cupBlock cupPure
  · apply natListEqOfPointwiseGetAt
    · show ((List.range (capState.openWires.length
          + (matchingOfSpineList capState.openWires.length cupBlock).topCount)).map _).length
        = ((List.range (survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
            + (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).topCount)).map _).length
      rw [listMapLenSCUR, listMapLenSCUR, rangeLenSCUR, rangeLenSCUR, midEq, ← topCountEq]
    · intro index indexRaw
      have indexLt : index < capState.openWires.length
          + (matchingOfSpineList capState.openWires.length cupBlock).topCount := by
        have lenLHS : (matchingOfSpineList capState.openWires.length cupBlock).partner.length
            = capState.openWires.length
              + (matchingOfSpineList capState.openWires.length cupBlock).topCount := by
          show ((List.range (capState.openWires.length
              + (matchingOfSpineList capState.openWires.length cupBlock).topCount)).map _).length
            = capState.openWires.length
              + (matchingOfSpineList capState.openWires.length cupBlock).topCount
          rw [listMapLenSCUR, rangeLenSCUR]
        rw [lenLHS] at indexRaw
        exact indexRaw
      have indexLtRHS : index < survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
          + (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).topCount := by
        rw [midEq, ← topCountEq]
        exact indexLt
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
        rw [natListGetAt_map_inRange _ _ index (by rw [rangeLenSCUR]; exact indexLtRHS),
          rangeGetAtBelowSCUR _ index indexLtRHS, midEq]
      rw [mapRead]
      rcases Nat.lt_or_ge index capState.openWires.length with indexBelow | indexAtLeast
      · rw [if_pos (bltTrueOfLtSCUR indexBelow)]
        exact stringCupRestrict_partner_cupBottom bottomCount bottomPositive capBlock cupBlock capPure cupPure
          cupChained indexBelow
      · rw [if_neg (neTrueOfEqFalseSCUR (bltFalseOfGeSCUR indexAtLeast))]
        have idxEq : capState.openWires.length + (index - capState.openWires.length) = index :=
          addSubCancelSCUR capState.openWires.length index indexAtLeast
        have topLt : index - capState.openWires.length
            < (processSpine capState cupBlock).openWires.length := by
          have step : capState.openWires.length + (index - capState.openWires.length)
              < capState.openWires.length + (matchingOfSpineList capState.openWires.length cupBlock).topCount := by
            rw [idxEq]; exact indexLt
          have topEq : (matchingOfSpineList capState.openWires.length cupBlock).topCount
              = (processSpine capState cupBlock).openWires.length := by
            show (processSpine ⟨List.range capState.openWires.length, [], capState.openWires.length, 0⟩
                cupBlock).openWires.length = (processSpine capState cupBlock).openWires.length
            exact stringProcessSpine_openWiresLength_congr_ofAllCupArity cupBlock cupPure
              ⟨List.range capState.openWires.length, [], capState.openWires.length, 0⟩ capState
              (rangeLenSCUR capState.openWires.length)
          rw [topEq] at step
          exact Nat.lt_of_add_lt_add_left step
        rcases Nat.lt_or_ge
            (natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
              (bottomCount + (index - capState.openWires.length))) bottomCount with wpBelow | wpAbove
        · rw [if_pos (bltTrueOfLtSCUR wpBelow)]
          have survivorTop := stringCupRestrict_partner_survivorTop bottomCount bottomPositive capBlock cupBlock
            capPure cupPure cupChained (topOffset := index - capState.openWires.length) topLt wpBelow
          rw [idxEq] at survivorTop
          exact survivorTop
        · rw [if_neg (neTrueOfEqFalseSCUR (bltFalseOfGeSCUR wpAbove))]
          have topTop := stringCupTopTopPartner (topOffset := index - capState.openWires.length) topLt wpAbove
          rw [idxEq] at topTop
          exact topTop
  · exact stringCupRestrict_loops_eq bottomCount capBlock cupBlock cupPure

/-! ## The cup half of the valley-append split (UNCONDITIONAL — takes the two reconstructions as hypotheses) -/

/-- ★ **The cup-block half of the valley-append split.**  Two valleys `capBlock ++ cupBlock` with EQUAL whole
`matchingOf` have EQUAL cup-block `matchingOf` (each read at its OWN mid-width).  The DUAL of the shipped
`stringSameWholeMatching_capBlockMatchingEq`: derived by `congrArg cupRestrict` over the whole equality, sandwiched
between the two cup reconstruction equations.  The cup block's own diagram is a FUNCTION (`cupRestrict`) of the whole
valley's diagram, so equal wholes force equal cup blocks.  Unconditional — the reconstruction equations are supplied
by the caller (via `stringCupRestrict_reconstructs`, gated on case 3). -/
theorem stringSameWholeMatching_cupBlockMatchingEq
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (capBlockFirst capBlockSecond cupBlockFirst cupBlockSecond :
      List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (cupReconstructsFirst :
      matchingOfSpineList
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockFirst
        = cupRestrict (matchingOfSpineList bottomCount (capBlockFirst ++ cupBlockFirst)))
    (cupReconstructsSecond :
      matchingOfSpineList
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length cupBlockSecond
        = cupRestrict (matchingOfSpineList bottomCount (capBlockSecond ++ cupBlockSecond)))
    (wholeEq : matchingOfSpineList bottomCount (capBlockFirst ++ cupBlockFirst)
      = matchingOfSpineList bottomCount (capBlockSecond ++ cupBlockSecond)) :
    matchingOfSpineList
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockFirst
      = matchingOfSpineList
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length cupBlockSecond :=
  cupReconstructsFirst.trans ((congrArg cupRestrict wholeEq).trans cupReconstructsSecond.symm)

/-! ## Concrete truth-probes — the three cup fields FIRE on the non-degenerate wide valley -/

/-- ★ **The cup `bottomCount` field FIRES on the genuine non-degenerate wide valley.**  On `[ε] ++ [η']` at
`bottomCount = 4` (mid-width `2`), the cup block's own bottom count equals `cupRestrict`'s reconstructed
`survivorTopTotal` — a real inhabitation with non-zero mid content. -/
theorem stringCupRestrict_bottomCount_eq_firesOnWideValley :
    (matchingOfSpineList
        (processSpine ⟨List.range 4, [], 4, 0⟩ [stringWideProbeCapAtom]).openWires.length
        [stringWideProbeCupAtom]).bottomCount
      = (cupRestrict (matchingOfSpineList 4 ([stringWideProbeCapAtom] ++ [stringWideProbeCupAtom]))).bottomCount :=
  stringCupRestrict_bottomCount_eq 4 (by decide) [stringWideProbeCapAtom] [stringWideProbeCupAtom]
    stringWideProbeCapBlock_pureCap stringWideProbeCupBlock_pureCup stringWideProbeCupBlock_chained

/-- ★ **The cup `topCount` field FIRES on the wide valley.**  Both cup runs end at equal top counts. -/
theorem stringCupRestrict_topCount_eq_firesOnWideValley :
    (matchingOfSpineList
        (processSpine ⟨List.range 4, [], 4, 0⟩ [stringWideProbeCapAtom]).openWires.length
        [stringWideProbeCupAtom]).topCount
      = (cupRestrict (matchingOfSpineList 4 ([stringWideProbeCapAtom] ++ [stringWideProbeCupAtom]))).topCount :=
  stringCupRestrict_topCount_eq 4 [stringWideProbeCapAtom] [stringWideProbeCupAtom] stringWideProbeCupBlock_pureCup

/-- ★ **The cup `loops` field FIRES on the wide valley.**  Both sides `0`: cups close no loops. -/
theorem stringCupRestrict_loops_eq_firesOnWideValley :
    (matchingOfSpineList
        (processSpine ⟨List.range 4, [], 4, 0⟩ [stringWideProbeCapAtom]).openWires.length
        [stringWideProbeCupAtom]).loops
      = (cupRestrict (matchingOfSpineList 4 ([stringWideProbeCapAtom] ++ [stringWideProbeCupAtom]))).loops :=
  stringCupRestrict_loops_eq 4 [stringWideProbeCapAtom] [stringWideProbeCupAtom] stringWideProbeCupBlock_pureCup

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the string cup-side `DiagramType.ext` `stringCupRestrict_reconstructs` is SHIPPED (GATED on the
top-top cup-arc case 3), and the cup-block splitter `stringSameWholeMatching_cupBlockMatchingEq` is UNCONDITIONAL,
zero-axiom (FC-3 r33, B5 Piece-II cup assembly).**  Landed here over the walking ADJOINT-TRIPLE signature as a
byte-identical token-swap of `ValleyCupRestrict` (field agreements) + `ValleyCupReconstruct` (the ext) +
`ValleyCupAssembly` (the cup splitter):

  * `stringProcessSpine_openWiresLength_congr_ofAllCupArity` + `stringCupRestrict_{loops,bottomCount,topCount}_eq` —
    the three cup fields that close WITHOUT the two-run bridge;
  * `stringCupRestrict_reconstructs` — the cup-side reconstruction, assembled from the three unconditional fields +
    the cup-bottom (case 1, `stringCupRestrict_partner_cupBottom`) and cup-top survivor (case 2,
    `stringCupRestrict_partner_survivorTop`) partner legs, GATED on a single case-3 hypothesis
    `stringCupTopTopPartner`;
  * `stringSameWholeMatching_cupBlockMatchingEq` — the cup-block half of the valley-append split, UNCONDITIONAL
    (pure `congrArg cupRestrict`, taking the two cup reconstruction equations as hypotheses).

The three cup fields are truth-probed on the genuine NON-DEGENERATE WIDE valley `[ε] ++ [η']` at `bottomCount = 4`
(mid-width `2`).  The gated reconstruct is NOT probed concretely: every cup arc IS a top-top arc, so case 3 is
reached on any real cup valley, and its ∀-quantified case-3 hypothesis over a symbolic matching is not
`decide`-dischargeable.

The named jamming dependency (the B5 residual, sized IN THIS FILE): the case-3 hypothesis `stringCupTopTopPartner`
is the string port of the walking-adjunction `cupTopTopPartner` (`ValleyCupTopTopSeed`), whose UNCONDITIONAL discharge
transitively needs the entire `ValleyCupTopTop{Seed,Fold,FloorShift,StepTransport}` cluster (~1051 lines) PLUS its
deep Arc dependency cluster (`ArcCensusCupPreservation`, `ArcDisciplineFold`, `ArcBoundaryTracking`,
`ArcPureCupSpine`, `ArcCupStepDrop`, `ArcCupLastCupReadoff`, `ArcSwapRenameable`, `PureCapSurvivorReadoff`,
`PureCapSurvivorUnlinked`, `MatchingPartnerInvolution`) + `ValleyCupCapStatePromotion` — a multi-session port, NOT a
one-file token-swap.  Until that ships as `stringCupTopTopPartner`, `stringCupRestrict_reconstructs` stays gated, so
`stringValleyAppend_split` / `stringValleysWithEqualMatching_spineTraceEquiv` (the latter also needs the un-ported
`valleysWithBlockMatchingEq_spineTraceEquiv` interface) remain unreachable, and the completeness/producer flips
`fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) / `fxString_hasConvOfMapEqPortFlip`
(`StringConvOfMapEqPort`) stay `false`.  This round flips ONLY this NEW cup marker.  `= true`. -/
def fxString_hasCupRestrictReconstructsGatedOnCupTopTop : Bool := true

end FX1Poly.Polygraph
