import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCapTopPartner
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.CupPositionEmbedding
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupRestrict

/-! # ValleyCupBottomPartner — the cup-BOTTOM and cup-TOP-survivor partner fields of `cupRestrict` (Piece II tail)

The full `DiagramType.ext` for `cupRestrict` (`cupRestrict_reconstructs`) has THREE partner-field cases (the cup
duals of `capRestrict`'s three; see the `ValleyCupRestrict` / `CupPositionEmbedding` honesty markers).  This file
lands the two that ride the seed-agnostic concrete cup embedding `cupPositionEmbedding` — the cup-BOTTOM case
(the dual of the cap survivor-bottom) and the cup-TOP survivor-top case (the dual of the cap-TOP).  Both close
because the survivor scatter between the two cup runs CANCELS under the shared literal embedding `phi =
cupPositionEmbedding cupBlock`:

  * **cup-alone run** — `matchingOf midWidth cupBlock` from the from-scratch seed `⟨range midWidth, [], midWidth, 0⟩`
    (bottoms `0 … midWidth-1`, empty links);
  * **in-valley run** — the cup block acting on `capState` (bottoms the scattered survivor values, cap links).

Both re-rank through the SAME `cupPositionEmbedding cupBlock` (it reads only the cup atoms' firing positions), so a
bottom port `sourcePos < midWidth` lands at the same shifted top position `midWidth + phi sourcePos` (cup-alone) /
`bc + phi sourcePos` (in-valley) in both runs.

  * ★ `cupAlone_survivorPartner` — the cup-ALONE bottom partner: `matchingOf midWidth cupBlock`.partner[sourcePos] =
    `midWidth + cupPositionEmbedding cupBlock sourcePos`.  A from-scratch instance of the cup-shift re-ranking
    (`partnerIndexOf_survivorUnlinked_eq_rank` through `cupPositionEmbedding_isWireOrderEmbedding`), with the
    survivor value read off `range midWidth` and unlinked in the empty base links.
  * ★ `cupRestrict_partner_cupBottom` — the CUP-BOTTOM partner-field agreement: for `sourcePos < midWidth`, the
    cup-alone partner equals `cupRestrict`'s reconstructed value `midWidth + (nthSurvivorTop V sourcePos - bc)`.
    Both equal `midWidth + cupPositionEmbedding cupBlock sourcePos` (RHS via `nthSurvivorTop_correct`).
  * ★ `cupRestrict_partner_survivorTop` — the CUP-TOP survivor-top partner-field agreement: for a cup-top port
    `midWidth + topOffset` whose whole-valley top `bc + topOffset` is a survivor-top (`V.partner[bc+topOffset] <
    bc`), the cup-alone partner equals `cupRestrict`'s reconstructed value `survivorTopRank V (bc + topOffset)`.
    Both equal the survivor rank `sourcePos` (surjectivity `survivorTop_iff_cupImage` gives `topOffset = phi
    sourcePos`; the cup-alone INVOLUTION reflects `midWidth + phi sourcePos` back to `sourcePos`;
    `survivorTop_rankReadoff_ofStrictMono` reads the rank off as `sourcePos`).

## What this file does NOT close — the cup-TOP top-top arc (case 3)

The third cup partner case (`V.partner[bc + topOffset] ≥ bc`, a top-top cup arc internal to the cup block) has NO
cap analogue and is NOT reached by the position embedding (both endpoints are cup legs = non-image positions,
connectivity-determined).  It needs the un-shipped multi-cup component fold of the composite survivor-scatter seed
rename over a non-empty base link list.  So `cupRestrict_reconstructs` (all three cases) — and hence
`valleyAppend_split` / `valleysWithEqualMatching_spineTraceEquiv` — stay gated.  No gate flag is flipped.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local range / arithmetic plumbing (propext-free copies) -/

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

/-- `base + value - base = value` (hand-rolled; `Nat.add_sub_cancel_left` risks a `propext` leak). -/
private theorem addSubCancelLeftLocal : (base value : Nat) → base + value - base = value
  | 0, value => by rw [Nat.zero_add, Nat.sub_zero]
  | base + 1, value => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact addSubCancelLeftLocal base value

/-- An in-range positional read is a member (local copy). -/
private theorem getAt_mem_of_lt : (wires : List Nat) → (index : Nat) →
    index < wires.length → natListGetAt wires index ∈ wires
  | [], _, indexInRange => absurd indexInRange (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, indexInRange =>
      List.Mem.tail _ (getAt_mem_of_lt rest index (Nat.lt_of_succ_lt_succ indexInRange))

/-- `Nat.blt smaller larger = true` when `smaller < larger` (propext-free). -/
private theorem bltTrueOfLt {smaller larger : Nat} (isLess : smaller < larger) :
    Nat.blt smaller larger = true := Nat.ble_eq_true_of_le isLess

/-! ## The cup-alone bottom partner -/

/-- ★ **The cup-ALONE bottom partner.**  For a pure-cup block run from the from-scratch seed
`⟨range midWidth, [], midWidth, 0⟩`, a bottom port `sourcePos < midWidth` has partner
`midWidth + cupPositionEmbedding cupBlock sourcePos`.  The bottom value at position `sourcePos` of `range midWidth`
IS `sourcePos`; it is unlinked in the empty base links, stays unlinked through the cup block
(`processSpine_preservesArcNodeUnlinked_ofAllCupArity`), and reappears at the shifted position
`cupPositionEmbedding cupBlock sourcePos` in the final open wires (`cupPositionEmbedding_isWireOrderEmbedding`,
value-preserving).  The generic read-off `partnerIndexOf_survivorUnlinked_eq_rank` (tolerating the linked cup-leg
tops) pins the partner at `midWidth + cupPositionEmbedding cupBlock sourcePos`. -/
theorem cupAlone_survivorPartner
    {overallSource overallTarget : adjunctionGraph.Mode} (midWidth : Nat)
    (midPositive : 0 < midWidth)
    (cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (cupPure : AllCupArity cupBlock)
    (cupChainedMid : SpineBoundaryChained midWidth cupBlock)
    {sourcePos : Nat} (sourceLt : sourcePos < midWidth) :
    natListGetAt (matchingOfSpineList midWidth cupBlock).partner sourcePos
      = midWidth + cupPositionEmbedding cupBlock sourcePos := by
  have midLen : (⟨List.range midWidth, [], midWidth, 0⟩ : WireState).openWires.length = midWidth :=
    rangeLenLocal midWidth
  have embedding : WireOrderEmbedding (cupPositionEmbedding cupBlock)
      (⟨List.range midWidth, [], midWidth, 0⟩ : WireState).openWires
      (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ cupBlock).openWires :=
    cupPositionEmbedding_isWireOrderEmbedding cupBlock cupPure ⟨List.range midWidth, [], midWidth, 0⟩
      midWidth midLen cupChainedMid
  have sourceLtSeed : sourcePos < (⟨List.range midWidth, [], midWidth, 0⟩ : WireState).openWires.length := by
    rw [midLen]; exact sourceLt
  have valueAtSource : natListGetAt (⟨List.range midWidth, [], midWidth, 0⟩ : WireState).openWires sourcePos
      = sourcePos :=
    rangeGetAtBelowLocal midWidth sourcePos sourceLt
  have survivorUnlinkedMid :
      ArcNodeUnlinked (⟨List.range midWidth, [], midWidth, 0⟩ : WireState).links sourcePos :=
    fun edge edgeMem => nomatch edgeMem
  have survivorUnlinkedWhole :
      ArcNodeUnlinked (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ cupBlock).links sourcePos :=
    processSpine_preservesArcNodeUnlinked_ofAllCupArity cupBlock cupPure
      ⟨List.range midWidth, [], midWidth, 0⟩ sourcePos sourceLt survivorUnlinkedMid
  have wholeDistinct :
      WireListDistinct (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ cupBlock).openWires :=
    processSpine_fromSeed_wireListDistinct midWidth midPositive cupBlock
  have rankWholeLt : cupPositionEmbedding cupBlock sourcePos
      < (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ cupBlock).openWires.length :=
    embedding.inRange sourcePos sourceLtSeed
  have survivorAtRankWhole :
      natListGetAt (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ cupBlock).openWires
        (cupPositionEmbedding cupBlock sourcePos) = sourcePos := by
    rw [embedding.reads sourcePos sourceLtSeed, valueAtSource]
  show natListGetAt (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ cupBlock)).partner
      sourcePos = midWidth + cupPositionEmbedding cupBlock sourcePos
  rw [extractDiagram_partner_getAt midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ cupBlock) sourcePos
    (Nat.lt_of_lt_of_le sourceLt (Nat.le_add_right midWidth
      (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ cupBlock).openWires.length))]
  exact partnerIndexOf_survivorUnlinked_eq_rank
    (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ cupBlock).links midWidth
    (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ cupBlock)
    sourceLt survivorUnlinkedWhole wholeDistinct rankWholeLt survivorAtRankWhole

/-! ## The floor-homogeneous whole-valley roots (two-mode, manual — the cap-file pattern) -/

/-- The whole valley's union-find roots stay floor-separated: below-`bc` nodes keep below-`bc` roots (N1) and
at-or-above-`bc` nodes keep at-or-above roots (N2).  Assembled from the cap edges (all below `bc`) then the cup
fold's floor-preservation (`processSpine_edgesFloorHomogeneous_ofAllCupArity`).  Packaged here so both partner
lemmas share it (the two-mode `capBlock cupBlock : … overallSource overallTarget` form, `capBlock ++ cupBlock`
well-typed). -/
private theorem valleyRootsFloorSeparated
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock) :
    (∀ node, node < bottomCount →
        unionFindRootOf (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock)
          cupBlock).links node < bottomCount)
      ∧ (∀ node, bottomCount ≤ node →
        bottomCount ≤ unionFindRootOf (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩
          capBlock) cupBlock).links node) := by
  have capNextFresh : (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).nextFresh = bottomCount :=
    processSpine_nextFresh_ofAllCapArity_seed bottomCount capBlock capPure
  have capFresh : WireStateFresh (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock) :=
    processSpine_wireStateFresh capBlock ⟨List.range bottomCount, [], bottomCount, 0⟩
      (wireStateFresh_initial bottomCount) bottomPositive
  have capEdgesBelow : ∀ edge ∈ (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).links,
      edge.1 < bottomCount ∧ edge.2 < bottomCount :=
    processSpine_links_below_ofAllCapArity_seed bottomCount bottomPositive capBlock capPure
  have capEdgesHomog : ∀ edge ∈ (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).links,
      edgeFloorHomogeneous bottomCount edge :=
    fun edge edgeIn =>
      ⟨fun floorLe => absurd floorLe (Nat.not_le.mpr (capEdgesBelow edge edgeIn).1),
       fun _ => (capEdgesBelow edge edgeIn).2⟩
  have wholeEdgesHomog : ∀ edge ∈ (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock)
      cupBlock).links, edgeFloorHomogeneous bottomCount edge :=
    processSpine_edgesFloorHomogeneous_ofAllCupArity bottomCount cupBlock cupPure
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock) capFresh
      (Nat.le_of_eq capNextFresh.symm) capEdgesHomog
  exact ⟨fun node nodeBelow =>
      unionFindRootOf_lt_of_edgesBelowFloor _ bottomCount
        (fun edge edgeIn => (wholeEdgesHomog edge edgeIn).2) node nodeBelow,
    fun node nodeAbove =>
      unionFindRootOf_ge_of_edgesPreserveFloor _ bottomCount
        (fun edge edgeIn => (wholeEdgesHomog edge edgeIn).1) node nodeAbove⟩

/-! ## The cup-BOTTOM partner-field agreement (case 1) -/

/-- ★ **The CUP-BOTTOM partner-field agreement.**  For a cup-bottom port `sourcePos < midWidth`
(`midWidth = capState.openWires.length`), the cup block's OWN partner equals `cupRestrict`'s reconstructed value
`midWidth + (nthSurvivorTop V sourcePos - bc)`, where `V = matchingOf bc (capBlock ++ cupBlock)`.  Both sides equal
`midWidth + cupPositionEmbedding cupBlock sourcePos`:

  * LHS (cup-alone): `cupAlone_survivorPartner`;
  * RHS (reconstructed): `nthSurvivorTop V sourcePos = bc + cupPositionEmbedding cupBlock sourcePos`
    (`nthSurvivorTop_correct` on the concrete in-valley embedding), so
    `nthSurvivorTop V sourcePos - bc = cupPositionEmbedding cupBlock sourcePos`. -/
theorem cupRestrict_partner_cupBottom
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock)
    (cupChained : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock)
    {sourcePos : Nat}
    (sourceLt : sourcePos < (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length) :
    natListGetAt (matchingOfSpineList
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock).partner
        sourcePos
      = (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length
        + (nthSurvivorTop (matchingOfSpineList bottomCount (capBlock ++ cupBlock)) sourcePos - bottomCount) := by
  let wholeState := processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock) cupBlock
  have midPositive : 0 < (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length :=
    Nat.lt_of_le_of_lt (Nat.zero_le sourcePos) sourceLt
  obtain ⟨embedding, cover⟩ := cupPositionEmbedding_imageCover bottomCount cupBlock cupPure
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock)
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length rfl
    (Nat.le_of_eq (processSpine_nextFresh_ofAllCapArity_seed bottomCount capBlock capPure).symm) cupChained
  obtain ⟨rootBelowFloor, rootAboveFloor⟩ :=
    valleyRootsFloorSeparated bottomCount bottomPositive capBlock cupBlock capPure cupPure
  have wholeSplit : matchingOfSpineList bottomCount (capBlock ++ cupBlock)
      = extractDiagram bottomCount wholeState := by
    show extractDiagram bottomCount (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩
        (capBlock ++ cupBlock)) = extractDiagram bottomCount wholeState
    rw [processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩]
  have nthEq : nthSurvivorTop (matchingOfSpineList bottomCount (capBlock ++ cupBlock)) sourcePos
      = bottomCount + cupPositionEmbedding cupBlock sourcePos := by
    rw [wholeSplit]
    exact nthSurvivorTop_correct bottomCount wholeState
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires
      rootBelowFloor rootAboveFloor embedding cover
      (fun index indexLt =>
        processSpine_openWires_below_ofAllCapArity_seed bottomCount bottomPositive capBlock capPure
          (natListGetAt (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires index)
          (getAt_mem_of_lt (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires
            index indexLt))
      sourceLt
  rw [nthEq, addSubCancelLeftLocal bottomCount (cupPositionEmbedding cupBlock sourcePos)]
  exact cupAlone_survivorPartner
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length midPositive
    cupBlock cupPure cupChained sourceLt

/-! ## The cup-TOP survivor-top partner-field agreement (case 2) -/

/-- ★ **The CUP-TOP survivor-top partner-field agreement.**  For a cup-top port `midWidth + topOffset` whose
whole-valley top port `bc + topOffset` is a SURVIVOR-TOP (`V.partner[bc + topOffset] < bc`), the cup block's OWN
partner equals `cupRestrict`'s reconstructed value `survivorTopRank V (bc + topOffset)`.  Both sides equal the
survivor rank `sourcePos`:

  * surjectivity (`survivorTop_iff_cupImage`, SHIPPED #2185) writes `topOffset = cupPositionEmbedding cupBlock
    sourcePos` for an in-range survivor rank `sourcePos < midWidth`;
  * RHS: `survivorTopRank V (bc + cupPositionEmbedding cupBlock sourcePos) = sourcePos`
    (`survivorTop_rankReadoff_ofStrictMono`);
  * LHS: the cup-alone INVOLUTION (`matchingOf_partner_isInvolution` on `cupBlock`) reflects the cup-alone bottom
    partner `midWidth + cupPositionEmbedding cupBlock sourcePos` (`cupAlone_survivorPartner`) back to `sourcePos`. -/
theorem cupRestrict_partner_survivorTop
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock)
    (cupChained : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock)
    {topOffset : Nat}
    (topLt : topOffset < (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock)
        cupBlock).openWires.length)
    (survivorTopCond : natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
        (bottomCount + topOffset) < bottomCount) :
    natListGetAt (matchingOfSpineList
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock).partner
        ((processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length + topOffset)
      = survivorTopRank (matchingOfSpineList bottomCount (capBlock ++ cupBlock)) (bottomCount + topOffset) := by
  let wholeState := processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock) cupBlock
  obtain ⟨embedding, cover⟩ := cupPositionEmbedding_imageCover bottomCount cupBlock cupPure
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock)
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length rfl
    (Nat.le_of_eq (processSpine_nextFresh_ofAllCapArity_seed bottomCount capBlock capPure).symm) cupChained
  obtain ⟨rootBelowFloor, rootAboveFloor⟩ :=
    valleyRootsFloorSeparated bottomCount bottomPositive capBlock cupBlock capPure cupPure
  have wholeSplit : matchingOfSpineList bottomCount (capBlock ++ cupBlock)
      = extractDiagram bottomCount wholeState := by
    show extractDiagram bottomCount (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩
        (capBlock ++ cupBlock)) = extractDiagram bottomCount wholeState
    rw [processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩]
  have survivorBelow : ∀ index,
      index < (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length →
      natListGetAt (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires index
        < bottomCount :=
    fun index indexLt =>
      processSpine_openWires_below_ofAllCapArity_seed bottomCount bottomPositive capBlock capPure
        (natListGetAt (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires index)
        (getAt_mem_of_lt (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires
          index indexLt)
  -- The whole-valley top port `bc + topOffset` is a survivor-top.
  have isSurv : isSurvivorTop (extractDiagram bottomCount wholeState) (bottomCount + topOffset) = true := by
    show (Nat.ble bottomCount (bottomCount + topOffset)
        && Nat.blt (natListGetAt (extractDiagram bottomCount wholeState).partner (bottomCount + topOffset))
            bottomCount) = true
    have partnerRead : natListGetAt (extractDiagram bottomCount wholeState).partner (bottomCount + topOffset)
        = natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
            (bottomCount + topOffset) := by
      rw [wholeSplit]
    rw [Nat.ble_eq_true_of_le (Nat.le_add_right bottomCount topOffset), Bool.true_and, partnerRead]
    exact bltTrueOfLt survivorTopCond
  -- Surjectivity: the survivor-top position is a cup-embedding image `topOffset = phi sourcePos`.
  obtain ⟨sourcePos, sourceLt, phiEq⟩ :=
    (survivorTop_iff_cupImage bottomCount wholeState
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires topOffset topLt
      rootBelowFloor rootAboveFloor embedding cover survivorBelow).mp isSurv
  have midPositive : 0 < (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length :=
    Nat.lt_of_le_of_lt (Nat.zero_le sourcePos) sourceLt
  -- RHS: the survivor-top rank read-off collapses to `sourcePos`.
  have rankReadoff : survivorTopRank (extractDiagram bottomCount wholeState)
      (bottomCount + cupPositionEmbedding cupBlock sourcePos) = sourcePos :=
    survivorTop_rankReadoff_ofStrictMono bottomCount wholeState
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires
      rootBelowFloor rootAboveFloor embedding cover survivorBelow sourceLt
  -- LHS: the cup-alone bottom partner, reflected by the involution.
  have cupAloneS : natListGetAt (matchingOfSpineList
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock).partner
      sourcePos
      = (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length
        + cupPositionEmbedding cupBlock sourcePos :=
    cupAlone_survivorPartner
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length midPositive
      cupBlock cupPure cupChained sourceLt
  have notFixed : natListGetAt (matchingOfSpineList
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock).partner
      sourcePos ≠ sourcePos := by
    rw [cupAloneS]
    intro eq
    exact Nat.lt_irrefl sourcePos (Nat.lt_of_lt_of_le
      (Nat.lt_of_lt_of_le sourceLt
        (Nat.le_add_right (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length
          (cupPositionEmbedding cupBlock sourcePos)))
      (Nat.le_of_eq eq))
  have invol := matchingOf_partner_isInvolution
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length midPositive
    cupBlock (spineHasCupCapAtoms_ofAllCupArity cupBlock cupPure) cupChained sourcePos
    (Nat.lt_of_lt_of_le sourceLt (Nat.le_add_right
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length
      (matchingOfSpineList
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock).topCount))
    notFixed
  rw [cupAloneS] at invol
  -- Close: rewrite `topOffset = phi sourcePos`, then LHS = sourcePos (involution) = RHS (rank read-off).
  rw [← phiEq, invol, wholeSplit, rankReadoff]

/-! ## Honesty marker -/

/-- **Honesty marker — the CUP-BOTTOM and CUP-TOP-survivor partner fields of `cupRestrict` AGREE; the cup-TOP
top-top arc (case 3) remains the un-shipped hard node.**

Landed here, all zero-axiom:

  * `cupAlone_survivorPartner` — the cup-ALONE bottom partner `midWidth + cupPositionEmbedding cupBlock sourcePos`,
    a from-scratch-seed instance of the cup-shift re-ranking pinned to the concrete embedding.

  * `cupRestrict_partner_cupBottom` — the CUP-BOTTOM partner agreement (dual of the cap survivor-bottom): both
    sides `= midWidth + cupPositionEmbedding cupBlock sourcePos`.

  * `cupRestrict_partner_survivorTop` — the CUP-TOP survivor-top partner agreement (dual of the cap-TOP): both
    sides `= sourcePos`, via surjectivity (#2185, SHIPPED) + the cup-alone involution + the rank read-off.

What this marker does NOT close — the third cup partner case (`cupRestrict`'s `else` branch,
`V.partner[bc + topOffset] ≥ bc`, a top-top cup arc internal to the cup block): the standalone-cup and in-valley
top-top link structure differ by the composite survivor-scatter seed rename over a NON-EMPTY base link list, and the
position embedding gives NO leverage (both endpoints are cup legs = non-image, connectivity-determined).  Its
multi-cup component fold is un-shipped.  So `cupRestrict_reconstructs` (all three cases) — and hence
`valleyAppend_split` / `valleysWithEqualMatching_spineTraceEquiv` — stay gated.  fib-3 also carries the independent
Piece-I beam (`MatchingReductsShareSpineTrace`, #1996), so `convOfMapEq` stays gated regardless.  No gate flag is
flipped.  `= true`. -/
def fxMode_hasCupBottomAndSurvivorTopPartner : Bool := true

end FX1Poly.Polygraph
