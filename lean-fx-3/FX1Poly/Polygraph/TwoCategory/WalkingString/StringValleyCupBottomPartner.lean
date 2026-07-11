import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCupPositionEmbedding
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCapReconstruct
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupRestrict
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyMatchingSurjectivity

/-! # WalkingString/StringValleyCupBottomPartner — the cup-BOTTOM and cup-TOP-survivor partner fields of `cupRestrict`
over the walking ADJOINT-TRIPLE (`F ⊣ G ⊣ H`) signature (FC-3 r33, B5: Piece-II cup tail)

The string clone of the walking-adjunction `ValleyCupBottomPartner`.  The cup-side reconstruction has THREE
partner-field cases (the cup duals of `capRestrict`'s three); this file lands the two that ride the seed-agnostic
concrete cup embedding `stringCupPositionEmbedding` — the cup-BOTTOM case (dual of the cap survivor-bottom) and the
cup-TOP survivor-top case (dual of the cap-TOP).  Both close because the survivor scatter between the two cup runs
CANCELS under the shared literal embedding `phi = stringCupPositionEmbedding cupBlock` (it reads only the cup atoms'
firing positions), so a bottom port `sourcePos < midWidth` lands at the same shifted top position in both runs:

  * **cup-alone run** — `matchingOf midWidth cupBlock` from the from-scratch seed `⟨range midWidth, [], midWidth, 0⟩`;
  * **in-valley run** — the cup block acting on `capState`.

Every keyed substrate lemma routes to its shipped string clone (`stringCupPositionEmbedding_isWireOrderEmbedding` /
`_imageCover` from r33's keystone; `stringProcessSpine_preservesArcNodeUnlinked_ofAllCupArity` from r32; the
`stringProcessSpine_{nextFresh,links_below,openWires_below}_ofAllCapArity_seed` /
`stringProcessSpine_edgesFloorHomogeneous_ofAllCupArity` seed leg from r29; `stringMatchingOf_partner_isInvolution`
from r31); the read-off substrate (`partnerIndexOf_survivorUnlinked_eq_rank`, `extractDiagram_partner_getAt`,
`nthSurvivorTop_correct`, `survivorTop_iff_cupImage`, `survivorTop_rankReadoff_ofStrictMono`,
`processSpine_fromSeed_wireListDistinct`, `processSpine_wireStateFresh`, `wireStateFresh_initial`,
`unionFindRootOf_{lt,ge}…`, `spineHasCupCapAtoms_ofAllCupArity`) and the `cupRestrict` def are signature-BLIND —
REUSED verbatim by import.  Every brick below is a byte-identical token-swap of the walking-adjunction original,
rerouting the signature token alone `adjunctionModeSignature → adjointTripleModeSignature`.

  * ★ `stringCupAlone_survivorPartner` — the cup-ALONE bottom partner `midWidth + stringCupPositionEmbedding cupBlock
    sourcePos`, a from-scratch-seed instance of the cup-shift re-ranking pinned to the concrete embedding.  Carries
    the `midPositive : 0 < midWidth` guard (its sole use is the from-seed wire-distinctness).
  * ★ `stringCupRestrict_partner_cupBottom` — the CUP-BOTTOM partner agreement: both sides
    `= midWidth + stringCupPositionEmbedding cupBlock sourcePos`.
  * ★ `stringCupRestrict_partner_survivorTop` — the CUP-TOP survivor-top partner agreement: both sides `= sourcePos`,
    via surjectivity + the cup-alone involution + the rank read-off.

Two truth-probes fire the cup-bottom leg + the cup-alone partner on the genuine NON-DEGENERATE WIDE valley `[ε] ++
[η']` at `bottomCount = 4` (mid-width `2`, `stringWideProbeCupBlock_chained`), so `midPositive` is genuinely
satisfied (mid-width `2 > 0`).  What this file does NOT close — the cup-TOP top-top cup-arc case (case 3), the
genuinely asymmetric node needing the un-shipped multi-cup component fold.  No gate flag is flipped.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local range / arithmetic plumbing (distinct `SCBP` suffix, propext-free copies) -/

private theorem rangeLoopLenSCBP : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLenSCBP count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLenSCBP (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLenSCBP count []]
  exact Nat.add_zero count

private theorem rangeLoopGetAtPastSCBP : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAtPastSCBP count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAtBelowSCBP : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAtBelowSCBP count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAtPastSCBP count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAtBelowSCBP (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAtBelowSCBP count [] index indexBelow

/-- `base + value - base = value` (hand-rolled; `Nat.add_sub_cancel_left` risks a `propext` leak). -/
private theorem addSubCancelLeftSCBP : (base value : Nat) → base + value - base = value
  | 0, value => by rw [Nat.zero_add, Nat.sub_zero]
  | base + 1, value => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact addSubCancelLeftSCBP base value

/-- An in-range positional read is a member (local copy). -/
private theorem getAtMemOfLtSCBP : (wires : List Nat) → (index : Nat) →
    index < wires.length → natListGetAt wires index ∈ wires
  | [], _, indexInRange => absurd indexInRange (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, indexInRange =>
      List.Mem.tail _ (getAtMemOfLtSCBP rest index (Nat.lt_of_succ_lt_succ indexInRange))

/-- `Nat.blt smaller larger = true` when `smaller < larger` (propext-free). -/
private theorem bltTrueOfLtSCBP {smaller larger : Nat} (isLess : smaller < larger) :
    Nat.blt smaller larger = true := Nat.ble_eq_true_of_le isLess

/-! ## The cup-alone bottom partner -/

/-- ★ **The cup-ALONE bottom partner.**  For a pure-cup block run from the from-scratch seed
`⟨range midWidth, [], midWidth, 0⟩`, a bottom port `sourcePos < midWidth` has partner
`midWidth + stringCupPositionEmbedding cupBlock sourcePos`.  The bottom value at position `sourcePos` of
`range midWidth` IS `sourcePos`; it is unlinked in the empty base links, stays unlinked through the cup block
(`stringProcessSpine_preservesArcNodeUnlinked_ofAllCupArity`), and reappears at the shifted position
`stringCupPositionEmbedding cupBlock sourcePos` in the final open wires
(`stringCupPositionEmbedding_isWireOrderEmbedding`, value-preserving).  The generic read-off
`partnerIndexOf_survivorUnlinked_eq_rank` pins the partner at `midWidth + stringCupPositionEmbedding cupBlock
sourcePos`. -/
theorem stringCupAlone_survivorPartner
    {overallSource overallTarget : adjointTripleGraph.Mode} (midWidth : Nat)
    (midPositive : 0 < midWidth)
    (cupBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (cupPure : AllCupArity cupBlock)
    (cupChainedMid : SpineBoundaryChained midWidth cupBlock)
    {sourcePos : Nat} (sourceLt : sourcePos < midWidth) :
    natListGetAt (matchingOfSpineList midWidth cupBlock).partner sourcePos
      = midWidth + stringCupPositionEmbedding cupBlock sourcePos := by
  have midLen : (⟨List.range midWidth, [], midWidth, 0⟩ : WireState).openWires.length = midWidth :=
    rangeLenSCBP midWidth
  have embedding : WireOrderEmbedding (stringCupPositionEmbedding cupBlock)
      (⟨List.range midWidth, [], midWidth, 0⟩ : WireState).openWires
      (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ cupBlock).openWires :=
    stringCupPositionEmbedding_isWireOrderEmbedding cupBlock cupPure ⟨List.range midWidth, [], midWidth, 0⟩
      midWidth midLen cupChainedMid
  have sourceLtSeed : sourcePos < (⟨List.range midWidth, [], midWidth, 0⟩ : WireState).openWires.length := by
    rw [midLen]; exact sourceLt
  have valueAtSource : natListGetAt (⟨List.range midWidth, [], midWidth, 0⟩ : WireState).openWires sourcePos
      = sourcePos :=
    rangeGetAtBelowSCBP midWidth sourcePos sourceLt
  have survivorUnlinkedMid :
      ArcNodeUnlinked (⟨List.range midWidth, [], midWidth, 0⟩ : WireState).links sourcePos :=
    fun edge edgeMem => nomatch edgeMem
  have survivorUnlinkedWhole :
      ArcNodeUnlinked (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ cupBlock).links sourcePos :=
    stringProcessSpine_preservesArcNodeUnlinked_ofAllCupArity cupBlock cupPure
      ⟨List.range midWidth, [], midWidth, 0⟩ sourcePos sourceLt survivorUnlinkedMid
  have wholeDistinct :
      WireListDistinct (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ cupBlock).openWires :=
    processSpine_fromSeed_wireListDistinct midWidth midPositive cupBlock
  have rankWholeLt : stringCupPositionEmbedding cupBlock sourcePos
      < (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ cupBlock).openWires.length :=
    embedding.inRange sourcePos sourceLtSeed
  have survivorAtRankWhole :
      natListGetAt (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ cupBlock).openWires
        (stringCupPositionEmbedding cupBlock sourcePos) = sourcePos := by
    rw [embedding.reads sourcePos sourceLtSeed, valueAtSource]
  show natListGetAt (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ cupBlock)).partner
      sourcePos = midWidth + stringCupPositionEmbedding cupBlock sourcePos
  rw [extractDiagram_partner_getAt midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ cupBlock) sourcePos
    (Nat.lt_of_lt_of_le sourceLt (Nat.le_add_right midWidth
      (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ cupBlock).openWires.length))]
  exact partnerIndexOf_survivorUnlinked_eq_rank
    (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ cupBlock).links midWidth
    (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ cupBlock)
    sourceLt survivorUnlinkedWhole wholeDistinct rankWholeLt survivorAtRankWhole

/-! ## The floor-homogeneous whole-valley roots (two-mode, manual) -/

/-- The whole valley's union-find roots stay floor-separated: below-`bc` nodes keep below-`bc` roots (N1) and
at-or-above-`bc` nodes keep at-or-above roots (N2).  Assembled from the cap edges (all below `bc`) then the cup
fold's floor-preservation (`stringProcessSpine_edgesFloorHomogeneous_ofAllCupArity`).  Packaged here so both partner
lemmas share it. -/
private theorem stringValleyRootsFloorSeparated
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock) :
    (∀ node, node < bottomCount →
        unionFindRootOf (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock)
          cupBlock).links node < bottomCount)
      ∧ (∀ node, bottomCount ≤ node →
        bottomCount ≤ unionFindRootOf (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩
          capBlock) cupBlock).links node) := by
  have capNextFresh : (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).nextFresh = bottomCount :=
    stringProcessSpine_nextFresh_ofAllCapArity_seed bottomCount capBlock capPure
  have capFresh : WireStateFresh (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock) :=
    processSpine_wireStateFresh capBlock ⟨List.range bottomCount, [], bottomCount, 0⟩
      (wireStateFresh_initial bottomCount) bottomPositive
  have capEdgesBelow : ∀ edge ∈ (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).links,
      edge.1 < bottomCount ∧ edge.2 < bottomCount :=
    stringProcessSpine_links_below_ofAllCapArity_seed bottomCount bottomPositive capBlock capPure
  have capEdgesHomog : ∀ edge ∈ (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).links,
      edgeFloorHomogeneous bottomCount edge :=
    fun edge edgeIn =>
      ⟨fun floorLe => absurd floorLe (Nat.not_le.mpr (capEdgesBelow edge edgeIn).1),
       fun _ => (capEdgesBelow edge edgeIn).2⟩
  have wholeEdgesHomog : ∀ edge ∈ (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock)
      cupBlock).links, edgeFloorHomogeneous bottomCount edge :=
    stringProcessSpine_edgesFloorHomogeneous_ofAllCupArity bottomCount cupBlock cupPure
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
`midWidth + stringCupPositionEmbedding cupBlock sourcePos`: LHS (cup-alone) via `stringCupAlone_survivorPartner`;
RHS via `nthSurvivorTop V sourcePos = bc + stringCupPositionEmbedding cupBlock sourcePos` (`nthSurvivorTop_correct`
on the concrete in-valley embedding). -/
theorem stringCupRestrict_partner_cupBottom
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
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
  obtain ⟨embedding, cover⟩ := stringCupPositionEmbedding_imageCover bottomCount cupBlock cupPure
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock)
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length rfl
    (Nat.le_of_eq (stringProcessSpine_nextFresh_ofAllCapArity_seed bottomCount capBlock capPure).symm) cupChained
  obtain ⟨rootBelowFloor, rootAboveFloor⟩ :=
    stringValleyRootsFloorSeparated bottomCount bottomPositive capBlock cupBlock capPure cupPure
  have wholeSplit : matchingOfSpineList bottomCount (capBlock ++ cupBlock)
      = extractDiagram bottomCount wholeState := by
    show extractDiagram bottomCount (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩
        (capBlock ++ cupBlock)) = extractDiagram bottomCount wholeState
    rw [processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩]
  have nthEq : nthSurvivorTop (matchingOfSpineList bottomCount (capBlock ++ cupBlock)) sourcePos
      = bottomCount + stringCupPositionEmbedding cupBlock sourcePos := by
    rw [wholeSplit]
    exact nthSurvivorTop_correct bottomCount wholeState
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires
      rootBelowFloor rootAboveFloor embedding cover
      (fun index indexLt =>
        stringProcessSpine_openWires_below_ofAllCapArity_seed bottomCount bottomPositive capBlock capPure
          (natListGetAt (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires index)
          (getAtMemOfLtSCBP (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires
            index indexLt))
      sourceLt
  rw [nthEq, addSubCancelLeftSCBP bottomCount (stringCupPositionEmbedding cupBlock sourcePos)]
  exact stringCupAlone_survivorPartner
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length midPositive
    cupBlock cupPure cupChained sourceLt

/-! ## The cup-TOP survivor-top partner-field agreement (case 2) -/

/-- ★ **The CUP-TOP survivor-top partner-field agreement.**  For a cup-top port `midWidth + topOffset` whose
whole-valley top port `bc + topOffset` is a SURVIVOR-TOP (`V.partner[bc + topOffset] < bc`), the cup block's OWN
partner equals `cupRestrict`'s reconstructed value `survivorTopRank V (bc + topOffset)`.  Both sides equal the
survivor rank `sourcePos`: surjectivity (`survivorTop_iff_cupImage`) writes `topOffset = stringCupPositionEmbedding
cupBlock sourcePos`; RHS `survivorTopRank V (bc + phi sourcePos) = sourcePos`
(`survivorTop_rankReadoff_ofStrictMono`); LHS the cup-alone INVOLUTION reflects the cup-alone bottom partner
`midWidth + phi sourcePos` back to `sourcePos`. -/
theorem stringCupRestrict_partner_survivorTop
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
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
  obtain ⟨embedding, cover⟩ := stringCupPositionEmbedding_imageCover bottomCount cupBlock cupPure
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock)
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length rfl
    (Nat.le_of_eq (stringProcessSpine_nextFresh_ofAllCapArity_seed bottomCount capBlock capPure).symm) cupChained
  obtain ⟨rootBelowFloor, rootAboveFloor⟩ :=
    stringValleyRootsFloorSeparated bottomCount bottomPositive capBlock cupBlock capPure cupPure
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
      stringProcessSpine_openWires_below_ofAllCapArity_seed bottomCount bottomPositive capBlock capPure
        (natListGetAt (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires index)
        (getAtMemOfLtSCBP (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires
          index indexLt)
  have isSurv : isSurvivorTop (extractDiagram bottomCount wholeState) (bottomCount + topOffset) = true := by
    show (Nat.ble bottomCount (bottomCount + topOffset)
        && Nat.blt (natListGetAt (extractDiagram bottomCount wholeState).partner (bottomCount + topOffset))
            bottomCount) = true
    have partnerRead : natListGetAt (extractDiagram bottomCount wholeState).partner (bottomCount + topOffset)
        = natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
            (bottomCount + topOffset) := by
      rw [wholeSplit]
    rw [Nat.ble_eq_true_of_le (Nat.le_add_right bottomCount topOffset), Bool.true_and, partnerRead]
    exact bltTrueOfLtSCBP survivorTopCond
  obtain ⟨sourcePos, sourceLt, phiEq⟩ :=
    (survivorTop_iff_cupImage bottomCount wholeState
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires topOffset topLt
      rootBelowFloor rootAboveFloor embedding cover survivorBelow).mp isSurv
  have midPositive : 0 < (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length :=
    Nat.lt_of_le_of_lt (Nat.zero_le sourcePos) sourceLt
  have rankReadoff : survivorTopRank (extractDiagram bottomCount wholeState)
      (bottomCount + stringCupPositionEmbedding cupBlock sourcePos) = sourcePos :=
    survivorTop_rankReadoff_ofStrictMono bottomCount wholeState
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires
      rootBelowFloor rootAboveFloor embedding cover survivorBelow sourceLt
  have cupAloneS : natListGetAt (matchingOfSpineList
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock).partner
      sourcePos
      = (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length
        + stringCupPositionEmbedding cupBlock sourcePos :=
    stringCupAlone_survivorPartner
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
          (stringCupPositionEmbedding cupBlock sourcePos)))
      (Nat.le_of_eq eq))
  have invol := stringMatchingOf_partner_isInvolution
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length midPositive
    cupBlock (spineHasCupCapAtoms_ofAllCupArity cupBlock cupPure) cupChained sourcePos
    (Nat.lt_of_lt_of_le sourceLt (Nat.le_add_right
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length
      (matchingOfSpineList
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock).topCount))
    notFixed
  rw [cupAloneS] at invol
  rw [← phiEq, invol, wholeSplit, rankReadoff]

/-! ## Concrete truth-probes — the cup-bottom leg + the cup-alone partner FIRE on the non-degenerate wide valley -/

/-- ★ **The cup-BOTTOM partner leg FIRES on the genuine non-degenerate wide valley.**  On the concrete valley
`[ε] ++ [η']` at `bottomCount = 4` (mid-width `2 > 0`, so `midPositive` genuinely holds), the cup-bottom port
`sourcePos = 0` re-ranks: the cup block's own partner equals `cupRestrict`'s reconstructed value — a real
inhabitation with non-zero mid content, NOT vacuous. -/
theorem stringCupRestrict_partner_cupBottom_firesOnWideValley :
    natListGetAt (matchingOfSpineList
        (processSpine ⟨List.range 4, [], 4, 0⟩ [stringWideProbeCapAtom]).openWires.length
        [stringWideProbeCupAtom]).partner 0
      = (processSpine ⟨List.range 4, [], 4, 0⟩ [stringWideProbeCapAtom]).openWires.length
        + (nthSurvivorTop (matchingOfSpineList 4 ([stringWideProbeCapAtom] ++ [stringWideProbeCupAtom])) 0 - 4) :=
  stringCupRestrict_partner_cupBottom 4 (by decide) [stringWideProbeCapAtom] [stringWideProbeCupAtom]
    stringWideProbeCapBlock_pureCap stringWideProbeCupBlock_pureCup stringWideProbeCupBlock_chained
    (sourcePos := 0) (by decide)

/-- ★ **The cup-ALONE bottom partner FIRES on the wide cup block at mid-width `2`.**  The cup block `[η']` run from
the from-scratch mid-width-`2` seed re-ranks bottom port `0` to `2 + stringCupPositionEmbedding [η'] 0` — the
`midPositive : 0 < 2` guard genuinely satisfied. -/
theorem stringCupAlone_survivorPartner_firesOnWideCupBlock :
    natListGetAt (matchingOfSpineList
        (processSpine ⟨List.range 4, [], 4, 0⟩ [stringWideProbeCapAtom]).openWires.length
        [stringWideProbeCupAtom]).partner 0
      = (processSpine ⟨List.range 4, [], 4, 0⟩ [stringWideProbeCapAtom]).openWires.length
        + stringCupPositionEmbedding [stringWideProbeCupAtom] 0 :=
  stringCupAlone_survivorPartner
    (processSpine ⟨List.range 4, [], 4, 0⟩ [stringWideProbeCapAtom]).openWires.length (by decide)
    [stringWideProbeCupAtom] stringWideProbeCupBlock_pureCup stringWideProbeCupBlock_chained
    (sourcePos := 0) (by decide)

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the string CUP-BOTTOM and CUP-TOP-survivor partner fields of `cupRestrict` AGREE, zero-axiom
(FC-3 r33, B5 Piece-II cup tail).**  Landed here over the walking ADJOINT-TRIPLE signature as a byte-identical
token-swap of the walking-adjunction `ValleyCupBottomPartner`, consuming the r33 keystone
(`stringCupPositionEmbedding` / `_isWireOrderEmbedding` / `_imageCover`), the r32 cup-unlinked preservation, the r29
seed floor legs, and the r31 involution:

  * `stringCupAlone_survivorPartner` — the cup-ALONE bottom partner `midWidth + stringCupPositionEmbedding cupBlock
    sourcePos`, guarded on `midPositive : 0 < midWidth`;
  * `stringCupRestrict_partner_cupBottom` — the CUP-BOTTOM agreement (both sides `= midWidth +
    stringCupPositionEmbedding cupBlock sourcePos`);
  * `stringCupRestrict_partner_survivorTop` — the CUP-TOP survivor-top agreement (both sides `= sourcePos`, via
    surjectivity + the cup-alone involution + the rank read-off).

Two truth-probes fire the cup-bottom leg + the cup-alone partner on the genuine NON-DEGENERATE WIDE valley `[ε] ++
[η']` at `bottomCount = 4` (mid-width `2 > 0`), so `midPositive` is genuinely satisfied — real inhabitations, not
vacuous.  What this marker does NOT close — the third cup partner case (`V.partner[bc + topOffset] ≥ bc`, a top-top
cup arc internal to the cup block): its multi-cup component fold over a NON-EMPTY base link list is un-shipped, so
`stringCupRestrict_reconstructs` (all three cases) stays GATED on a case-3 hypothesis.  No gate flag is flipped.
`= true`. -/
def fxString_hasCupBottomAndSurvivorTopPartner : Bool := true

end FX1Poly.Polygraph
