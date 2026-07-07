import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCapRestrict
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyTopCountTotal
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCapConsumedFront
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingPartnerInvolution
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRangeInterleave

/-! # ValleyCapTopPartner — the cap-TOP partner field of `capRestrict` (Piece II tail, cap partner case 3)

The full `DiagramType.ext` for `capRestrict` has three partner-field cases.  This file lands the last one — the
CAP-TOP port case — via the now-shipped `matchingOf` partner INVOLUTION
(`matchingOf_partner_isInvolution`), the counting bridge (`survivorTop_rankReadoff_ofStrictMono`), and the new
`nthSurvivorTop` correctness.

For a cap-TOP port `bottomCount + rankCap` (`rankCap < midWidth`), `capRestrict` reconstructs the partner as
`V.partner[nthSurvivorTop V rankCap]`.  We prove it equals the cap block's OWN partner of `bottomCount + rankCap`.
Both sides equal the `rankCap`-th survivor bottom `survivor_r = capState.openWires[rankCap]`:

  * LHS (cap-alone): the survivor's cap-alone partner top is `bottomCount + rankCap`
    (`partnerIndexOf_survivor_eq_rank`), so the cap-alone INVOLUTION reflects `bottomCount + rankCap` back to
    `survivor_r`.
  * RHS (whole valley): `nthSurvivorTop V rankCap = bottomCount + phi rankCap` (the new correctness lemma), the
    survivor's whole-valley partner top is `bottomCount + phi rankCap`
    (`partnerIndexOf_survivorUnlinked_eq_rank`), so the whole-valley INVOLUTION reflects `bottomCount + phi rankCap`
    back to `survivor_r`.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- An in-range positional read is a member (local copy). -/
private theorem getAt_mem_of_lt : (wires : List Nat) → (index : Nat) →
    index < wires.length → natListGetAt wires index ∈ wires
  | [], _, indexInRange => absurd indexInRange (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, indexInRange =>
      List.Mem.tail _ (getAt_mem_of_lt rest index (Nat.lt_of_succ_lt_succ indexInRange))

/-! ## Local range plumbing (propext-free copies) -/

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

/-! ## Generic `firstIndexWhere`-over-range combinator -/

/-- A `firstIndexWhere` scan over `front ++ back` skips a front all of whose elements fail the predicate. -/
private theorem firstIndexWhere_append_ofFrontFails (predicate : Nat → Bool) :
    (front back : List Nat) → (fallback : Nat) →
    (∀ value, value ∈ front → predicate value = false) →
    firstIndexWhere predicate (front ++ back) fallback
      = firstIndexWhere predicate back fallback
  | [], _, _, _ => rfl
  | head :: rest, back, fallback, frontFails => by
      show (if predicate head then head else firstIndexWhere predicate (rest ++ back) fallback)
        = firstIndexWhere predicate back fallback
      cases headProbe : predicate head with
      | true =>
          exact Bool.noConfusion (headProbe.symm.trans (frontFails head (List.Mem.head rest)))
      | false =>
          show firstIndexWhere predicate (rest ++ back) fallback = firstIndexWhere predicate back fallback
          exact firstIndexWhere_append_ofFrontFails predicate rest back fallback
            (fun value valueMem => frontFails value (List.Mem.tail head valueMem))

/-- A successor range decomposes at the FRONT: `List.range (count + 1) = 0 :: (List.range count).map (1 + ·)`.
Built from the shipped `rangeSplit` at base `1` (`List.range 1 = [0]` definitionally) plus `Nat.add_comm`. -/
private theorem rangeConsZeroLocal (count : Nat) :
    List.range (count + 1) = 0 :: (List.range count).map (fun offset => 1 + offset) := by
  have split := rangeSplit 1 count
  rw [Nat.add_comm 1 count] at split
  exact split

/-- ★ **The least-passing-index over a range.**  For a predicate that passes at exactly the target `target`
(`passesTarget`) among the first `target + 1` indices (`belowFail` on all smaller), `firstIndexWhere` over
`List.range total` returns `target`.  A pure combinator: split `List.range total = List.range target ++
(target :: rest)`, drop the failing front, and pick up the passing head. -/
theorem firstIndexWhere_range_eq_of_minimal (predicate : Nat → Bool) (target total : Nat)
    (targetLt : target < total) (passesTarget : predicate target = true)
    (belowFail : ∀ smaller, smaller < target → predicate smaller = false) :
    firstIndexWhere predicate (List.range total) 0 = target := by
  obtain ⟨width, widthEq⟩ := Nat.le.dest (Nat.le_of_lt targetLt)
  -- widthEq : target + width = total, and width ≥ 1 since target < total
  cases width with
  | zero =>
      rw [Nat.add_zero] at widthEq
      exact absurd targetLt (by rw [← widthEq]; exact Nat.lt_irrefl target)
  | succ priorWidth =>
  have totalEq : total = target + (priorWidth + 1) := widthEq.symm
  have rangeDecomp : List.range total
      = List.range target ++ (0 :: (List.range priorWidth).map (fun offset => 1 + offset)).map
          (fun offset => target + offset) := by
    rw [totalEq, rangeSplit target (priorWidth + 1), rangeConsZeroLocal priorWidth]
  have headEq : (0 :: (List.range priorWidth).map (fun offset => 1 + offset)).map
        (fun offset => target + offset)
      = target :: ((List.range priorWidth).map (fun offset => 1 + offset)).map (fun offset => target + offset) := by
    show (target + 0) :: _ = target :: _
    rw [Nat.add_zero]
  rw [rangeDecomp, headEq,
    firstIndexWhere_append_ofFrontFails predicate (List.range target)
      (target :: ((List.range priorWidth).map (fun offset => 1 + offset)).map (fun offset => target + offset)) 0
      (fun value valueMem => belowFail value (mem_range_imp_lt valueMem))]
  show (if predicate target then target
      else firstIndexWhere predicate
        (((List.range priorWidth).map (fun offset => 1 + offset)).map (fun offset => target + offset)) 0)
    = target
  rw [passesTarget]
  exact if_pos rfl

/-! ## `nthSurvivorTop` correctness -/

/-- `Nat.beq n n = true` (hand-rolled; `Nat.beq_refl` / `beq_self_eq_true` leak `propext`). -/
private theorem natBeqSelf : (value : Nat) → Nat.beq value value = true
  | 0 => rfl
  | value + 1 => natBeqSelf value

/-- `Nat.beq a b = false` when `a < b` (hence `a ≠ b`). -/
private theorem natBeqFalseOfLt {smaller larger : Nat} (isLess : smaller < larger) :
    Nat.beq smaller larger = false := by
  cases probe : Nat.beq smaller larger with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true probe) (Nat.ne_of_lt isLess)

/-- ★ **`nthSurvivorTop` correctness.**  For a floor-separated final state with a strictly-monotone cup embedding
`phi` whose image is exactly the survivor-top positions, the `rankCap`-th survivor-top of `extractDiagram
bottomCount finalState` is the boundary index `bottomCount + phi rankCap`.  The scan `firstIndexWhere` returns
that index because (passing) `bottomCount + phi rankCap` is a survivor-top of rank `rankCap`
(`survivorTop_iff_cupImage` + `survivorTop_rankReadoff_ofStrictMono`), and (minimal) every smaller survivor-top
has strictly smaller rank (`survivorTopRank_strictMono_atSurvivorTop`), so fails the rank test. -/
theorem nthSurvivorTop_correct
    (bottomCount : Nat) (finalState : WireState) {phi : Nat → Nat} (midOpen : List Nat)
    (rootBelowFloor : ∀ node, node < bottomCount →
        unionFindRootOf finalState.links node < bottomCount)
    (rootAboveFloor : ∀ node, bottomCount ≤ node →
        bottomCount ≤ unionFindRootOf finalState.links node)
    (emb : WireOrderEmbedding phi midOpen finalState.openWires)
    (cover : ∀ targetPos, targetPos < finalState.openWires.length →
        (∃ sourcePos, sourcePos < midOpen.length ∧ phi sourcePos = targetPos)
          ∨ bottomCount ≤ natListGetAt finalState.openWires targetPos)
    (survivorBelow : ∀ index, index < midOpen.length → natListGetAt midOpen index < bottomCount)
    {rankCap : Nat} (rankLt : rankCap < midOpen.length) :
    nthSurvivorTop (extractDiagram bottomCount finalState) rankCap = bottomCount + phi rankCap := by
  have phiInRange : phi rankCap < finalState.openWires.length := emb.inRange rankCap rankLt
  have rankReadoff :
      survivorTopRank (extractDiagram bottomCount finalState) (bottomCount + phi rankCap) = rankCap :=
    survivorTop_rankReadoff_ofStrictMono bottomCount finalState midOpen rootBelowFloor rootAboveFloor
      emb cover survivorBelow rankLt
  have targetSurvivor :
      isSurvivorTop (extractDiagram bottomCount finalState) (bottomCount + phi rankCap) = true :=
    (survivorTop_iff_cupImage bottomCount finalState midOpen (phi rankCap) phiInRange
      rootBelowFloor rootAboveFloor emb cover survivorBelow).mpr ⟨rankCap, rankLt, rfl⟩
  refine firstIndexWhere_range_eq_of_minimal
    (fun index => isSurvivorTop (extractDiagram bottomCount finalState) index
      && Nat.beq (survivorTopRank (extractDiagram bottomCount finalState) index) rankCap)
    (bottomCount + phi rankCap) (bottomCount + finalState.openWires.length)
    (Nat.add_lt_add_left phiInRange bottomCount) ?_ ?_
  · -- passesTarget
    show (isSurvivorTop (extractDiagram bottomCount finalState) (bottomCount + phi rankCap)
        && Nat.beq (survivorTopRank (extractDiagram bottomCount finalState) (bottomCount + phi rankCap)) rankCap)
      = true
    rw [targetSurvivor, rankReadoff, natBeqSelf rankCap]
    rfl
  · -- belowFail
    intro smaller smallerLt
    show (isSurvivorTop (extractDiagram bottomCount finalState) smaller
        && Nat.beq (survivorTopRank (extractDiagram bottomCount finalState) smaller) rankCap)
      = false
    cases smallerSurvivor : isSurvivorTop (extractDiagram bottomCount finalState) smaller with
    | false => rw [Bool.false_and]
    | true =>
        have rankLtCap : survivorTopRank (extractDiagram bottomCount finalState) smaller < rankCap := by
          have strictStep := survivorTopRank_strictMono_atSurvivorTop (extractDiagram bottomCount finalState)
            smallerLt smallerSurvivor
          rw [rankReadoff] at strictStep
          exact strictStep
        rw [natBeqFalseOfLt rankLtCap, Bool.and_false]

/-! ## The append arity discipline -/

/-- A concatenation of two cup/cap-disciplined blocks is cup/cap-disciplined (`SpineHasCupCapAtoms` is a
`∀`-`Mem` predicate; `List.mem_append` split, structural on the prefix). -/
theorem spineHasCupCapAtoms_append
    {overallSource overallTarget : adjunctionGraph.Mode} :
    (first second : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    SpineHasCupCapAtoms first → SpineHasCupCapAtoms second →
    SpineHasCupCapAtoms (first ++ second)
  | [], _, _, secondArity => secondArity
  | head :: rest, second, firstArity, secondArity =>
      spineHasCupCapAtoms_cons (firstArity head (List.Mem.head rest))
        (spineHasCupCapAtoms_append rest second
          (fun atom atomMem => firstArity atom (List.Mem.tail head atomMem)) secondArity)

/-! ## The cap-TOP partner-field agreement -/

/-- ★ **The CAP-TOP partner-field agreement.**  For a cap-TOP port `bottomCount + rankCap`
(`rankCap < midWidth = capState.openWires.length`), the cap block's OWN partner equals `capRestrict`'s
reconstructed value `V.partner[nthSurvivorTop V rankCap]`, where `V = matchingOf bc (capBlock ++ cupBlock)`.
Both sides equal the `rankCap`-th survivor bottom `survivor = capState.openWires[rankCap]`:

  * the cap-alone INVOLUTION (`matchingOf_partner_isInvolution` on `capBlock`) reflects the survivor's cap-alone
    partner `bottomCount + rankCap` (`partnerIndexOf_survivor_eq_rank`) back to the survivor;
  * `nthSurvivorTop V rankCap = bottomCount + phi rankCap` (`nthSurvivorTop_correct`) and the whole-valley
    INVOLUTION (`matchingOf_partner_isInvolution` on `capBlock ++ cupBlock`) reflects the survivor's whole-valley
    partner `bottomCount + phi rankCap` (`partnerIndexOf_survivorUnlinked_eq_rank`) back to the survivor. -/
theorem capRestrict_partner_capTop
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock)
    (cupChained : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock)
    (wholeChained : SpineBoundaryChained bottomCount (capBlock ++ cupBlock))
    {rankCap : Nat}
    (rankCapLt : rankCap < (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length) :
    natListGetAt (matchingOfSpineList bottomCount capBlock).partner (bottomCount + rankCap)
      = natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
          (nthSurvivorTop (matchingOfSpineList bottomCount (capBlock ++ cupBlock)) rankCap) := by
  let capState := processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock
  let wholeState := processSpine capState cupBlock
  have capChained : SpineBoundaryChained bottomCount capBlock :=
    spineBoundaryChained_prefix_ofAppend capBlock cupBlock bottomCount wholeChained
  have wholeSplit : matchingOfSpineList bottomCount (capBlock ++ cupBlock)
      = extractDiagram bottomCount wholeState := by
    show extractDiagram bottomCount (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩
        (capBlock ++ cupBlock)) = extractDiagram bottomCount wholeState
    rw [processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩]
  -- The survivor is the `rankCap`-th cap-state open wire.
  have survivorMem : natListGetAt capState.openWires rankCap ∈ capState.openWires :=
    getAt_mem_of_lt capState.openWires rankCap rankCapLt
  have survivorBelowSelf : natListGetAt capState.openWires rankCap < bottomCount :=
    processSpine_openWires_below_ofAllCapArity_seed bottomCount bottomPositive capBlock capPure
      (natListGetAt capState.openWires rankCap) survivorMem
  have survivorUnlinkedMid : ArcNodeUnlinked capState.links (natListGetAt capState.openWires rankCap) :=
    processSpine_openWires_unlinked_ofAllCapArity_seed bottomCount capBlock capPure capChained
      (natListGetAt capState.openWires rankCap) survivorMem
  have capDistinct : WireListDistinct capState.openWires :=
    processSpine_fromSeed_wireListDistinct bottomCount bottomPositive capBlock
  have capAllUnlinked : ∀ wire ∈ capState.openWires, ArcNodeUnlinked capState.links wire :=
    processSpine_openWires_unlinked_ofAllCapArity_seed bottomCount capBlock capPure capChained
  have capNextFresh : capState.nextFresh = bottomCount :=
    processSpine_nextFresh_ofAllCapArity_seed bottomCount capBlock capPure
  -- ONE cup embedding `phi` with its value cover.
  obtain ⟨phi, embedding, cover⟩ := processSpine_wireOrderImageCover_ofAllCupArity bottomCount cupBlock cupPure
    capState capState.openWires.length rfl (Nat.le_of_eq capNextFresh.symm) cupChained
  have survivorUnlinkedWhole : ArcNodeUnlinked wholeState.links (natListGetAt capState.openWires rankCap) :=
    processSpine_preservesArcNodeUnlinked_ofAllCupArity cupBlock cupPure capState
      (natListGetAt capState.openWires rankCap) (by rw [capNextFresh]; exact survivorBelowSelf)
      survivorUnlinkedMid
  have wholeDistinct : WireListDistinct wholeState.openWires := by
    have base : WireListDistinct
        (processSpine (canonicalMatchingSeed bottomCount) (capBlock ++ cupBlock)).openWires :=
      processSpine_fromSeed_wireListDistinct bottomCount bottomPositive (capBlock ++ cupBlock)
    rw [show canonicalMatchingSeed bottomCount
          = (⟨List.range bottomCount, [], bottomCount, 0⟩ : WireState) from rfl,
      processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩] at base
    exact base
  have rankWholeLt : phi rankCap < wholeState.openWires.length := embedding.inRange rankCap rankCapLt
  have survivorAtRankWhole :
      natListGetAt wholeState.openWires (phi rankCap) = natListGetAt capState.openWires rankCap := by
    rw [embedding.reads rankCap rankCapLt]
  -- The floor-homogeneous roots N1/N2 for the whole valley.
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
  have rootBelowFloor : ∀ node, node < bottomCount → unionFindRootOf wholeState.links node < bottomCount :=
    fun node nodeBelow =>
      unionFindRootOf_lt_of_edgesBelowFloor wholeState.links bottomCount
        (fun edge edgeIn => (wholeEdgesHomog edge edgeIn).2) node nodeBelow
  have rootAboveFloor : ∀ node, bottomCount ≤ node → bottomCount ≤ unionFindRootOf wholeState.links node :=
    fun node nodeAbove =>
      unionFindRootOf_ge_of_edgesPreserveFloor wholeState.links bottomCount
        (fun edge edgeIn => (wholeEdgesHomog edge edgeIn).1) node nodeAbove
  have survivorBelowAll : ∀ index, index < capState.openWires.length →
      natListGetAt capState.openWires index < bottomCount :=
    fun index indexLt =>
      processSpine_openWires_below_ofAllCapArity_seed bottomCount bottomPositive capBlock capPure
        (natListGetAt capState.openWires index) (getAt_mem_of_lt capState.openWires index indexLt)
  -- (a) The whole-valley partner of the survivor is `bottomCount + phi rankCap`.
  have wholePartnerEq :
      natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
          (natListGetAt capState.openWires rankCap)
        = bottomCount + phi rankCap := by
    rw [wholeSplit, extractDiagram_partner_getAt bottomCount wholeState
      (natListGetAt capState.openWires rankCap)
      (Nat.lt_of_lt_of_le survivorBelowSelf (Nat.le_add_right bottomCount wholeState.openWires.length))]
    exact partnerIndexOf_survivorUnlinked_eq_rank wholeState.links bottomCount wholeState
      survivorBelowSelf survivorUnlinkedWhole wholeDistinct rankWholeLt survivorAtRankWhole
  -- (LHS) The cap-alone partner of the survivor is `bottomCount + rankCap`.
  have capPartnerEq :
      natListGetAt (matchingOfSpineList bottomCount capBlock).partner
          (natListGetAt capState.openWires rankCap)
        = bottomCount + rankCap := by
    show natListGetAt (extractDiagram bottomCount capState).partner
        (natListGetAt capState.openWires rankCap) = bottomCount + rankCap
    rw [extractDiagram_partner_getAt bottomCount capState (natListGetAt capState.openWires rankCap)
      (Nat.lt_of_lt_of_le survivorBelowSelf (Nat.le_add_right bottomCount capState.openWires.length))]
    exact partnerIndexOf_survivor_eq_rank capState.links bottomCount capState
      survivorBelowSelf survivorUnlinkedMid capDistinct capAllUnlinked rankCapLt rfl
  -- LEG A: LHS = survivor (cap-alone involution flips `bottomCount + rankCap`).
  have notFixedCap :
      natListGetAt (matchingOfSpineList bottomCount capBlock).partner
          (natListGetAt capState.openWires rankCap)
        ≠ natListGetAt capState.openWires rankCap := by
    rw [capPartnerEq]
    intro eq
    exact Nat.lt_irrefl _
      (eq ▸ Nat.lt_of_lt_of_le survivorBelowSelf (Nat.le_add_right bottomCount rankCap))
  have legA :
      natListGetAt (matchingOfSpineList bottomCount capBlock).partner (bottomCount + rankCap)
        = natListGetAt capState.openWires rankCap := by
    have invol := matchingOf_partner_isInvolution bottomCount bottomPositive capBlock
      (spineHasCupCapAtoms_ofAllCapArity capBlock capPure) capChained
      (natListGetAt capState.openWires rankCap)
      (Nat.lt_of_lt_of_le survivorBelowSelf
        (Nat.le_add_right bottomCount (matchingOfSpineList bottomCount capBlock).topCount))
      notFixedCap
    rw [capPartnerEq] at invol
    exact invol
  -- LEG B: RHS = survivor (whole-valley involution flips `bottomCount + phi rankCap`).
  have nthEq :
      nthSurvivorTop (matchingOfSpineList bottomCount (capBlock ++ cupBlock)) rankCap
        = bottomCount + phi rankCap := by
    rw [wholeSplit]
    exact nthSurvivorTop_correct bottomCount wholeState capState.openWires rootBelowFloor rootAboveFloor
      embedding cover survivorBelowAll rankCapLt
  have notFixedWhole :
      natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
          (natListGetAt capState.openWires rankCap)
        ≠ natListGetAt capState.openWires rankCap := by
    rw [wholePartnerEq]
    intro eq
    exact Nat.lt_irrefl _
      (eq ▸ Nat.lt_of_lt_of_le survivorBelowSelf (Nat.le_add_right bottomCount (phi rankCap)))
  have involWhole := matchingOf_partner_isInvolution bottomCount bottomPositive (capBlock ++ cupBlock)
    (spineHasCupCapAtoms_append capBlock cupBlock
      (spineHasCupCapAtoms_ofAllCapArity capBlock capPure)
      (spineHasCupCapAtoms_ofAllCupArity cupBlock cupPure))
    wholeChained (natListGetAt capState.openWires rankCap)
    (Nat.lt_of_lt_of_le survivorBelowSelf
      (Nat.le_add_right bottomCount (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).topCount))
    notFixedWhole
  rw [wholePartnerEq] at involWhole
  -- Close: LHS = survivor = RHS.
  rw [legA, nthEq, involWhole]

/-! ## Partner-in-range plumbing -/

/-- Every partner value of `extractDiagram bc state` at an in-range boundary index is itself in range: the
`findPartnerScan` result is either a scanned candidate (a `List.range` member, `< total`) or the in-range
exclude sentinel. -/
theorem matchingOf_partner_below (bottomCount : Nat) (state : WireState) (index : Nat)
    (inRange : index < bottomCount + state.openWires.length) :
    natListGetAt (extractDiagram bottomCount state).partner index < bottomCount + state.openWires.length := by
  rw [extractDiagram_partner_getAt bottomCount state index inRange]
  show findPartnerScan state.links (matchingBoundaryNodes bottomCount state)
      (unionFindRootOf state.links (natListGetAt (matchingBoundaryNodes bottomCount state) index))
      index (List.range (bottomCount + state.openWires.length))
    < bottomCount + state.openWires.length
  rcases findPartnerScan_result_mem_or_eq_exclude state.links (matchingBoundaryNodes bottomCount state)
      (unionFindRootOf state.links (natListGetAt (matchingBoundaryNodes bottomCount state) index)) index
      (List.range (bottomCount + state.openWires.length)) with memRange | eqExclude
  · exact mem_range_imp_lt memRange
  · rw [eqExclude]; exact inRange

/-! ## Survivor-membership routing (partner-above ⟹ survivor bottom) -/

/-- ★ **Survivor-membership routing.**  For a whole valley `capBlock ++ cupBlock` and a bottom port `index < bc`
whose whole-valley partner is a TOP (`bc ≤ V.partner[index]`), `index` is a SURVIVOR — an open wire of the
cap-block mid-state.  Proof via the shipped INVOLUTION and surjectivity: the partner top port `t = V.partner[index]`
has partner `index < bc`, so `t` is a survivor-top; `survivorTop_iff_cupImage` gives `t = bc + phi s` for a
survivor rank `s`; the survivor `survivor_s = capState.openWires[s]` has whole-valley partner `t`
(`partnerIndexOf_survivorUnlinked_eq_rank`), so the involution reflects `V.partner[t] = survivor_s = index`.
Hence `index = survivor_s ∈ capState.openWires`. -/
theorem bottomSurvivor_of_partnerAbove
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock)
    (cupChained : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock)
    (wholeChained : SpineBoundaryChained bottomCount (capBlock ++ cupBlock))
    {index : Nat} (indexBelow : index < bottomCount)
    (partnerAbove :
      bottomCount ≤ natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner index) :
    index ∈ (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires := by
  let capState := processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock
  let wholeState := processSpine capState cupBlock
  have capChained : SpineBoundaryChained bottomCount capBlock :=
    spineBoundaryChained_prefix_ofAppend capBlock cupBlock bottomCount wholeChained
  have wholeSplit : matchingOfSpineList bottomCount (capBlock ++ cupBlock)
      = extractDiagram bottomCount wholeState := by
    show extractDiagram bottomCount (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩
        (capBlock ++ cupBlock)) = extractDiagram bottomCount wholeState
    rw [processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩]
  have wholeArity : SpineHasCupCapAtoms (capBlock ++ cupBlock) :=
    spineHasCupCapAtoms_append capBlock cupBlock
      (spineHasCupCapAtoms_ofAllCapArity capBlock capPure)
      (spineHasCupCapAtoms_ofAllCupArity cupBlock cupPure)
  -- The whole-valley seed facts (mirroring the cap-TOP setup).
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
  have rootBelowFloor : ∀ node, node < bottomCount → unionFindRootOf wholeState.links node < bottomCount :=
    fun node nodeBelow =>
      unionFindRootOf_lt_of_edgesBelowFloor wholeState.links bottomCount
        (fun edge edgeIn => (wholeEdgesHomog edge edgeIn).2) node nodeBelow
  have rootAboveFloor : ∀ node, bottomCount ≤ node → bottomCount ≤ unionFindRootOf wholeState.links node :=
    fun node nodeAbove =>
      unionFindRootOf_ge_of_edgesPreserveFloor wholeState.links bottomCount
        (fun edge edgeIn => (wholeEdgesHomog edge edgeIn).1) node nodeAbove
  have survivorBelowAll : ∀ pos, pos < capState.openWires.length →
      natListGetAt capState.openWires pos < bottomCount :=
    fun pos posLt =>
      processSpine_openWires_below_ofAllCapArity_seed bottomCount bottomPositive capBlock capPure
        (natListGetAt capState.openWires pos) (getAt_mem_of_lt capState.openWires pos posLt)
  have wholeDistinct : WireListDistinct wholeState.openWires := by
    have base : WireListDistinct
        (processSpine (canonicalMatchingSeed bottomCount) (capBlock ++ cupBlock)).openWires :=
      processSpine_fromSeed_wireListDistinct bottomCount bottomPositive (capBlock ++ cupBlock)
    rw [show canonicalMatchingSeed bottomCount
          = (⟨List.range bottomCount, [], bottomCount, 0⟩ : WireState) from rfl,
      processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩] at base
    exact base
  -- `t := V.partner[index]` is a TOP in range, and the involution reflects it back to `index`.
  have partnerInRange : natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner index
      < bottomCount + wholeState.openWires.length := by
    rw [wholeSplit]
    exact matchingOf_partner_below bottomCount wholeState index
      (Nat.lt_of_lt_of_le indexBelow (Nat.le_add_right bottomCount wholeState.openWires.length))
  have notFixedIndex : natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner index
      ≠ index := by
    intro eq
    exact Nat.lt_irrefl bottomCount (Nat.lt_of_le_of_lt (eq ▸ partnerAbove) indexBelow)
  have involIndex := matchingOf_partner_isInvolution bottomCount bottomPositive (capBlock ++ cupBlock)
    wholeArity wholeChained index
    (Nat.lt_of_lt_of_le indexBelow (Nat.le_add_right bottomCount
      (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).topCount))
    notFixedIndex
  -- Write `t = bc + topOffset` and show it is a survivor-top.
  obtain ⟨topOffset, topOffsetEq⟩ := Nat.le.dest partnerAbove
  -- topOffsetEq : bottomCount + topOffset = V.partner[index]
  have topOffsetLt : topOffset < wholeState.openWires.length := by
    have := partnerInRange
    rw [← topOffsetEq] at this
    exact Nat.lt_of_add_lt_add_left this
  have partnerAtTop : natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
      (bottomCount + topOffset) = index := by
    rw [topOffsetEq]; exact involIndex
  have isSurvivorTopValue :
      isSurvivorTop (extractDiagram bottomCount wholeState) (bottomCount + topOffset) = true := by
    show (Nat.ble bottomCount (bottomCount + topOffset)
        && Nat.blt (natListGetAt (extractDiagram bottomCount wholeState).partner (bottomCount + topOffset))
            bottomCount) = true
    have partnerAtTopWhole :
        natListGetAt (extractDiagram bottomCount wholeState).partner (bottomCount + topOffset) = index := by
      rw [← wholeSplit]; exact partnerAtTop
    rw [Nat.ble_eq_true_of_le (Nat.le_add_right bottomCount topOffset), Bool.true_and, partnerAtTopWhole]
    show Nat.blt index bottomCount = true
    exact Nat.ble_eq_true_of_le indexBelow
  obtain ⟨survivorRank, survivorRankLt, phiEq⟩ :=
    (survivorTop_iff_cupImage bottomCount wholeState capState.openWires topOffset topOffsetLt
      rootBelowFloor rootAboveFloor embedding cover survivorBelowAll).mp isSurvivorTopValue
  -- The survivor at position `survivorRank` has whole-valley partner `bc + phi survivorRank = t`.
  have survivorMemS : natListGetAt capState.openWires survivorRank ∈ capState.openWires :=
    getAt_mem_of_lt capState.openWires survivorRank survivorRankLt
  have survivorBelowS : natListGetAt capState.openWires survivorRank < bottomCount :=
    survivorBelowAll survivorRank survivorRankLt
  have survivorUnlinkedMidS :
      ArcNodeUnlinked capState.links (natListGetAt capState.openWires survivorRank) :=
    processSpine_openWires_unlinked_ofAllCapArity_seed bottomCount capBlock capPure capChained
      (natListGetAt capState.openWires survivorRank) survivorMemS
  have survivorUnlinkedWholeS :
      ArcNodeUnlinked wholeState.links (natListGetAt capState.openWires survivorRank) :=
    processSpine_preservesArcNodeUnlinked_ofAllCupArity cupBlock cupPure capState
      (natListGetAt capState.openWires survivorRank) (by rw [capNextFresh]; exact survivorBelowS)
      survivorUnlinkedMidS
  have survivorAtRankWholeS :
      natListGetAt wholeState.openWires (phi survivorRank) = natListGetAt capState.openWires survivorRank := by
    rw [embedding.reads survivorRank survivorRankLt]
  have sPartnerEq : natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
      (natListGetAt capState.openWires survivorRank) = bottomCount + phi survivorRank := by
    rw [wholeSplit, extractDiagram_partner_getAt bottomCount wholeState
      (natListGetAt capState.openWires survivorRank)
      (Nat.lt_of_lt_of_le survivorBelowS (Nat.le_add_right bottomCount wholeState.openWires.length))]
    exact partnerIndexOf_survivorUnlinked_eq_rank wholeState.links bottomCount wholeState
      survivorBelowS survivorUnlinkedWholeS wholeDistinct (embedding.inRange survivorRank survivorRankLt)
      survivorAtRankWholeS
  -- Involution at the survivor reflects `t` back to `survivor_s`; but the involution at `index` also gives `t → index`.
  have notFixedS : natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
      (natListGetAt capState.openWires survivorRank) ≠ natListGetAt capState.openWires survivorRank := by
    rw [sPartnerEq]
    intro eq
    exact Nat.lt_irrefl _
      (eq ▸ Nat.lt_of_lt_of_le survivorBelowS (Nat.le_add_right bottomCount (phi survivorRank)))
  have involS := matchingOf_partner_isInvolution bottomCount bottomPositive (capBlock ++ cupBlock)
    wholeArity wholeChained (natListGetAt capState.openWires survivorRank)
    (Nat.lt_of_lt_of_le survivorBelowS (Nat.le_add_right bottomCount
      (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).topCount))
    notFixedS
  rw [sPartnerEq] at involS
  -- involS : V.partner[bc + phi survivorRank] = survivor_s ; and bc + phi survivorRank = t = bc + topOffset.
  have topCollapse : bottomCount + phi survivorRank = bottomCount + topOffset :=
    congrArg (bottomCount + ·) phiEq
  rw [topCollapse, partnerAtTop] at involS
  -- involS : index = survivor_s
  rw [involS]
  exact survivorMemS

/-! ## The cap-side reconstruction — the full `DiagramType.ext` -/

/-- Small `Nat.blt` reflection helpers (propext-free). -/
private theorem bltTrueOfLt {smaller larger : Nat} (isLess : smaller < larger) :
    Nat.blt smaller larger = true := Nat.ble_eq_true_of_le isLess

private theorem bltFalseOfGe {value bound : Nat} (isGe : bound ≤ value) :
    Nat.blt value bound = false := by
  cases probe : Nat.blt value bound with
  | false => rfl
  | true =>
      exact absurd (Nat.lt_of_lt_of_le (Nat.le_of_ble_eq_true probe) isGe) (Nat.lt_irrefl value)

private theorem neTrueOfEqFalse {flag : Bool} (isFalse : flag = false) : ¬ (flag = true) :=
  fun isTrue => Bool.noConfusion (isFalse.symm.trans isTrue)

/-- ★ **The cap-side reconstruction (F-assembly).**  The cap block's OWN diagram is `capRestrict` of the whole
valley's diagram: `matchingOf bc capBlock = capRestrict (matchingOf bc (capBlock ++ cupBlock))`.  Componentwise
via `diagramType_eq_of_fields`: `bottomCount` copies (`rfl`), `topCount` is the survivor-top total
(`survivorTopTotal_eq_midWidth`), `loops` copies (`capRestrict_loops_eq`), and the `partner` list agrees
pointwise (`natListEqOfPointwiseGetAt`) by the three shipped partner cases —
cap-consumed (`capConsumed_partner_agree`), survivor-bottom (`capRestrict_partner_survivorBottom` routed through
`bottomSurvivor_of_partnerAbove`), and cap-top (`capRestrict_partner_capTop`). -/
theorem capRestrict_reconstructs
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock)
    (cupChained : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock)
    (wholeChained : SpineBoundaryChained bottomCount (capBlock ++ cupBlock)) :
    matchingOfSpineList bottomCount capBlock
      = capRestrict (matchingOfSpineList bottomCount (capBlock ++ cupBlock)) := by
  let capState := processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock
  have capChained : SpineBoundaryChained bottomCount capBlock :=
    spineBoundaryChained_prefix_ofAppend capBlock cupBlock bottomCount wholeChained
  have wholeArity : SpineHasCupCapAtoms (capBlock ++ cupBlock) :=
    spineHasCupCapAtoms_append capBlock cupBlock
      (spineHasCupCapAtoms_ofAllCapArity capBlock capPure)
      (spineHasCupCapAtoms_ofAllCupArity cupBlock cupPure)
  have midEq : survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
      = capState.openWires.length :=
    survivorTopTotal_eq_midWidth bottomCount bottomPositive capBlock cupBlock capPure cupPure cupChained
  apply diagramType_eq_of_fields
  · -- bottomCount
    rfl
  · -- topCount : capState.openWires.length = survivorTopTotal V
    exact midEq.symm
  · -- partner : pointwise
    apply natListEqOfPointwiseGetAt
    · -- lengths
      show ((List.range (bottomCount + capState.openWires.length)).map
          (partnerIndexOf capState.links (matchingBoundaryNodes bottomCount capState)
            (bottomCount + capState.openWires.length))).length
        = ((List.range (bottomCount
            + survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock)))).map _).length
      rw [listMapLenLocal, listMapLenLocal, rangeLenLocal, rangeLenLocal, midEq]
    · -- pointwise agreement
      intro index indexRaw
      have indexLt : index < bottomCount + capState.openWires.length := by
        have lenLHS : (matchingOfSpineList bottomCount capBlock).partner.length
            = bottomCount + capState.openWires.length := by
          show ((List.range (bottomCount + capState.openWires.length)).map
              (partnerIndexOf capState.links (matchingBoundaryNodes bottomCount capState)
                (bottomCount + capState.openWires.length))).length
            = bottomCount + capState.openWires.length
          rw [listMapLenLocal, rangeLenLocal]
        rw [lenLHS] at indexRaw
        exact indexRaw
      have indexLtRHS : index < bottomCount
          + survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock)) := by
        rw [midEq]; exact indexLt
      -- read the reconstructed partner value at `index`
      have mapRead : natListGetAt
            (capRestrict (matchingOfSpineList bottomCount (capBlock ++ cupBlock))).partner index
          = (if Nat.blt index bottomCount then
              (if Nat.blt (natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner index)
                    bottomCount
                then natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner index
                else bottomCount + survivorTopRank (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
                       (natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner index))
            else natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
                   (nthSurvivorTop (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
                     (index - bottomCount))) := by
        show natListGetAt ((List.range (bottomCount
              + survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock)))).map
            (fun idx =>
              if Nat.blt idx bottomCount then
                (if Nat.blt (natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner idx)
                      bottomCount
                  then natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner idx
                  else bottomCount + survivorTopRank (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
                         (natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner idx))
              else natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
                     (nthSurvivorTop (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
                       (idx - bottomCount)))) index = _
        rw [natListGetAt_map_inRange _ _ index (by rw [rangeLenLocal]; exact indexLtRHS),
          rangeGetAtBelowLocal _ index indexLtRHS]
      rw [mapRead]
      rcases Nat.lt_or_ge index bottomCount with indexBelow | indexAtLeast
      · -- bottom port
        rw [if_pos (bltTrueOfLt indexBelow)]
        rcases Nat.lt_or_ge
            (natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner index)
            bottomCount with wpBelow | wpAbove
        · -- cap-CONSUMED bottom port
          rw [if_pos (bltTrueOfLt wpBelow)]
          have wpNe :
              natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner index ≠ index :=
            matchingOf_partner_neSelf bottomCount bottomPositive (capBlock ++ cupBlock) wholeArity
              wholeChained index
              (Nat.lt_of_lt_of_le indexBelow (Nat.le_add_right bottomCount
                (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).topCount))
          exact capConsumed_partner_agree bottomCount bottomPositive capBlock cupBlock cupPure
            indexBelow wpBelow wpNe
        · -- SURVIVOR bottom port
          rw [if_neg (neTrueOfEqFalse (bltFalseOfGe wpAbove))]
          have survivorMem : index ∈ capState.openWires :=
            bottomSurvivor_of_partnerAbove bottomCount bottomPositive capBlock cupBlock capPure cupPure
              cupChained wholeChained indexBelow wpAbove
          exact capRestrict_partner_survivorBottom bottomCount bottomPositive capBlock cupBlock capPure
            cupPure capChained cupChained survivorMem
      · -- cap-TOP port
        rw [if_neg (neTrueOfEqFalse (bltFalseOfGe indexAtLeast))]
        have idxEq : bottomCount + (index - bottomCount) = index :=
          addSubCancelLocal bottomCount index indexAtLeast
        have rLt : index - bottomCount < capState.openWires.length := by
          have step : bottomCount + (index - bottomCount) < bottomCount + capState.openWires.length := by
            rw [idxEq]; exact indexLt
          exact Nat.lt_of_add_lt_add_left step
        have capTop := capRestrict_partner_capTop bottomCount bottomPositive capBlock cupBlock capPure
          cupPure cupChained wholeChained rLt
        rw [idxEq] at capTop
        exact capTop
  · -- loops
    exact capRestrict_loops_eq bottomCount capBlock cupBlock cupPure

/-! ## The cap half of the valley-append split — derived, no longer a hypothesis -/

/-- ★ **The cap-block half of the valley-append split.**  Two valleys `capBlock ++ cupBlock` with EQUAL whole
`matchingOf` have EQUAL cap-block `matchingOf`.  Derived — not assumed — by `congrArg capRestrict` over the whole
equality, sandwiched between the two `capRestrict_reconstructs` field agreements: the cap block's own diagram is a
FUNCTION (`capRestrict`) of the whole valley's diagram, so equal wholes force equal cap blocks.  This discharges
the cap-side `capMatchEq` premise of the shipped `valleysWithBlockMatchingEq_spineTraceEquiv`. -/
theorem sameWholeMatching_capBlockMatchingEq
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlockFirst capBlockSecond cupBlockFirst cupBlockSecond :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (capPureFirst : AllCapArity capBlockFirst) (capPureSecond : AllCapArity capBlockSecond)
    (cupPureFirst : AllCupArity cupBlockFirst) (cupPureSecond : AllCupArity cupBlockSecond)
    (cupChainedFirst : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockFirst)
    (cupChainedSecond : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length cupBlockSecond)
    (wholeChainedFirst : SpineBoundaryChained bottomCount (capBlockFirst ++ cupBlockFirst))
    (wholeChainedSecond : SpineBoundaryChained bottomCount (capBlockSecond ++ cupBlockSecond))
    (wholeEq : matchingOfSpineList bottomCount (capBlockFirst ++ cupBlockFirst)
      = matchingOfSpineList bottomCount (capBlockSecond ++ cupBlockSecond)) :
    matchingOfSpineList bottomCount capBlockFirst = matchingOfSpineList bottomCount capBlockSecond :=
  (capRestrict_reconstructs bottomCount bottomPositive capBlockFirst cupBlockFirst capPureFirst cupPureFirst
      cupChainedFirst wholeChainedFirst).trans
    ((congrArg capRestrict wholeEq).trans
      (capRestrict_reconstructs bottomCount bottomPositive capBlockSecond cupBlockSecond capPureSecond
        cupPureSecond cupChainedSecond wholeChainedSecond).symm)

end FX1Poly.Polygraph
