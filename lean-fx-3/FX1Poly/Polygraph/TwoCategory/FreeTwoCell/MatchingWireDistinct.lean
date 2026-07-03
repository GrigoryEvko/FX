import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingSwapRenameable
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRightPadSeed

/-! # MatchingWireDistinct — the open-wire distinctness invariant (MODE3-D, the injectivity prerequisite)

The matching fold's open-wire list never repeats a node id.  This is the missing hypothesis for
the mid-state wire map's injectivity: `relativeWireMap` reads the wire list POSITIONALLY, so its
injectivity — and with it every `sigma`-equivariance step of the vcompRight interface gluing —
reduces to the positional distinctness of the wires it reads.

* `WireListDistinct` — the positional predicate (`getAt`-based, NOT `List.Nodup`, whose lemma set
  is membership-iff machinery; everything here stays hand-rolled like the range kit);
* out-of-range normalization — a splice at or past the end IS the splice at the end
  (`natListInsertAt_pastEnd`), a pair removal past the end IS the identity
  (`natListRemoveTwoAt_pastEnd`) — so the per-step lemmas are UNCONDITIONAL in the position and
  the fold threads no boundary discipline;
* `stepCup_wireListDistinct` / `stepCap_wireListDistinct` / `stepAtom_wireListDistinct` — the
  per-step preservation: a cup splices two fresh legs (distinct from each other by succession,
  from everything existing by `WireStateFresh`), a cap keeps a positional subsequence (no
  freshness needed), a box drops pairs then splices a pairwise-distinct fresh block;
* ★ `processSpine_wireListDistinct` + `processSpine_fromSeed_wireListDistinct` — the fold
  invariant, threaded exactly like `processSpine_wireStateFresh`, instantiated at the canonical
  seed (`List.range bottomCount` is positionally distinct).

Consumed by the relative-wire-map zone discipline (`relativeWireMap` port-image injectivity) and
through it by the vcompRight gluing legs.  Raw Lean 4 + Init; structural recursion only;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The positional distinctness predicate -/

/-- A `Nat` list is **positionally distinct** when in-range reads at two different positions
never coincide.  Positional (`natListGetAt`-based) rather than membership-based: the consumer is
the mid-state wire map, which reads positions. -/
def WireListDistinct (wires : List Nat) : Prop :=
  ∀ indexOne indexTwo : Nat, indexOne < indexTwo → indexTwo < wires.length →
    natListGetAt wires indexOne ≠ natListGetAt wires indexTwo

/-! ## Range read plumbing (private copies — the seed files' kits are file-private) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length
        = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

private theorem rangeLoopGetAt_past : (count : Nat) → (accumulated : List Nat) →
    (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count)
      = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAt_past count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAt_below : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAt_below count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAt_past count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAt_below (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAt_below count [] index indexBelow

/-! ## Nat helpers (hand-rolled; the core cancellation lemmas leak `propext`) -/

private theorem natNeOfLt {smaller larger : Nat} (strict : smaller < larger) :
    smaller ≠ larger :=
  fun wereEqual => absurd (wereEqual ▸ strict) (Nat.lt_irrefl larger)

private theorem natAddLtMonoRight : (added : Nat) → {smaller larger : Nat} →
    smaller < larger → smaller + added < larger + added
  | 0, _, _, strict => strict
  | added + 1, _, _, strict => Nat.succ_lt_succ (natAddLtMonoRight added strict)

private theorem natLtOfAddLtAddRight : (added : Nat) → {smaller larger : Nat} →
    smaller + added < larger + added → smaller < larger
  | 0, _, _, strict => strict
  | added + 1, _, _, strict => natLtOfAddLtAddRight added (Nat.lt_of_succ_lt_succ strict)

private theorem natLtOfAddLtAddLeft (base : Nat) {smaller larger : Nat}
    (strict : base + smaller < base + larger) : smaller < larger := by
  rw [Nat.add_comm base smaller, Nat.add_comm base larger] at strict
  exact natLtOfAddLtAddRight base strict

/-- An in-range positional read is a member (the range bound replaces the `0 < bound` default
threading of `natListGetAt_lt`). -/
private theorem natListGetAt_mem_inRange : (wires : List Nat) → (index : Nat) →
    index < wires.length → natListGetAt wires index ∈ wires
  | [], _, indexInRange => absurd indexInRange (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, indexInRange =>
      List.Mem.tail _ (natListGetAt_mem_inRange rest index (Nat.lt_of_succ_lt_succ indexInRange))

/-! ## Out-of-range normalization — splices clamp to the end, removals vanish -/

private theorem natListAppendNil : (wires : List Nat) → wires ++ [] = wires
  | [] => rfl
  | head :: rest => congrArg (head :: ·) (natListAppendNil rest)

/-- A splice at or past the end is the splice AT the end — the normalization that makes the
per-step distinctness lemmas unconditional in the position. -/
theorem natListInsertAt_pastEnd : (wires : List Nat) → (position : Nat) → (block : List Nat) →
    wires.length ≤ position →
    natListInsertAt wires position block = natListInsertAt wires wires.length block
  | [], 0, _, _ => rfl
  | [], _ + 1, block, _ => (natListAppendNil block).symm
  | _ :: rest, 0, _, atOrPastEnd => absurd atOrPastEnd (Nat.not_succ_le_zero rest.length)
  | head :: rest, position + 1, block, atOrPastEnd => by
      show head :: natListInsertAt rest position block
        = head :: natListInsertAt rest rest.length block
      rw [natListInsertAt_pastEnd rest position block (Nat.le_of_succ_le_succ atOrPastEnd)]

/-- A pair removal past the end removes nothing — the matcher runs out of the two elements it
needs.  (The list is split two-deep because `natListRemoveTwoAt`'s singleton arm makes its
matcher case the tail.) -/
theorem natListRemoveTwoAt_pastEnd : (wires : List Nat) → (position : Nat) →
    wires.length < position + 2 → natListRemoveTwoAt wires position = wires
  | [], _, _ => rfl
  | [_], 0, _ => rfl
  | [_], _ + 1, _ => rfl
  | _ :: _ :: rest, 0, tooShort =>
      absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ tooShort))
        (Nat.not_lt_zero rest.length)
  | first :: second :: rest, position + 1, tooShort => by
      show first :: natListRemoveTwoAt (second :: rest) position = first :: second :: rest
      rw [natListRemoveTwoAt_pastEnd (second :: rest) position (Nat.lt_of_succ_lt_succ tooShort)]

/-! ## Distinctness through an in-range fresh-block splice (the three-zone argument) -/

/-- ★ Splicing a pairwise-distinct block of ids at or above `freshBound` into a positionally
distinct list of ids below `freshBound` keeps positional distinctness.  Reads decompose by zone
(below the splice / inside the block / shifted past the block); same-zone pairs land on the
input distinctness hypotheses, cross-zone pairs separate by the bound. -/
private theorem wireListDistinct_insertFreshBlock (wires : List Nat) (position : Nat)
    (block : List Nat) (freshBound : Nat)
    (positionInRange : position ≤ wires.length)
    (wiresDistinct : WireListDistinct wires) (blockDistinct : WireListDistinct block)
    (wiresBelowBound : ∀ wire ∈ wires, wire < freshBound)
    (blockAtOrAboveBound : ∀ leg ∈ block, freshBound ≤ leg) :
    WireListDistinct (natListInsertAt wires position block) := by
  intro indexOne indexTwo oneLtTwo twoInRange
  rw [natListInsertAt_length] at twoInRange
  cases Nat.lt_or_ge indexOne position with
  | inl oneBelow =>
      have oneInWires : indexOne < wires.length := Nat.lt_of_lt_of_le oneBelow positionInRange
      have readOne := natListGetAt_natListInsertAt_below wires position block indexOne
        oneBelow oneInWires
      cases Nat.lt_or_ge indexTwo position with
      | inl twoBelow =>
          have twoInWires : indexTwo < wires.length := Nat.lt_of_lt_of_le twoBelow positionInRange
          have readTwo := natListGetAt_natListInsertAt_below wires position block indexTwo
            twoBelow twoInWires
          rw [readOne, readTwo]
          exact wiresDistinct indexOne indexTwo oneLtTwo twoInWires
      | inr twoAtOrPast =>
          obtain ⟨twoTailOffset, twoTailOffsetEq⟩ := Nat.le.dest twoAtOrPast
          cases Nat.lt_or_ge twoTailOffset block.length with
          | inl twoInside =>
              have readTwo : natListGetAt (natListInsertAt wires position block) indexTwo
                  = natListGetAt block twoTailOffset := by
                rw [← twoTailOffsetEq]
                exact natListGetAt_natListInsertAt_inside wires position block twoTailOffset
                  twoInside positionInRange
              rw [readOne, readTwo]
              have oneReadBelow : natListGetAt wires indexOne < freshBound :=
                wiresBelowBound _ (natListGetAt_mem_inRange wires indexOne oneInWires)
              have twoReadAtOrAbove : freshBound ≤ natListGetAt block twoTailOffset :=
                blockAtOrAboveBound _ (natListGetAt_mem_inRange block twoTailOffset twoInside)
              exact natNeOfLt (Nat.lt_of_lt_of_le oneReadBelow twoReadAtOrAbove)
          | inr twoPastBlock =>
              obtain ⟨twoPastOffset, twoPastOffsetEq⟩ := Nat.le.dest twoPastBlock
              have indexTwoForm : position + twoPastOffset + block.length = indexTwo := by
                rw [Nat.add_assoc position twoPastOffset block.length,
                  Nat.add_comm twoPastOffset block.length, twoPastOffsetEq, twoTailOffsetEq]
              have twoOldInWires : position + twoPastOffset < wires.length :=
                natLtOfAddLtAddRight block.length (by rw [indexTwoForm]; exact twoInRange)
              have readTwo : natListGetAt (natListInsertAt wires position block) indexTwo
                  = natListGetAt wires (position + twoPastOffset) := by
                rw [← indexTwoForm]
                exact natListGetAt_natListInsertAt_pastBlock wires position block twoPastOffset
                  positionInRange
              rw [readOne, readTwo]
              exact wiresDistinct indexOne (position + twoPastOffset)
                (Nat.lt_of_lt_of_le oneBelow (Nat.le_add_right position twoPastOffset))
                twoOldInWires
  | inr oneAtOrPast =>
      obtain ⟨oneTailOffset, oneTailOffsetEq⟩ := Nat.le.dest oneAtOrPast
      have twoAtOrPast : position ≤ indexTwo :=
        Nat.le_of_lt (Nat.lt_of_le_of_lt oneAtOrPast oneLtTwo)
      obtain ⟨twoTailOffset, twoTailOffsetEq⟩ := Nat.le.dest twoAtOrPast
      have tailsLt : oneTailOffset < twoTailOffset :=
        natLtOfAddLtAddLeft position (by rw [oneTailOffsetEq, twoTailOffsetEq]; exact oneLtTwo)
      cases Nat.lt_or_ge oneTailOffset block.length with
      | inl oneInside =>
          have readOne : natListGetAt (natListInsertAt wires position block) indexOne
              = natListGetAt block oneTailOffset := by
            rw [← oneTailOffsetEq]
            exact natListGetAt_natListInsertAt_inside wires position block oneTailOffset
              oneInside positionInRange
          cases Nat.lt_or_ge twoTailOffset block.length with
          | inl twoInside =>
              have readTwo : natListGetAt (natListInsertAt wires position block) indexTwo
                  = natListGetAt block twoTailOffset := by
                rw [← twoTailOffsetEq]
                exact natListGetAt_natListInsertAt_inside wires position block twoTailOffset
                  twoInside positionInRange
              rw [readOne, readTwo]
              exact blockDistinct oneTailOffset twoTailOffset tailsLt twoInside
          | inr twoPastBlock =>
              obtain ⟨twoPastOffset, twoPastOffsetEq⟩ := Nat.le.dest twoPastBlock
              have indexTwoForm : position + twoPastOffset + block.length = indexTwo := by
                rw [Nat.add_assoc position twoPastOffset block.length,
                  Nat.add_comm twoPastOffset block.length, twoPastOffsetEq, twoTailOffsetEq]
              have twoOldInWires : position + twoPastOffset < wires.length :=
                natLtOfAddLtAddRight block.length (by rw [indexTwoForm]; exact twoInRange)
              have readTwo : natListGetAt (natListInsertAt wires position block) indexTwo
                  = natListGetAt wires (position + twoPastOffset) := by
                rw [← indexTwoForm]
                exact natListGetAt_natListInsertAt_pastBlock wires position block twoPastOffset
                  positionInRange
              rw [readOne, readTwo]
              have twoReadBelow : natListGetAt wires (position + twoPastOffset) < freshBound :=
                wiresBelowBound _ (natListGetAt_mem_inRange wires _ twoOldInWires)
              have oneReadAtOrAbove : freshBound ≤ natListGetAt block oneTailOffset :=
                blockAtOrAboveBound _ (natListGetAt_mem_inRange block oneTailOffset oneInside)
              exact (natNeOfLt (Nat.lt_of_lt_of_le twoReadBelow oneReadAtOrAbove)).symm
      | inr onePastBlock =>
          obtain ⟨onePastOffset, onePastOffsetEq⟩ := Nat.le.dest onePastBlock
          have twoPastBlock : block.length ≤ twoTailOffset :=
            Nat.le_of_lt (Nat.lt_of_le_of_lt onePastBlock tailsLt)
          obtain ⟨twoPastOffset, twoPastOffsetEq⟩ := Nat.le.dest twoPastBlock
          have indexOneForm : position + onePastOffset + block.length = indexOne := by
            rw [Nat.add_assoc position onePastOffset block.length,
              Nat.add_comm onePastOffset block.length, onePastOffsetEq, oneTailOffsetEq]
          have indexTwoForm : position + twoPastOffset + block.length = indexTwo := by
            rw [Nat.add_assoc position twoPastOffset block.length,
              Nat.add_comm twoPastOffset block.length, twoPastOffsetEq, twoTailOffsetEq]
          have twoOldInWires : position + twoPastOffset < wires.length :=
            natLtOfAddLtAddRight block.length (by rw [indexTwoForm]; exact twoInRange)
          have pastOffsetsLt : onePastOffset < twoPastOffset :=
            natLtOfAddLtAddLeft block.length
              (by rw [onePastOffsetEq, twoPastOffsetEq]; exact tailsLt)
          have readOne : natListGetAt (natListInsertAt wires position block) indexOne
              = natListGetAt wires (position + onePastOffset) := by
            rw [← indexOneForm]
            exact natListGetAt_natListInsertAt_pastBlock wires position block onePastOffset
              positionInRange
          have readTwo : natListGetAt (natListInsertAt wires position block) indexTwo
              = natListGetAt wires (position + twoPastOffset) := by
            rw [← indexTwoForm]
            exact natListGetAt_natListInsertAt_pastBlock wires position block twoPastOffset
              positionInRange
          rw [readOne, readTwo]
          exact wiresDistinct (position + onePastOffset) (position + twoPastOffset)
            (Nat.add_lt_add_left pastOffsetsLt position) twoOldInWires

/-- The position-unconditional form — an out-of-range splice normalizes to the end splice. -/
private theorem wireListDistinct_insertFreshBlockAnyPosition (wires : List Nat) (position : Nat)
    (block : List Nat) (freshBound : Nat)
    (wiresDistinct : WireListDistinct wires) (blockDistinct : WireListDistinct block)
    (wiresBelowBound : ∀ wire ∈ wires, wire < freshBound)
    (blockAtOrAboveBound : ∀ leg ∈ block, freshBound ≤ leg) :
    WireListDistinct (natListInsertAt wires position block) := by
  cases Nat.lt_or_ge wires.length position with
  | inl pastEnd =>
      rw [natListInsertAt_pastEnd wires position block (Nat.le_of_lt pastEnd)]
      exact wireListDistinct_insertFreshBlock wires wires.length block freshBound
        (Nat.le_refl wires.length) wiresDistinct blockDistinct wiresBelowBound
        blockAtOrAboveBound
  | inr inRange =>
      exact wireListDistinct_insertFreshBlock wires position block freshBound inRange
        wiresDistinct blockDistinct wiresBelowBound blockAtOrAboveBound

/-! ## Distinctness through a pair removal (the two-zone argument, no freshness needed) -/

/-- A pair removal keeps a positional subsequence, so positional distinctness survives — at any
position (out-of-range removals vanish by `natListRemoveTwoAt_pastEnd`). -/
theorem wireListDistinct_natListRemoveTwoAt (wires : List Nat) (position : Nat)
    (wiresDistinct : WireListDistinct wires) :
    WireListDistinct (natListRemoveTwoAt wires position) := by
  cases Nat.lt_or_ge wires.length (position + 2) with
  | inl pastEnd =>
      rw [natListRemoveTwoAt_pastEnd wires position pastEnd]
      exact wiresDistinct
  | inr inRange =>
      have lengthEq := natListRemoveTwoAt_length wires position inRange
      intro indexOne indexTwo oneLtTwo twoInRange
      cases Nat.lt_or_ge indexOne position with
      | inl oneBelow =>
          have readOne := natListGetAt_natListRemoveTwoAt_below wires position indexOne oneBelow
          cases Nat.lt_or_ge indexTwo position with
          | inl twoBelow =>
              have readTwo :=
                natListGetAt_natListRemoveTwoAt_below wires position indexTwo twoBelow
              rw [readOne, readTwo]
              exact wiresDistinct indexOne indexTwo oneLtTwo
                (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le twoBelow (Nat.le_add_right position 2))
                  inRange)
          | inr twoAtOrPast =>
              obtain ⟨twoOffset, twoOffsetEq⟩ := Nat.le.dest twoAtOrPast
              have readTwo : natListGetAt (natListRemoveTwoAt wires position) indexTwo
                  = natListGetAt wires (position + twoOffset + 2) := by
                rw [← twoOffsetEq]
                exact natListGetAt_natListRemoveTwoAt_pastPair wires position twoOffset inRange
              have twoOldInWires : position + twoOffset + 2 < wires.length := by
                rw [← lengthEq]
                exact natAddLtMonoRight 2 (by rw [twoOffsetEq]; exact twoInRange)
              rw [readOne, readTwo]
              exact wiresDistinct indexOne (position + twoOffset + 2)
                (Nat.lt_of_lt_of_le oneBelow (Nat.le_add_right position (twoOffset + 2)))
                twoOldInWires
      | inr oneAtOrPast =>
          obtain ⟨oneOffset, oneOffsetEq⟩ := Nat.le.dest oneAtOrPast
          have twoAtOrPast : position ≤ indexTwo :=
            Nat.le_of_lt (Nat.lt_of_le_of_lt oneAtOrPast oneLtTwo)
          obtain ⟨twoOffset, twoOffsetEq⟩ := Nat.le.dest twoAtOrPast
          have readOne : natListGetAt (natListRemoveTwoAt wires position) indexOne
              = natListGetAt wires (position + oneOffset + 2) := by
            rw [← oneOffsetEq]
            exact natListGetAt_natListRemoveTwoAt_pastPair wires position oneOffset inRange
          have readTwo : natListGetAt (natListRemoveTwoAt wires position) indexTwo
              = natListGetAt wires (position + twoOffset + 2) := by
            rw [← twoOffsetEq]
            exact natListGetAt_natListRemoveTwoAt_pastPair wires position twoOffset inRange
          have offsetsLt : position + oneOffset + 2 < position + twoOffset + 2 :=
            natAddLtMonoRight 2
              (by rw [oneOffsetEq, twoOffsetEq]; exact oneLtTwo)
          have twoOldInWires : position + twoOffset + 2 < wires.length := by
            rw [← lengthEq]
            exact natAddLtMonoRight 2 (by rw [twoOffsetEq]; exact twoInRange)
          rw [readOne, readTwo]
          exact wiresDistinct (position + oneOffset + 2) (position + twoOffset + 2)
            offsetsLt twoOldInWires

/-! ## The per-step preservation -/

/-- The cup's two fresh legs are positionally distinct (successive ids). -/
private theorem wireListDistinct_cupLegs (leftLeg : Nat) :
    WireListDistinct [leftLeg, leftLeg + 1] := by
  intro indexOne indexTwo oneLtTwo twoInRange
  cases indexTwo with
  | zero => exact absurd oneLtTwo (Nat.not_lt_zero indexOne)
  | succ indexTwoPred =>
      cases indexTwoPred with
      | zero =>
          cases indexOne with
          | zero => exact natNeOfLt (Nat.lt_succ_self leftLeg)
          | succ indexOnePred =>
              exact absurd (Nat.lt_of_succ_lt_succ oneLtTwo) (Nat.not_lt_zero indexOnePred)
      | succ indexTwoPredPred =>
          exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ twoInRange))
            (Nat.not_lt_zero indexTwoPredPred)

/-- The box arm's fresh output block is positionally distinct (offset-shifted range reads). -/
private theorem wireListDistinct_freshBlock (freshBase count : Nat) :
    WireListDistinct ((List.range count).map (· + freshBase)) := by
  intro indexOne indexTwo oneLtTwo twoInRange
  have blockLength : ((List.range count).map (· + freshBase)).length = count := by
    rw [mapLength, rangeLength]
  rw [blockLength] at twoInRange
  have oneInCount : indexOne < count := Nat.lt_trans oneLtTwo twoInRange
  have oneInRange : indexOne < (List.range count).length := by
    rw [rangeLength]; exact oneInCount
  have twoInRangeList : indexTwo < (List.range count).length := by
    rw [rangeLength]; exact twoInRange
  rw [natListGetAt_map_inRange (· + freshBase) (List.range count) indexOne oneInRange,
    natListGetAt_map_inRange (· + freshBase) (List.range count) indexTwo twoInRangeList,
    rangeGetAt_below count indexOne oneInCount, rangeGetAt_below count indexTwo twoInRange]
  exact natNeOfLt (natAddLtMonoRight freshBase oneLtTwo)

/-- A CUP step preserves positional distinctness — the two spliced legs are successive fresh
ids, above every existing wire by `WireStateFresh`. -/
theorem stepCup_wireListDistinct (state : WireState) (position : Nat)
    (fresh : WireStateFresh state) (distinct : WireListDistinct state.openWires) :
    WireListDistinct (stepCup state position).openWires := by
  show WireListDistinct
    (natListInsertAt state.openWires position [state.nextFresh, state.nextFresh + 1])
  refine wireListDistinct_insertFreshBlockAnyPosition state.openWires position
    [state.nextFresh, state.nextFresh + 1] state.nextFresh distinct
    (wireListDistinct_cupLegs state.nextFresh) fresh.1 ?_
  intro leg legMem
  cases legMem with
  | head => exact Nat.le_refl state.nextFresh
  | tail _ legInTail =>
      cases legInTail with
      | head => exact Nat.le_succ state.nextFresh
      | tail _ legDeeper => nomatch legDeeper

/-- A CAP step preserves positional distinctness — the removal keeps a positional subsequence
(no freshness needed). -/
theorem stepCap_wireListDistinct (state : WireState) (position : Nat)
    (distinct : WireListDistinct state.openWires) :
    WireListDistinct (stepCap state position).openWires := by
  rw [stepCap_openWires]
  exact wireListDistinct_natListRemoveTwoAt state.openWires position distinct

/-- The box arm's iterated pair removal preserves positional distinctness. -/
private theorem wireListDistinct_droppedWires (position : Nat) :
    (numConsumed : Nat) → (openWires : List Nat) → WireListDistinct openWires →
    WireListDistinct
      (Nat.rec openWires (fun _ shorter => natListRemoveTwoAt shorter position) numConsumed
        : List Nat)
  | 0, _, distinct => distinct
  | numConsumed + 1, openWires, distinct =>
      wireListDistinct_natListRemoveTwoAt _ position
        (wireListDistinct_droppedWires position numConsumed openWires distinct)

/-- One matching step preserves positional distinctness — cup and cap by their lemmas, the box
arm by iterated removal then a fresh-block splice. -/
theorem stepAtom_wireListDistinct {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : WireState) (atom : SpineAtom signature sourceMode targetMode)
    (fresh : WireStateFresh state) (distinct : WireListDistinct state.openWires) :
    WireListDistinct (stepAtom state atom).openWires := by
  unfold stepAtom
  split
  · exact stepCup_wireListDistinct state _ fresh distinct
  · exact stepCap_wireListDistinct state _ distinct
  · refine wireListDistinct_insertFreshBlockAnyPosition _ atom.leftContext.length
      ((List.range atom.generatorCod.length).map (· + state.nextFresh)) state.nextFresh
      (wireListDistinct_droppedWires atom.leftContext.length atom.generatorDom.length
        state.openWires distinct)
      (wireListDistinct_freshBlock state.nextFresh atom.generatorCod.length) ?_ ?_
    · exact fun wire wireMem => fresh.1 wire
        (mem_droppedWires atom.leftContext.length atom.generatorDom.length state.openWires
          wire wireMem)
    · exact fun leg legMem =>
        mem_mapAdd_ge state.nextFresh (List.range atom.generatorCod.length) leg legMem

/-! ## The fold invariant -/

/-- ★ **The whole matching fold keeps the open-wire list positionally distinct** — structural
recursion threading `WireStateFresh` + `0 < nextFresh` exactly like
`processSpine_wireStateFresh`. -/
theorem processSpine_wireListDistinct {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : WireState) →
    WireStateFresh state → 0 < state.nextFresh → WireListDistinct state.openWires →
    WireListDistinct (processSpine state atoms).openWires
  | [], _, _, _, distinct => distinct
  | atom :: rest, state, fresh, nfPos, distinct =>
      processSpine_wireListDistinct rest (stepAtom state atom)
        (stepAtom_wireStateFresh state atom fresh nfPos)
        (Nat.lt_of_lt_of_le nfPos (stepAtom_nextFresh_le state atom))
        (stepAtom_wireListDistinct state atom fresh distinct)

/-- The canonical seed's open wires (`List.range bottomCount`) are positionally distinct. -/
theorem canonicalMatchingSeed_wireListDistinct (bottomCount : Nat) :
    WireListDistinct (canonicalMatchingSeed bottomCount).openWires := by
  show WireListDistinct (List.range bottomCount)
  intro indexOne indexTwo oneLtTwo twoInRange
  rw [rangeLength] at twoInRange
  rw [rangeGetAt_below bottomCount indexOne (Nat.lt_trans oneLtTwo twoInRange),
    rangeGetAt_below bottomCount indexTwo twoInRange]
  exact natNeOfLt oneLtTwo

/-- ★ **Every composite mid-state has positionally distinct open wires** — the fold invariant
instantiated at the canonical seed (whose `nextFresh = bottomCount` needs positivity for the
cap arm's freshness threading). -/
theorem processSpine_fromSeed_wireListDistinct {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (bottomPos : 0 < bottomCount)
    (atoms : List (SpineAtom signature sourceMode targetMode)) :
    WireListDistinct (processSpine (canonicalMatchingSeed bottomCount) atoms).openWires :=
  processSpine_wireListDistinct atoms (canonicalMatchingSeed bottomCount)
    (wireStateFresh_initial bottomCount) bottomPos
    (canonicalMatchingSeed_wireListDistinct bottomCount)

/-! ## Honesty marker -/

/-- **Honesty marker — the open-wire distinctness invariant is SHIPPED.**  Positional
(`getAt`-based) distinctness is preserved by every matching step unconditionally in the position
(out-of-range splices/removals normalized away), folds through whole spines threading only
`WireStateFresh` + `0 < nextFresh`, and holds at every mid-state reachable from the canonical
seed.  This is the injectivity prerequisite for the mid-state wire map's zone discipline —
NOT yet shipped: the zone-disciplined injection bundle itself and the gluing legs it feeds.
`= true`. -/
def fxMode_hasMatchingWireDistinctness : Bool := true

end FX1Poly.Polygraph
