import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcMiddle
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStaircaseCanonical

/-! # BRAUER-MIDDLE r14 — T-ENUM E2 (the conjugator-correctness leg): the permutation-realizer roundtrip

The r13 arc-enumeration round (`Brauer/WiringDescArcEnumeration.lean`) shipped E1 (the `filterMap` read-offs list
exactly `d`'s arcs) and named E2 (conjugator-correctness) as its own r14 round, with only the four structural base
cases and four `decide`-validated width probes.  This file lands E2 in full: the general, validity-gated selection-sort
roundtrip

  `permuteOfCrossingWord width (permutationToCrossingWord width order) = order`

for every distinct, length-`width`, `[0, width)`-bounded one-line `order` (the `IsPermutationOfRange` gate).  So the
`permutationToCrossingWord` staircases genuinely realize the read-off orders — the bubble-carry (selection-sort)
induction the r13 base cases scaffolded, machine-checked zero-axiom instead of `decide`-on-four-widths.

## The proof (structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`)

  * The realizer's fold maintains a loop invariant on `currentPerm`: length `width`, distinct, the same membership set
    as `List.range width`, and its prefix `[0, position)` already equal to `order`'s.  Each bubble
    `descendingSwapPositions endIndex position` (bridged to the shipped `descendingPositions` so
    `run_bubblesFromIndex` applies) PLACES `order[position]` at index `position` and FIXES the prefix below `position`
    (all bubble positions are `≥ position`), re-establishing the invariant one step up.
  * The `position ≤ endIndex` down-carry and the last-slot closure both use `order`'s distinctness (via `natListGetAt`
    injectivity) — the load-bearing role of the gate.  The final slot is FORCED without a global pigeonhole: `order`'s
    last value is bounded, hence in `currentPerm` (whose set is `range width`), and injectivity pins its index to the
    last, so prefix agreement `[0, width-1)` upgrades to full equality.
  * The `Nat.sub` / `List.range` / `map` / membership infrastructure is re-derived `propext`-free per the zero-dep
    discipline (Lean core's `Nat.sub_sub_self`, `Nat.add_sub_cancel'`, `List.mem_range`, `List.mem_map` all leak
    `propext`); the swap-fold spine reuses the shipped `foldl_append_swap` / `run_bubblesFromIndex` /
    `swap_moves_value_down` / `memBool_applyAdjacentSwap` / `isDistinctList_applyAdjacentSwap`.

## Honest scope — this proves the E2 leg; it does NOT close #2013

The roundtrip is proven for every order satisfying the `IsPermutationOfRange` gate.  Establishing that the SPECIFIC
extractor read-off orders (`capArcFeet ++ throughStrandBottoms`, `throughStrandPerm`,
`permInverse (throughStrandTops ++ cupArcTops)`) satisfy the gate — i.e. are genuine permutations of their range — is
the T-CLOSE partition-to-permutation wiring, still deferred.  So E3 (fold-alignment) and both tag-correspondence
masters stay `false`, and #2013 does not close; the E2 marker `fxBrauer_hasArcConjugatorLeg` flips
(`Brauer/WiringDescArcEnumeration.lean`) because the conjugator-correctness selection-sort induction is now built.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Section 0 — re-derived propext-free Nat / Bool arithmetic -/

private theorem addSubCancelLeftConj : (a b : Nat) → a + b - a = b
  | 0, b => by rw [Nat.zero_add, Nat.sub_zero]
  | a + 1, b => by
      show (a + 1) + b - (a + 1) = b
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact addSubCancelLeftConj a b

private theorem addSubCancelRightConj : (a b : Nat) → a + b - b = a
  | a, 0 => rfl
  | a, b + 1 => by
      show a + (b + 1) - (b + 1) = a
      rw [Nat.add_succ, Nat.succ_sub_succ]
      exact addSubCancelRightConj a b

private theorem addSubCancelLeConj {lower upper : Nat} (le : lower ≤ upper) :
    lower + (upper - lower) = upper := by
  match Nat.le.dest le with
  | ⟨witness, witnessEq⟩ => rw [← witnessEq, addSubCancelLeftConj lower witness]

private theorem subSubSelfConj {inner outer : Nat} (le : inner ≤ outer) :
    outer - (outer - inner) = inner := by
  have recon : inner + (outer - inner) = outer := addSubCancelLeConj le
  have step : outer - (outer - inner) = (inner + (outer - inner)) - (outer - inner) := by rw [recon]
  rw [step]; exact addSubCancelRightConj inner (outer - inner)

private theorem natSubSuccEqConj : (top index : Nat) → top - 1 - index = top - (index + 1)
  | 0, index => by rw [Nat.zero_sub 1, Nat.zero_sub index, Nat.zero_sub (index + 1)]
  | top + 1, index => by rw [Nat.succ_sub_succ top index]; rfl

private theorem boolAndLeftConj : (a b : Bool) → (a && b) = true → a = true
  | true, _, _ => rfl
  | false, _, h => Bool.noConfusion h

private theorem boolAndRightConj : (a b : Bool) → (a && b) = true → b = true
  | true, _, h => h
  | false, _, h => Bool.noConfusion h

private theorem eqFalseOfNotTrueConj : (b : Bool) → (not b) = true → b = false
  | true, h => Bool.noConfusion h
  | false, _ => rfl

/-! ## Section 1 — the propext-free `Nat.beq` deciders -/

private theorem natBeqSelfConj : (n : Nat) → Nat.beq n n = true
  | 0 => rfl
  | n + 1 => natBeqSelfConj n

private theorem eqOfNatBeqTrueConj : (a b : Nat) → Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => Bool.noConfusion h
  | _ + 1, 0, h => Bool.noConfusion h
  | a + 1, b + 1, h => congrArg (· + 1) (eqOfNatBeqTrueConj a b h)

private theorem natBeqFalseOfNeConj : (a b : Nat) → a ≠ b → Nat.beq a b = false
  | 0, 0, h => absurd rfl h
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, _ => rfl
  | a + 1, b + 1, h => natBeqFalseOfNeConj a b (fun equalTail => h (congrArg (· + 1) equalTail))

private theorem eqOfBEqTrueConj {a b : Nat} (h : (a == b) = true) : a = b := of_decide_eq_true h

private theorem neOfBEqFalseConj {a b : Nat} (h : (a == b) = false) : a ≠ b := of_decide_eq_false h

/-! ## Section 2 — re-derived list positional helpers (`natListGetAt` over range / map) -/

private theorem mapLengthConj (mapFn : Nat → Nat) : (entries : List Nat) →
    (entries.map mapFn).length = entries.length
  | [] => rfl
  | _ :: rest => congrArg (· + 1) (mapLengthConj mapFn rest)

private theorem rangeLoopLengthConj : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      show (List.range.loop count (count :: accumulated)).length = (count + 1) + accumulated.length
      rw [rangeLoopLengthConj count (count :: accumulated)]
      show count + (accumulated.length + 1) = (count + 1) + accumulated.length
      rw [Nat.add_succ, Nat.succ_add]

private theorem rangeLengthConj (count : Nat) : (List.range count).length = count :=
  (rangeLoopLengthConj count []).trans (Nat.add_zero count)

private theorem getAtRangeLoopPastConj : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := getAtRangeLoopPastConj count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem getAtRangeLoopConj : (count : Nat) → (accumulated : List Nat) → (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact getAtRangeLoopConj count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_lt_succ indexBelow) atLeast
          have pastRead : natListGetAt (List.range.loop count (count :: accumulated)) (0 + count)
              = natListGetAt (count :: accumulated) 0 := getAtRangeLoopPastConj count (count :: accumulated) 0
          rw [Nat.zero_add] at pastRead
          rw [indexEq]; exact pastRead

private theorem getAtRangeConj (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  getAtRangeLoopConj count [] index indexBelow

private theorem getAtMapConj (mapFn : Nat → Nat) : (entries : List Nat) → (index : Nat) →
    index < entries.length → natListGetAt (entries.map mapFn) index = mapFn (natListGetAt entries index)
  | [], index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | _ :: _, 0, _ => rfl
  | _ :: rest, index + 1, indexBelow =>
      getAtMapConj mapFn rest index (Nat.lt_of_succ_lt_succ indexBelow)

private theorem listExtGetAtConj : (entriesLeft entriesRight : List Nat) →
    entriesLeft.length = entriesRight.length →
    (∀ index, index < entriesLeft.length → natListGetAt entriesLeft index = natListGetAt entriesRight index) →
    entriesLeft = entriesRight
  | [], [], _, _ => rfl
  | [], _ :: _, lengthsEq, _ => Nat.noConfusion lengthsEq
  | _ :: _, [], lengthsEq, _ => Nat.noConfusion lengthsEq
  | headLeft :: tailLeft, headRight :: tailRight, lengthsEq, getAtEq => by
      have headEq : headLeft = headRight := getAtEq 0 (Nat.succ_pos _)
      have tailEq : tailLeft = tailRight :=
        listExtGetAtConj tailLeft tailRight (Nat.succ.inj lengthsEq)
          (fun index indexBelow => getAtEq (index + 1) (Nat.succ_lt_succ indexBelow))
      rw [headEq, tailEq]

private theorem getAtMemConj : (entries : List Nat) → (index : Nat) → index < entries.length →
    natListGetAt entries index ∈ entries
  | [], index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | _ :: _, 0, _ => List.Mem.head _
  | head :: rest, index + 1, indexBelow =>
      List.Mem.tail head (getAtMemConj rest index (Nat.lt_of_succ_lt_succ indexBelow))

/-! ## Section 3 — boolean membership bridges -/

private theorem memBoolOfMemConj : (entries : List Nat) → (value : Nat) → value ∈ entries →
    memBool value entries = true
  | [], value, memNil => nomatch memNil
  | head :: rest, value, memCons => by
      show (Nat.beq head value || memBool value rest) = true
      cases memCons with
      | head => rw [natBeqSelfConj]; rfl
      | tail _ memRest => rw [memBoolOfMemConj rest value memRest, Bool.or_true]

private theorem memBoolFoldlSwapConj : (positions initial : List Nat) → (value : Nat) →
    memBool value (positions.foldl applyAdjacentSwap initial) = memBool value initial
  | [], _, _ => rfl
  | position :: rest, initial, value => by
      show memBool value (rest.foldl applyAdjacentSwap (applyAdjacentSwap initial position))
        = memBool value initial
      rw [memBoolFoldlSwapConj rest (applyAdjacentSwap initial position) value,
        memBool_applyAdjacentSwap value initial position]

private theorem memBoolRangeOfLtConj (width value : Nat) (valueBelow : value < width) :
    memBool value (List.range width) = true := by
  have getEq : natListGetAt (List.range width) value = value := getAtRangeConj width value valueBelow
  have indexInRange : value < (List.range width).length := by rw [rangeLengthConj]; exact valueBelow
  have entryMem : natListGetAt (List.range width) value ∈ List.range width :=
    getAtMemConj (List.range width) value indexInRange
  rw [getEq] at entryMem
  exact memBoolOfMemConj (List.range width) value entryMem

/-! ## Section 4 — `natIndexOfValue` roundtrip + `natListGetAt` injectivity -/

private theorem natIndexOfValueRoundtripConj : (perm : List Nat) → (value : Nat) → memBool value perm = true →
    natListGetAt perm (natIndexOfValue perm value) = value ∧ natIndexOfValue perm value < perm.length
  | [], value, memTrue => Bool.noConfusion memTrue
  | head :: rest, value, memTrue => by
      cases hbeq : (head == value) with
      | true =>
          have headEq : head = value := eqOfBEqTrueConj hbeq
          have indexZero : natIndexOfValue (head :: rest) value = 0 := by
            show (match head == value with | true => 0 | false => natIndexOfValue rest value + 1) = 0
            rw [hbeq]
          refine ⟨?_, ?_⟩
          · rw [indexZero]; exact headEq
          · rw [indexZero]; exact Nat.succ_pos rest.length
      | false =>
          have headNe : head ≠ value := neOfBEqFalseConj hbeq
          have beqFalse : Nat.beq head value = false := natBeqFalseOfNeConj head value headNe
          have memRest : memBool value rest = true := by
            have split : memBool value (head :: rest) = (Nat.beq head value || memBool value rest) := rfl
            rw [split, beqFalse, Bool.false_or] at memTrue; exact memTrue
          have ih := natIndexOfValueRoundtripConj rest value memRest
          have indexSucc : natIndexOfValue (head :: rest) value = natIndexOfValue rest value + 1 := by
            show (match head == value with | true => 0 | false => natIndexOfValue rest value + 1)
              = natIndexOfValue rest value + 1
            rw [hbeq]
          refine ⟨?_, ?_⟩
          · rw [indexSucc]; exact ih.1
          · rw [indexSucc]; exact Nat.succ_lt_succ ih.2

private theorem permGetAtInjectiveConj : (perm : List Nat) → isDistinctList perm = true →
    (indexLeft indexRight : Nat) → indexLeft < perm.length → indexRight < perm.length →
    natListGetAt perm indexLeft = natListGetAt perm indexRight → indexLeft = indexRight
  | [], _, _, _, leftBelow, _, _ => absurd leftBelow (Nat.not_lt_zero _)
  | head :: rest, distinct, indexLeft, indexRight, leftBelow, rightBelow, getEq => by
      have splitDist : isDistinctList (head :: rest) = (not (memBool head rest) && isDistinctList rest) := rfl
      rw [splitDist] at distinct
      have headNotMem : memBool head rest = false :=
        eqFalseOfNotTrueConj (memBool head rest) (boolAndLeftConj _ _ distinct)
      have distRest : isDistinctList rest = true := boolAndRightConj _ _ distinct
      match indexLeft, indexRight with
      | 0, 0 => rfl
      | 0, indexR + 1 =>
          have restBelow : indexR < rest.length := Nat.lt_of_succ_lt_succ rightBelow
          have headEqEntry : head = natListGetAt rest indexR := getEq
          have entryMem : natListGetAt rest indexR ∈ rest := getAtMemConj rest indexR restBelow
          have headMem : memBool head rest = true := by
            rw [headEqEntry]; exact memBoolOfMemConj rest _ entryMem
          rw [headMem] at headNotMem; exact Bool.noConfusion headNotMem
      | indexL + 1, 0 =>
          have restBelow : indexL < rest.length := Nat.lt_of_succ_lt_succ leftBelow
          have headEqEntry : head = natListGetAt rest indexL := getEq.symm
          have entryMem : natListGetAt rest indexL ∈ rest := getAtMemConj rest indexL restBelow
          have headMem : memBool head rest = true := by
            rw [headEqEntry]; exact memBoolOfMemConj rest _ entryMem
          rw [headMem] at headNotMem; exact Bool.noConfusion headNotMem
      | indexL + 1, indexR + 1 =>
          have leftRest : indexL < rest.length := Nat.lt_of_succ_lt_succ leftBelow
          have rightRest : indexR < rest.length := Nat.lt_of_succ_lt_succ rightBelow
          have restEq : natListGetAt rest indexL = natListGetAt rest indexR := getEq
          exact congrArg (· + 1)
            (permGetAtInjectiveConj rest distRest indexL indexR leftRest rightRest restEq)

/-! ## Section 5 — the descending-run bridge to `descendingPositions` -/

private theorem descendingPositionsLengthConj : (top count : Nat) → (descendingPositions top count).length = count
  | _, 0 => rfl
  | top, count + 1 =>
      congrArg (· + 1) (descendingPositionsLengthConj (top - 1) count)

private theorem getAtDescendingPositionsConj : (count top index : Nat) → index < count →
    natListGetAt (descendingPositions top count) index = top - index
  | 0, _, index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | count + 1, top, 0, _ => rfl
  | count + 1, top, index + 1, indexBelow => by
      show natListGetAt (descendingPositions (top - 1) count) index = top - (index + 1)
      rw [getAtDescendingPositionsConj count (top - 1) index (Nat.lt_of_succ_lt_succ indexBelow)]
      exact natSubSuccEqConj top index

private theorem descendingSwapPositionsBridgeConj (endIndex startIndex : Nat) :
    descendingSwapPositions endIndex startIndex
      = descendingPositions (endIndex - 1) (endIndex - startIndex) := by
  have lengthLeft : (descendingSwapPositions endIndex startIndex).length = endIndex - startIndex := by
    show ((List.range (endIndex - startIndex)).map (fun step => endIndex - 1 - step)).length = endIndex - startIndex
    rw [mapLengthConj, rangeLengthConj]
  have lengthRight : (descendingPositions (endIndex - 1) (endIndex - startIndex)).length = endIndex - startIndex :=
    descendingPositionsLengthConj (endIndex - 1) (endIndex - startIndex)
  apply listExtGetAtConj
  · rw [lengthLeft, lengthRight]
  · intro index indexBelow
    rw [lengthLeft] at indexBelow
    have leftGet : natListGetAt (descendingSwapPositions endIndex startIndex) index = endIndex - 1 - index := by
      show natListGetAt ((List.range (endIndex - startIndex)).map (fun step => endIndex - 1 - step)) index
        = endIndex - 1 - index
      rw [getAtMapConj (fun step => endIndex - 1 - step) (List.range (endIndex - startIndex)) index
        (by rw [rangeLengthConj]; exact indexBelow)]
      show endIndex - 1 - natListGetAt (List.range (endIndex - startIndex)) index = endIndex - 1 - index
      rw [getAtRangeConj (endIndex - startIndex) index indexBelow]
    rw [leftGet, getAtDescendingPositionsConj (endIndex - startIndex) (endIndex - 1) index indexBelow]

/-! ## Section 6 — a single adjacent swap / a fold of high swaps fixes low indices -/

private theorem swapFixesBelowConj : (perm : List Nat) → (pos j : Nat) → j < pos →
    natListGetAt (applyAdjacentSwap perm pos) j = natListGetAt perm j
  | [], _, _, _ => rfl
  | _ :: [], _, _, _ => rfl
  | _ :: _ :: _, 0, j, hj => absurd hj (Nat.not_lt_zero j)
  | _ :: _ :: _, _ + 1, 0, _ => rfl
  | first :: second :: rest, pos + 1, j + 1, hj => by
      show natListGetAt (applyAdjacentSwap (second :: rest) pos) j = natListGetAt (second :: rest) j
      exact swapFixesBelowConj (second :: rest) pos j (Nat.lt_of_succ_lt_succ hj)

private theorem foldlSwapFixesBelowConj : (word init : List Nat) → (bound j : Nat) →
    (∀ p, memBool p word = true → bound ≤ p) → j < bound →
    natListGetAt (word.foldl applyAdjacentSwap init) j = natListGetAt init j
  | [], _, _, _, _, _ => rfl
  | pos :: rest, init, bound, j, hall, hj => by
      show natListGetAt (rest.foldl applyAdjacentSwap (applyAdjacentSwap init pos)) j = natListGetAt init j
      have hposGe : bound ≤ pos := hall pos (by
        rw [show memBool pos (pos :: rest) = (Nat.beq pos pos || memBool pos rest) from rfl, natBeqSelfConj]; rfl)
      have hjLtPos : j < pos := Nat.lt_of_lt_of_le hj hposGe
      have hrec : natListGetAt (rest.foldl applyAdjacentSwap (applyAdjacentSwap init pos)) j
          = natListGetAt (applyAdjacentSwap init pos) j :=
        foldlSwapFixesBelowConj rest (applyAdjacentSwap init pos) bound j
          (fun p hp => hall p (by
            rw [show memBool p (pos :: rest) = (Nat.beq pos p || memBool p rest) from rfl, hp, Bool.or_true]))
          hj
      rw [hrec]
      exact swapFixesBelowConj init pos j hjLtPos

private theorem descendingPositionsMemGeConj : (count top lo : Nat) → lo + count ≤ top + 1 →
    (x : Nat) → memBool x (descendingPositions top count) = true → lo ≤ x
  | 0, _, _, _, _, hmem => Bool.noConfusion hmem
  | count + 1, top, lo, hle, x, hmem => by
      have split : memBool x (descendingPositions top (count + 1))
          = (Nat.beq top x || memBool x (descendingPositions (top - 1) count)) := rfl
      rw [split] at hmem
      have loCountLeTop : lo + count ≤ top := Nat.le_of_succ_le_succ hle
      cases hbeq : Nat.beq top x with
      | true =>
          have topEqX : top = x := eqOfNatBeqTrueConj top x hbeq
          have loLeTop : lo ≤ top := Nat.le_trans (Nat.le_add_right lo count) loCountLeTop
          rw [topEqX] at loLeTop; exact loLeTop
      | false =>
          rw [hbeq, Bool.false_or] at hmem
          have hleIH : lo + count ≤ (top - 1) + 1 :=
            Nat.le_trans loCountLeTop (Nat.le_succ_of_pred_le (Nat.le_refl (top - 1)))
          exact descendingPositionsMemGeConj count (top - 1) lo hleIH x hmem

/-! ## Section 7 — distinctness through a swap fold + the realizer-fold unfold -/

private theorem isDistinctListFoldlSwapConj : (word init : List Nat) → isDistinctList init = true →
    isDistinctList (word.foldl applyAdjacentSwap init) = true
  | [], _, hdist => hdist
  | pos :: rest, init, hdist => by
      show isDistinctList (rest.foldl applyAdjacentSwap (applyAdjacentSwap init pos)) = true
      exact isDistinctListFoldlSwapConj rest (applyAdjacentSwap init pos)
        (isDistinctList_applyAdjacentSwap init pos hdist)

private theorem permutationRealizerFoldSuccConj (order : List Nat) (fuel position : Nat) (currentPerm : List Nat) :
    permutationRealizerFold order (fuel + 1) position currentPerm
      = descendingSwapPositions (natIndexOfValue currentPerm (natListGetAt order position)) position
        ++ permutationRealizerFold order fuel (position + 1)
            ((descendingSwapPositions (natIndexOfValue currentPerm (natListGetAt order position)) position).foldl
              applyAdjacentSwap currentPerm) := rfl

/-! ## Section 8 — the validity gate + the selection-sort roundtrip induction -/

structure IsPermutationOfRange (width : Nat) (order : List Nat) : Prop where
  hasWidthLength : order.length = width
  isDistinct : isDistinctList order = true
  isBounded : ∀ index, index < width → natListGetAt order index < width

private theorem realizerFoldEvalConj (order : List Nat) (width : Nat)
    (orderLength : order.length = width)
    (orderDistinct : isDistinctList order = true)
    (orderBounded : ∀ index, index < width → natListGetAt order index < width) :
    (fuel position : Nat) → (currentPerm : List Nat) →
    position + fuel + 1 = width →
    currentPerm.length = width →
    isDistinctList currentPerm = true →
    (∀ value, memBool value currentPerm = memBool value (List.range width)) →
    (∀ j, j < position → natListGetAt currentPerm j = natListGetAt order j) →
    (permutationRealizerFold order fuel position currentPerm).foldl applyAdjacentSwap currentPerm = order
  | 0, position, currentPerm, hFuel, hLen, _, hMem, hPrefix => by
      show currentPerm = order
      have widthEq : position + 1 = width := hFuel
      refine listExtGetAtConj currentPerm order ?_ ?_
      · rw [hLen, orderLength]
      · intro j hj
        rw [hLen] at hj
        rcases Nat.lt_or_ge j position with hjLt | hjGe
        · exact hPrefix j hjLt
        · have hposLt : position < width := by rw [← widthEq]; exact Nat.lt_succ_self position
          have hvalLt : natListGetAt order position < width := orderBounded position hposLt
          have hvalMem : memBool (natListGetAt order position) currentPerm = true := by
            rw [hMem]; exact memBoolRangeOfLtConj width (natListGetAt order position) hvalLt
          have rt := natIndexOfValueRoundtripConj currentPerm (natListGetAt order position) hvalMem
          have kLtWidth : natIndexOfValue currentPerm (natListGetAt order position) < width := by
            rw [← hLen]; exact rt.2
          have kEqPos : natIndexOfValue currentPerm (natListGetAt order position) = position := by
            rcases Nat.lt_or_ge (natIndexOfValue currentPerm (natListGetAt order position)) position with hkLt | hkGe
            · exfalso
              have hpre := hPrefix (natIndexOfValue currentPerm (natListGetAt order position)) hkLt
              have hOrdEq : natListGetAt order (natIndexOfValue currentPerm (natListGetAt order position))
                  = natListGetAt order position := hpre.symm.trans rt.1
              have hinj := permGetAtInjectiveConj order orderDistinct
                (natIndexOfValue currentPerm (natListGetAt order position)) position
                (by rw [orderLength]; exact kLtWidth) (by rw [orderLength]; exact hposLt) hOrdEq
              rw [hinj] at hkLt; exact Nat.lt_irrefl position hkLt
            · refine Nat.le_antisymm (Nat.le_of_lt_succ ?_) hkGe
              show natIndexOfValue currentPerm (natListGetAt order position) < position + 1
              rw [widthEq]; exact kLtWidth
          have hjEqPos : j = position := by
            refine Nat.le_antisymm (Nat.le_of_lt_succ ?_) hjGe
            show j < position + 1; rw [widthEq]; exact hj
          rw [hjEqPos]
          have hlast := rt.1
          rw [kEqPos] at hlast
          exact hlast
  | fuel + 1, position, currentPerm, hFuel, hLen, hDist, hMem, hPrefix => by
      have hposLt : position < width := by
        rw [← hFuel]
        exact Nat.lt_of_le_of_lt (Nat.le_add_right position (fuel + 1)) (Nat.lt_succ_self _)
      have hvalLt : natListGetAt order position < width := orderBounded position hposLt
      have hvalMem : memBool (natListGetAt order position) currentPerm = true := by
        rw [hMem]; exact memBoolRangeOfLtConj width (natListGetAt order position) hvalLt
      have rt := natIndexOfValueRoundtripConj currentPerm (natListGetAt order position) hvalMem
      have kLtWidth : natIndexOfValue currentPerm (natListGetAt order position) < width := by
        rw [← hLen]; exact rt.2
      have hposLeE : position ≤ natIndexOfValue currentPerm (natListGetAt order position) := by
        rcases Nat.lt_or_ge (natIndexOfValue currentPerm (natListGetAt order position)) position with hEl | hGe
        · exfalso
          have hpre := hPrefix (natIndexOfValue currentPerm (natListGetAt order position)) hEl
          have hOrdEq : natListGetAt order (natIndexOfValue currentPerm (natListGetAt order position))
              = natListGetAt order position := hpre.symm.trans rt.1
          have hinj := permGetAtInjectiveConj order orderDistinct
            (natIndexOfValue currentPerm (natListGetAt order position)) position
            (by rw [orderLength]; exact kLtWidth) (by rw [orderLength]; exact hposLt) hOrdEq
          rw [hinj] at hEl; exact Nat.lt_irrefl position hEl
        · exact hGe
      have hbridge := descendingSwapPositionsBridgeConj (natIndexOfValue currentPerm (natListGetAt order position)) position
      have hrun := run_bubblesFromIndex (natIndexOfValue currentPerm (natListGetAt order position))
        (natIndexOfValue currentPerm (natListGetAt order position) - position) currentPerm
        (natListGetAt order position) rfl rt.2 (Nat.sub_le _ _)
      rw [← hbridge, subSubSelfConj hposLeE] at hrun
      have hvalMem2 : memBool (natListGetAt order position)
          ((descendingSwapPositions (natIndexOfValue currentPerm (natListGetAt order position)) position).foldl
            applyAdjacentSwap currentPerm) = true := by
        rw [memBoolFoldlSwapConj]; exact hvalMem
      have rt2 := natIndexOfValueRoundtripConj
        ((descendingSwapPositions (natIndexOfValue currentPerm (natListGetAt order position)) position).foldl
          applyAdjacentSwap currentPerm) (natListGetAt order position) hvalMem2
      have hplace : natListGetAt
          ((descendingSwapPositions (natIndexOfValue currentPerm (natListGetAt order position)) position).foldl
            applyAdjacentSwap currentPerm) position = natListGetAt order position := by
        have hlast := rt2.1
        rw [hrun] at hlast
        exact hlast
      have hMemGeHyp : position + (natIndexOfValue currentPerm (natListGetAt order position) - position)
          ≤ (natIndexOfValue currentPerm (natListGetAt order position) - 1) + 1 := by
        rw [addSubCancelLeConj hposLeE]; exact Nat.le_succ_of_pred_le (Nat.le_refl _)
      have hallGe : ∀ p, memBool p
          (descendingSwapPositions (natIndexOfValue currentPerm (natListGetAt order position)) position) = true
          → position ≤ p := by
        intro p hp
        exact descendingPositionsMemGeConj (natIndexOfValue currentPerm (natListGetAt order position) - position)
          (natIndexOfValue currentPerm (natListGetAt order position) - 1) position hMemGeHyp p (hbridge ▸ hp)
      rw [permutationRealizerFoldSuccConj order fuel position currentPerm, foldl_append_swap]
      refine realizerFoldEvalConj order width orderLength orderDistinct orderBounded fuel (position + 1) _
        ?_ ?_ ?_ ?_ ?_
      · have hAssoc : position + 1 + fuel = position + (fuel + 1) :=
          (Nat.add_right_comm position 1 fuel).trans (Nat.add_assoc position fuel 1)
        show position + 1 + fuel + 1 = width
        rw [hAssoc]; exact hFuel
      · rw [foldlAdjacentSwap_length]; exact hLen
      · exact isDistinctListFoldlSwapConj _ _ hDist
      · exact fun value => (memBoolFoldlSwapConj _ _ value).trans (hMem value)
      · intro j hj
        rcases Nat.lt_or_ge j position with hjLt | hjGe
        · have hfix := foldlSwapFixesBelowConj
            (descendingSwapPositions (natIndexOfValue currentPerm (natListGetAt order position)) position)
            currentPerm position j hallGe hjLt
          rw [hfix]; exact hPrefix j hjLt
        · have hjEq : j = position := Nat.le_antisymm (Nat.le_of_lt_succ hj) hjGe
          rw [hjEq]; exact hplace

/-- ★★ **THE Conj ROUNDTRIP (conjugator-correctness).**  For any distinct, length-`width`, `[0, width)`-bounded one-line
`order`, the `permutationToCrossingWord` staircase realizes it: `permuteOfCrossingWord width` inverts
`permutationToCrossingWord width`.  The selection-sort induction the r13 base cases scaffolded. -/
theorem permuteOfCrossingWord_permutationToCrossingWord (width : Nat) (order : List Nat)
    (valid : IsPermutationOfRange width order) :
    permuteOfCrossingWord width (permutationToCrossingWord width order) = order := by
  cases width with
  | zero =>
      have hlen : order.length = 0 := valid.hasWidthLength
      clear valid
      cases order with
      | nil => rfl
      | cons head tail => exact Nat.noConfusion hlen
  | succ w =>
      show (permutationRealizerFold order w 0 (List.range (w + 1))).foldl applyAdjacentSwap (List.range (w + 1))
        = order
      exact realizerFoldEvalConj order (w + 1) valid.hasWidthLength valid.isDistinct valid.isBounded
        w 0 (List.range (w + 1)) (by rw [Nat.zero_add]) (rangeLengthConj (w + 1))
        (isDistinctList_range (w + 1)) (fun _ => rfl) (fun j hj => absurd hj (Nat.not_lt_zero j))

/-! ## Section 9 — BRAUER r21 B1: the staircase POSITION-BOUND (`∀ pos ∈ staircase, pos + 2 ≤ width`)

The `WellFormedBrauerFold` crossing-phase discharge (`wellFormedBrauerFold_crossingWord`) takes exactly the window
hypothesis `∀ pos ∈ positions, pos + 2 ≤ width`.  For the corrected extractor's three crossing staircases
(`bottomPerm` / `middle` / `topPerm`) that hypothesis is the range property of `permutationToCrossingWord`: every
emitted adjacent-transposition position is `≤ endIndex - 1` for an `endIndex` that the roundtrip pins strictly below
`width`.  A fresh induction reusing the SAME loop invariants as `realizerFoldEvalConj` MINUS distinctness and prefix
agreement (the bound needs only boundedness of `order`): `currentPerm.length = width`, its membership set is
`List.range width`, and the fuel accounting `position + fuel + 1 = width`. -/

/-- The UPPER mirror of `descendingPositionsMemGeConj` — every member of a descending run is `≤ top`.  Structural on
`count`, splitting the `top :: descendingPositions (top - 1) count` cons; the recursive step relaxes `top - 1 ≤ top`
(`Nat.sub_le`). -/
private theorem descendingPositionsMemLeTopConj : (count top target : Nat) →
    memBool target (descendingPositions top count) = true → target ≤ top
  | 0, _, _, hmem => Bool.noConfusion hmem
  | count + 1, top, target, hmem => by
      have split : memBool target (descendingPositions top (count + 1))
          = (Nat.beq top target || memBool target (descendingPositions (top - 1) count)) := rfl
      rw [split] at hmem
      cases hbeq : Nat.beq top target with
      | true => exact Nat.le_of_eq (eqOfNatBeqTrueConj top target hbeq).symm
      | false =>
          rw [hbeq, Bool.false_or] at hmem
          exact Nat.le_trans (descendingPositionsMemLeTopConj count (top - 1) target hmem) (Nat.sub_le top 1)

/-- A descending run with any member is non-empty (`0 < count`) — the emptiness a `descendingSwapPositions endIndex
position` collapses to when `endIndex ≤ position`, ruled out by the mere existence of a member. -/
private theorem descendingPositionsMemPosConj : (count top target : Nat) →
    memBool target (descendingPositions top count) = true → 0 < count
  | 0, _, _, hmem => Bool.noConfusion hmem
  | count + 1, _, _, _ => Nat.succ_pos count

/-- Append membership splits — a `propext`-free `List.mem_append`, structural on the left list. -/
private theorem memAppendCasesConj : (listLeft listRight : List Nat) → (target : Nat) →
    target ∈ listLeft ++ listRight → target ∈ listLeft ∨ target ∈ listRight
  | [], _, _, mem => Or.inr mem
  | head :: rest, listRight, target, mem => by
      have memReduced : target ∈ head :: (rest ++ listRight) := mem
      cases memReduced with
      | head => exact Or.inl (List.Mem.head rest)
      | tail _ memRest =>
          cases memAppendCasesConj rest listRight target memRest with
          | inl memLeft => exact Or.inl (List.Mem.tail head memLeft)
          | inr memRight => exact Or.inr memRight

/-- The realizer-fold POSITION BOUND (the fresh induction).  Under the same loop invariants the roundtrip threads
MINUS distinctness/prefix, every emitted position of `permutationRealizerFold order fuel position currentPerm` is
`+ 2 ≤ width`.  Each bubble `descendingSwapPositions endIndex position` emits positions `≤ endIndex - 1`, and
`endIndex = natIndexOfValue currentPerm (natListGetAt order position)` is pinned `< width` by the roundtrip (the
value is bounded, hence a member of `currentPerm` whose set is `List.range width`). -/
private theorem realizerFoldPosBoundConj (order : List Nat) (width : Nat)
    (orderBounded : ∀ index, index < width → natListGetAt order index < width) :
    (fuel position : Nat) → (currentPerm : List Nat) →
    position + fuel + 1 = width →
    currentPerm.length = width →
    (∀ value, memBool value currentPerm = memBool value (List.range width)) →
    (pos : Nat) → pos ∈ permutationRealizerFold order fuel position currentPerm →
    pos + 2 ≤ width
  | 0, _position, _currentPerm, _hFuel, _hLen, _hMem, _pos, hposMem => nomatch hposMem
  | fuel + 1, position, currentPerm, hFuel, hLen, hMem, pos, hposMem => by
      rw [permutationRealizerFoldSuccConj order fuel position currentPerm] at hposMem
      cases memAppendCasesConj _ _ pos hposMem with
      | inl posInBubble =>
          have hposLt : position < width := by
            rw [← hFuel]
            exact Nat.lt_of_le_of_lt (Nat.le_add_right position (fuel + 1)) (Nat.lt_succ_self _)
          have hvalLt : natListGetAt order position < width := orderBounded position hposLt
          have hvalMem : memBool (natListGetAt order position) currentPerm = true := by
            rw [hMem]; exact memBoolRangeOfLtConj width (natListGetAt order position) hvalLt
          have rt := natIndexOfValueRoundtripConj currentPerm (natListGetAt order position) hvalMem
          have endLtWidth : natIndexOfValue currentPerm (natListGetAt order position) < width := by
            rw [← hLen]; exact rt.2
          have hbridge := descendingSwapPositionsBridgeConj
            (natIndexOfValue currentPerm (natListGetAt order position)) position
          have posBoolMem : memBool pos
              (descendingSwapPositions (natIndexOfValue currentPerm (natListGetAt order position)) position) = true :=
            memBoolOfMemConj _ pos posInBubble
          rw [hbridge] at posBoolMem
          have hxle : pos ≤ natIndexOfValue currentPerm (natListGetAt order position) - 1 :=
            descendingPositionsMemLeTopConj
              (natIndexOfValue currentPerm (natListGetAt order position) - position)
              (natIndexOfValue currentPerm (natListGetAt order position) - 1) pos posBoolMem
          have hcountpos : 0 < natIndexOfValue currentPerm (natListGetAt order position) - position :=
            descendingPositionsMemPosConj
              (natIndexOfValue currentPerm (natListGetAt order position) - position)
              (natIndexOfValue currentPerm (natListGetAt order position) - 1) pos posBoolMem
          have oneLeEnd : 1 ≤ natIndexOfValue currentPerm (natListGetAt order position) :=
            Nat.lt_of_lt_of_le hcountpos
              (Nat.sub_le (natIndexOfValue currentPerm (natListGetAt order position)) position)
          have hpred : (natIndexOfValue currentPerm (natListGetAt order position) - 1) + 1
              = natIndexOfValue currentPerm (natListGetAt order position) := by
            have hc := addSubCancelLeConj oneLeEnd
            rw [Nat.add_comm 1 (natIndexOfValue currentPerm (natListGetAt order position) - 1)] at hc
            exact hc
          have hxplus1 : pos + 1 ≤ natIndexOfValue currentPerm (natListGetAt order position) :=
            hpred ▸ Nat.add_le_add_right hxle 1
          show pos + 2 ≤ width
          exact Nat.le_trans (Nat.add_le_add_right hxplus1 1) endLtWidth
      | inr posInRest =>
          refine realizerFoldPosBoundConj order width orderBounded fuel (position + 1)
            ((descendingSwapPositions (natIndexOfValue currentPerm (natListGetAt order position)) position).foldl
              applyAdjacentSwap currentPerm) ?_ ?_ ?_ pos posInRest
          · have hAssoc : position + 1 + fuel = position + (fuel + 1) :=
              (Nat.add_right_comm position 1 fuel).trans (Nat.add_assoc position fuel 1)
            show position + 1 + fuel + 1 = width
            rw [hAssoc]; exact hFuel
          · rw [foldlAdjacentSwap_length]; exact hLen
          · exact fun value => (memBoolFoldlSwapConj _ _ value).trans (hMem value)

/-- ★ **Truth-probe (concrete conjugator outputs FIRST).**  The reversal staircase — the MAXIMAL crossing case where
the very first bubble emits `width - 2` — has every emitted position `+ 2 ≤ width` at width four; the identity
staircase (empty) and a width-4 3-cycle-shaped order confirm the bound on non-degenerate outputs.  Read straight off
the kernel, before the general lemma. -/
theorem permutationToCrossingWord_posBound_probe :
    (permutationToCrossingWord 4 [3, 2, 1, 0]).all (fun pos => decide (pos + 2 ≤ 4)) = true
      ∧ (permutationToCrossingWord 4 [2, 0, 3, 1]).all (fun pos => decide (pos + 2 ≤ 4)) = true
      ∧ (permutationToCrossingWord 3 [0, 1, 2]).all (fun pos => decide (pos + 2 ≤ 3)) = true :=
  ⟨by decide, by decide, by decide⟩

/-- ★★ **THE STAIRCASE POSITION-BOUND (BRAUER r21 B1).**  Every adjacent-transposition position the
`permutationToCrossingWord` staircase emits is `+ 2 ≤ width`, needing ONLY that `order` is `[0, width)`-bounded
(distinctness and prefix agreement are NOT used).  This is the exact window hypothesis
`wellFormedBrauerFold_crossingWord` consumes for the three crossing phases of the corrected word.  The bound is TIGHT:
the reversal's first bubble emits `width - 2` (`permutationToCrossingWord_posBound_probe`). -/
theorem permutationToCrossingWord_posBound (width : Nat) (order : List Nat)
    (orderBounded : ∀ index, index < width → natListGetAt order index < width) :
    ∀ pos, pos ∈ permutationToCrossingWord width order → pos + 2 ≤ width := by
  cases width with
  | zero =>
      intro pos hposMem
      have empty : permutationToCrossingWord 0 order = [] := rfl
      rw [empty] at hposMem
      exact nomatch hposMem
  | succ w =>
      intro pos hposMem
      exact realizerFoldPosBoundConj order (w + 1) orderBounded w 0 (List.range (w + 1))
        (by rw [Nat.zero_add]) (rangeLengthConj (w + 1)) (fun _ => rfl) pos hposMem

/-! ## Honesty marker -/

/-- ★★ **Honesty marker — the E2 conjugator-correctness roundtrip is SHIPPED (r14).**
`permuteOfCrossingWord_permutationToCrossingWord` proves, zero-axiom and structural, that the
`permutationToCrossingWord` selection-sort staircase realizes EVERY validity-gated one-line `order`
(`IsPermutationOfRange`: distinct, length-`width`, `[0, width)`-bounded) — the general form the r13 round validated
only on four concrete widths (`permutationRealizer_transposition` / `_threeCycle` / `_reversal` / `_width4`).  Feeds the
E2 marker flip `fxBrauer_hasArcConjugatorLeg` (`Brauer/WiringDescArcEnumeration.lean`).  The residual is that the
specific extractor read-off orders satisfy the gate (T-CLOSE), so the masters stay `false` and #2013 does not close.
`= true`. -/
def fxBrauer_hasConjugatorRoundtrip : Bool := true

/-- ★★ **Honesty marker — THE STAIRCASE POSITION-BOUND is SHIPPED (BRAUER r21 B1).**
`permutationToCrossingWord_posBound` proves, zero-axiom and structural, that every position the
`permutationToCrossingWord` selection-sort staircase emits satisfies `pos + 2 ≤ width` from ONLY the boundedness of
`order` (a strict weakening of the roundtrip's `IsPermutationOfRange` gate — no distinctness, no prefix agreement).
This is exactly the window hypothesis the `WellFormedBrauerFold` crossing-phase discharge
(`wellFormedBrauerFold_crossingWord`) consumes, fed for the corrected word's three crossing staircases.  The bound is
tight at the reversal's first bubble (`permutationToCrossingWord_posBound_probe`, the concrete-output truth-probe).
`= true`. -/
def fxBrauer_hasStaircasePositionBound : Bool := true

end FX1Poly.Polygraph
