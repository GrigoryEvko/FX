import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerReadback
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupSlideReadback
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScan

/-! # BRAUER-V2 r2 B2 — the crossing-only READ-OFF bridge: `StateIsPermGraph ⇒ extractDiagram = permutationDiagram`

The r4 pass proved the T2 STATE INVARIANT `stateIsPermGraph_ofInRange` (`Brauer/WiringDescBrauerReadback.lean`): after
processing an in-range crossing word, the union-find boundary same-component view IS the through-strand permutation
graph.  This file discharges the LAST node the r4 recon named — the READ-OFF that the canonical `partnerIndexOf` scan
returns exactly the permutation-forced partner — hence proves the corrected boundary-width-aware readback
`BrauerCrossingOnlyReadbackInRange` (`Brauer/WiringDescCupSlideReadback.lean`) UNCONDITIONALLY (no readback hypothesis).

## The argument

`extractDiagram bottomCount state` reads the boundary matching by, at each index, scanning `List.range (2·n)` for the
first OTHER boundary index sharing a union-find component (`partnerIndexOf` / `findPartnerScan`).  The invariant turns
"shares a component" into "carries the same through-strand" (`boundaryStrand`).  For a GENUINE permutation `perm` (a
distinct list of length `n` over `[0, n)` — `isDistinctList_permuteOfCrossingWord`), each strand value sits at EXACTLY
two boundary indices, so the matching partner is unique and equals `permPartnerAt`: the bottom port `i` (strand `i`)
partners the top port `n + perm⁻¹(i)`; the top port `n + j` (strand `perm[j]`) partners the bottom port `perm[j]`.
That is precisely the `permutationDiagram` partner list, so the two diagrams coincide field-by-field.

## What this file ships (each zero-axiom, structural)

  * the permutation-bijection facts of a `permuteOfCrossingWord` output (distinct + value-bounded + surjective +
    injective + `natIndexOfValue` roundtrip);
  * `findPartnerScan_returnsUnique` — a first-match scan with a UNIQUE satisfier returns it;
  * `partnerIndexOf_eq_permPartnerAt` — the pointwise read-off from the state invariant;
  * `extractDiagram_eq_permutationDiagram_ofPermGraph` — the field-by-field diagram equality;
  * ★ `brauerCrossingOnlyReadbackInRange_proof : BrauerCrossingOnlyReadbackInRange` — the corrected readback, PROVEN.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local `Nat` / `Bool` helpers (propext-free, self-contained) -/

/-- `Nat.beq a a = true` — structural on `a`. -/
private theorem beqSelfTrue : (value : Nat) → Nat.beq value value = true
  | 0 => rfl
  | value + 1 => beqSelfTrue value

/-- `Nat.beq a b = true → a = b` — structural on both. -/
private theorem eqOfBeqTrue : (leftValue rightValue : Nat) → Nat.beq leftValue rightValue = true →
    leftValue = rightValue
  | 0, 0, _ => rfl
  | 0, _ + 1, hbeq => Bool.noConfusion hbeq
  | _ + 1, 0, hbeq => Bool.noConfusion hbeq
  | leftPred + 1, rightPred + 1, hbeq =>
      congrArg (· + 1) (eqOfBeqTrue leftPred rightPred hbeq)

/-- `a ≠ b → Nat.beq a b = false` (contrapositive of `eqOfBeqTrue`). -/
private theorem beqFalseOfNe (leftValue rightValue : Nat) (notEqual : leftValue ≠ rightValue) :
    Nat.beq leftValue rightValue = false := by
  cases hbeq : Nat.beq leftValue rightValue with
  | true => exact absurd (eqOfBeqTrue leftValue rightValue hbeq) notEqual
  | false => rfl

/-- `a ≠ b → (a != b) = true`. -/
private theorem bneTrueOfNe (leftValue rightValue : Nat) (notEqual : leftValue ≠ rightValue) :
    (leftValue != rightValue) = true := by
  show (!(leftValue == rightValue)) = true
  cases hBeq : (leftValue == rightValue) with
  | true => exact absurd (of_decide_eq_true hBeq) notEqual
  | false => rfl

/-- `(a != b) = true → a ≠ b`. -/
private theorem neOfBneTrue (leftValue rightValue : Nat) (bneTrue : (leftValue != rightValue) = true) :
    leftValue ≠ rightValue := fun valuesEq => by
  have selfBne : (rightValue != rightValue) = false := by
    show (!(rightValue == rightValue)) = false
    have selfBeq : (rightValue == rightValue) = true := decide_eq_true rfl
    rw [selfBeq]
    rfl
  rw [valuesEq, selfBne] at bneTrue
  exact Bool.noConfusion bneTrue

/-- Conjunction from both flags. -/
private theorem andBothTrue (leftFlag rightFlag : Bool) (leftTrue : leftFlag = true)
    (rightTrue : rightFlag = true) : (leftFlag && rightFlag) = true := by
  subst leftTrue; subst rightTrue; rfl

/-- Left projection of a true conjunction. -/
private theorem andLeftTrue (leftFlag rightFlag : Bool) (bothTrue : (leftFlag && rightFlag) = true) :
    leftFlag = true := by
  cases leftFlag with
  | true => rfl
  | false => exact Bool.noConfusion bothTrue

/-- Right projection of a true conjunction. -/
private theorem andRightTrue (leftFlag rightFlag : Bool) (bothTrue : (leftFlag && rightFlag) = true) :
    rightFlag = true := by
  cases leftFlag with
  | true => exact bothTrue
  | false => exact Bool.noConfusion bothTrue

/-- `decide (a = b) = true → a = b` for `Nat` (via the structural `Nat.decEq`). -/
private theorem eqOfDecideNatTrue (leftValue rightValue : Nat)
    (decideTrue : decide (leftValue = rightValue) = true) : leftValue = rightValue :=
  of_decide_eq_true decideTrue

/-- `a = b → decide (a = b) = true`. -/
private theorem decideNatTrueOfEq (leftValue rightValue : Nat) (equal : leftValue = rightValue) :
    decide (leftValue = rightValue) = true :=
  decide_eq_true equal

/-! ## `List.range` membership (both directions, structural on the loop) -/

/-- Any accumulator member is a `range.loop` member (the accumulator survives the fold). -/
private theorem memRangeLoop_ofMemAcc : (count : Nat) → (accumulated : List Nat) → (value : Nat) →
    value ∈ accumulated → value ∈ List.range.loop count accumulated
  | 0, _, _, memAcc => memAcc
  | count + 1, accumulated, value, memAcc =>
      memRangeLoop_ofMemAcc count (count :: accumulated) value (List.Mem.tail count memAcc)

/-- Every index below `count` is a `range.loop count` member. -/
private theorem memRangeLoop_ofLt : (count : Nat) → (accumulated : List Nat) → (value : Nat) →
    value < count → value ∈ List.range.loop count accumulated
  | 0, _, value, valueBelow => absurd valueBelow (Nat.not_lt_zero value)
  | count + 1, accumulated, value, valueBelow => by
      cases Nat.lt_or_ge value count with
      | inl below => exact memRangeLoop_ofLt count (count :: accumulated) value below
      | inr atLeast =>
          have valueEq : value = count := Nat.le_antisymm (Nat.le_of_lt_succ valueBelow) atLeast
          rw [valueEq]
          exact memRangeLoop_ofMemAcc count (count :: accumulated) count (List.Mem.head accumulated)

/-- A `range.loop count` member is below `count` or was in the accumulator. -/
private theorem ltOrMemAcc_ofMemRangeLoop : (count : Nat) → (accumulated : List Nat) → (value : Nat) →
    value ∈ List.range.loop count accumulated → value < count ∨ value ∈ accumulated
  | 0, _, _, memLoop => Or.inr memLoop
  | count + 1, accumulated, value, memLoop => by
      rcases ltOrMemAcc_ofMemRangeLoop count (count :: accumulated) value memLoop with below | memCons
      · exact Or.inl (Nat.lt_succ_of_lt below)
      · cases memCons with
        | head => exact Or.inl (Nat.lt_succ_self count)
        | tail _ memRest => exact Or.inr memRest

/-- `k < n → k ∈ List.range n`. -/
private theorem memRange_ofLt (bound value : Nat) (valueBelow : value < bound) :
    value ∈ List.range bound :=
  memRangeLoop_ofLt bound [] value valueBelow

/-- `k ∈ List.range n → k < n`. -/
private theorem lt_ofMemRange (bound value : Nat) (memRange : value ∈ List.range bound) :
    value < bound := by
  rcases ltOrMemAcc_ofMemRangeLoop bound [] value memRange with below | memNil
  · exact below
  · nomatch memNil

/-! ## Propext-free `Nat` / `List` arithmetic helpers (zero-axiom local copies) -/

/-- `a + b - a = b` — structural on `a`, propext-free (avoids the axiom-leaking `addSubCancelLeftLocal`). -/
private theorem addSubCancelLeftLocal : (a b : Nat) → a + b - a = b
  | 0, b => Nat.zero_add b
  | a + 1, b => by
      show (a + 1) + b - (a + 1) = b
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact addSubCancelLeftLocal a b

/-- `n ≤ m → n + (m - n) = m` — via `Nat.le.dest`, propext-free (replaces `addSubSelfLocal`). -/
private theorem addSubSelfLocal {lowerBound upperBound : Nat} (le : lowerBound ≤ upperBound) :
    lowerBound + (upperBound - lowerBound) = upperBound := by
  have dest := Nat.le.dest le
  match dest with
  | ⟨witness, witnessEq⟩ => rw [← witnessEq, addSubCancelLeftLocal lowerBound witness]

/-- `k ≤ m → m < n → m - k < n - k` — via `Nat.le.dest`, propext-free (replaces `subLtSubRightLocal`). -/
private theorem subLtSubRightLocal {subtractand lower upper : Nat} (le : subtractand ≤ lower)
    (lt : lower < upper) : lower - subtractand < upper - subtractand := by
  have leUpper : subtractand ≤ upper := Nat.le_of_lt (Nat.lt_of_le_of_lt le lt)
  have destLower := Nat.le.dest le
  have destUpper := Nat.le.dest leUpper
  match destLower, destUpper with
  | ⟨lowerWitness, lowerEq⟩, ⟨upperWitness, upperEq⟩ =>
      rw [← lowerEq, ← upperEq, addSubCancelLeftLocal subtractand lowerWitness,
        addSubCancelLeftLocal subtractand upperWitness]
      rw [← lowerEq, ← upperEq] at lt
      exact Nat.lt_of_add_lt_add_left lt

/-- `(l1 ++ l2).length = l1.length + l2.length` — structural, propext-free (replaces `listLengthAppendLocal`). -/
private theorem listLengthAppendLocal : (leftList rightList : List Nat) →
    (leftList ++ rightList).length = leftList.length + rightList.length
  | [], rightList => (Nat.zero_add rightList.length).symm
  | _ :: tailLeft, rightList => by
      show (tailLeft ++ rightList).length + 1 = (tailLeft.length + 1) + rightList.length
      rw [listLengthAppendLocal tailLeft rightList, Nat.succ_add]

/-- `(List.range.loop count acc).length = count + acc.length` — structural, propext-free. -/
private theorem rangeLoopLengthLocal : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      show (List.range.loop count (count :: accumulated)).length = (count + 1) + accumulated.length
      rw [rangeLoopLengthLocal count (count :: accumulated)]
      show count + (accumulated.length + 1) = (count + 1) + accumulated.length
      rw [Nat.add_succ, Nat.succ_add]

/-! ## `natListGetAt` over append / range / map (propext-free local copies) -/

/-- `natListGetAt` on the left of an append below the left length. -/
private theorem getAt_appendLeft : (leftList rightList : List Nat) → (index : Nat) →
    index < leftList.length → natListGetAt (leftList ++ rightList) index = natListGetAt leftList index
  | [], _, index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | _ :: _, _, 0, _ => rfl
  | _ :: restLeft, rightList, index + 1, indexBelow =>
      getAt_appendLeft restLeft rightList index (Nat.lt_of_succ_lt_succ indexBelow)

/-- `natListGetAt` on the right of an append at a shifted index. -/
private theorem getAt_appendRight : (leftList rightList : List Nat) → (index : Nat) →
    natListGetAt (leftList ++ rightList) (leftList.length + index) = natListGetAt rightList index
  | [], rightList, index => by
      show natListGetAt rightList (0 + index) = natListGetAt rightList index
      rw [Nat.zero_add]
  | headLeft :: restLeft, rightList, index => by
      show natListGetAt (headLeft :: (restLeft ++ rightList)) (restLeft.length + 1 + index)
        = natListGetAt rightList index
      rw [Nat.add_right_comm restLeft.length 1 index]
      show natListGetAt (restLeft ++ rightList) (restLeft.length + index) = natListGetAt rightList index
      exact getAt_appendRight restLeft rightList index

/-- Reading `List.range count` below its length returns the index. -/
private theorem getAt_range : (count : Nat) → (accumulated : List Nat) → (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact getAt_range count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_lt_succ indexBelow) atLeast
          have pastRead : natListGetAt (List.range.loop count (count :: accumulated)) (0 + count)
              = natListGetAt (count :: accumulated) 0 := getAt_rangePast count (count :: accumulated) 0
          rw [Nat.zero_add] at pastRead
          rw [indexEq]; exact pastRead
where
  /-- Reading `range.loop` past its front drops into the accumulator. -/
  getAt_rangePast : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
      natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
    | 0, _, _ => rfl
    | count + 1, accumulated, offset => by
        have inner := getAt_rangePast count (count :: accumulated) (offset + 1)
        rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
        exact inner

/-- `natListGetAt (List.range count) index = index` for `index < count`. -/
private theorem getAt_rangeTop (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  getAt_range count [] index indexBelow

/-- `natListGetAt` through a `List.map` at an in-range index. -/
private theorem getAt_map (mapFn : Nat → Nat) : (entries : List Nat) → (index : Nat) →
    index < entries.length → natListGetAt (entries.map mapFn) index = mapFn (natListGetAt entries index)
  | [], index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | _ :: _, 0, _ => rfl
  | _ :: rest, index + 1, indexBelow =>
      getAt_map mapFn rest index (Nat.lt_of_succ_lt_succ indexBelow)

/-- `(entries.map mapFn).length = entries.length`. -/
private theorem map_length (mapFn : Nat → Nat) : (entries : List Nat) →
    (entries.map mapFn).length = entries.length
  | [] => rfl
  | _ :: rest => congrArg (· + 1) (map_length mapFn rest)

/-- `List.range count` has length `count` — propext-free via `rangeLoopLengthLocal`. -/
private theorem range_length (count : Nat) : (List.range count).length = count :=
  (rangeLoopLengthLocal count []).trans (Nat.add_zero count)

/-- Extensionality for `Nat` lists by `natListGetAt` at equal length. -/
private theorem listExtGetAt : (entriesLeft entriesRight : List Nat) →
    entriesLeft.length = entriesRight.length →
    (∀ index, index < entriesLeft.length → natListGetAt entriesLeft index = natListGetAt entriesRight index) →
    entriesLeft = entriesRight
  | [], [], _, _ => rfl
  | [], _ :: _, lengthsEq, _ => Nat.noConfusion lengthsEq
  | _ :: _, [], lengthsEq, _ => Nat.noConfusion lengthsEq
  | headLeft :: tailLeft, headRight :: tailRight, lengthsEq, getAtEq => by
      have headEq : headLeft = headRight := getAtEq 0 (Nat.succ_pos _)
      have tailEq : tailLeft = tailRight :=
        listExtGetAt tailLeft tailRight (Nat.succ.inj lengthsEq)
          (fun index indexBelow => getAtEq (index + 1) (Nat.succ_lt_succ indexBelow))
      rw [headEq, tailEq]

/-! ## Boolean membership bridges (`memBool ↔ List.Mem`) -/

/-- `memBool value entries = true → value ∈ entries`. -/
private theorem mem_ofMemBool : (entries : List Nat) → (value : Nat) → memBool value entries = true →
    value ∈ entries
  | [], value, memTrue => Bool.noConfusion memTrue
  | head :: rest, value, memTrue => by
      have split : memBool value (head :: rest) = (Nat.beq head value || memBool value rest) := rfl
      rw [split] at memTrue
      cases hhead : Nat.beq head value with
      | true => rw [eqOfBeqTrue head value hhead]; exact List.Mem.head rest
      | false =>
          rw [hhead, Bool.false_or] at memTrue
          exact List.Mem.tail head (mem_ofMemBool rest value memTrue)

/-- `value ∈ entries → memBool value entries = true`. -/
private theorem memBool_ofMem : (entries : List Nat) → (value : Nat) → value ∈ entries →
    memBool value entries = true
  | [], value, memNil => nomatch memNil
  | head :: rest, value, memCons => by
      show (Nat.beq head value || memBool value rest) = true
      cases memCons with
      | head => rw [beqSelfTrue head, Bool.true_or]
      | tail _ memRest => rw [memBool_ofMem rest value memRest, Bool.or_true]

/-- `natListGetAt entries index ∈ entries` for `index < entries.length`. -/
private theorem getAt_mem : (entries : List Nat) → (index : Nat) → index < entries.length →
    natListGetAt entries index ∈ entries
  | [], index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | head :: _, 0, _ => List.Mem.head _
  | head :: rest, index + 1, indexBelow =>
      List.Mem.tail head (getAt_mem rest index (Nat.lt_of_succ_lt_succ indexBelow))

/-! ## The permutation-bijection facts of a `permuteOfCrossingWord` output -/

/-- Membership is invariant across the whole adjacent-swap fold. -/
private theorem memBool_foldlSwap : (positions initial : List Nat) → (value : Nat) →
    memBool value (positions.foldl applyAdjacentSwap initial) = memBool value initial
  | [], _, _ => rfl
  | position :: rest, initial, value => by
      show memBool value (rest.foldl applyAdjacentSwap (applyAdjacentSwap initial position))
        = memBool value initial
      rw [memBool_foldlSwap rest (applyAdjacentSwap initial position) value,
        memBool_applyAdjacentSwap value initial position]

/-- The realized permutation carries exactly the identity's membership set. -/
private theorem memBool_permuteOfCrossingWord (bottomCount : Nat) (positions : List Nat) (value : Nat) :
    memBool value (permuteOfCrossingWord bottomCount positions) = memBool value (List.range bottomCount) :=
  memBool_foldlSwap positions (List.range bottomCount) value

/-- Every value below `bottomCount` occurs in the realized permutation (surjectivity). -/
private theorem perm_mem_ofLt (bottomCount : Nat) (positions : List Nat) (value : Nat)
    (valueBelow : value < bottomCount) :
    memBool value (permuteOfCrossingWord bottomCount positions) = true := by
  rw [memBool_permuteOfCrossingWord bottomCount positions value]
  exact memBool_ofMem (List.range bottomCount) value (memRange_ofLt bottomCount value valueBelow)

/-- Every entry of the realized permutation is below `bottomCount` (value bound). -/
private theorem perm_getAt_lt (bottomCount : Nat) (positions : List Nat) (index : Nat)
    (indexBelow : index < bottomCount) :
    natListGetAt (permuteOfCrossingWord bottomCount positions) index < bottomCount := by
  have lengthEq : (permuteOfCrossingWord bottomCount positions).length = bottomCount :=
    permuteOfCrossingWord_length bottomCount positions
  have indexInRange : index < (permuteOfCrossingWord bottomCount positions).length := by
    rw [lengthEq]; exact indexBelow
  have entryMem : natListGetAt (permuteOfCrossingWord bottomCount positions) index
      ∈ permuteOfCrossingWord bottomCount positions :=
    getAt_mem (permuteOfCrossingWord bottomCount positions) index indexInRange
  have memBoolTrue : memBool (natListGetAt (permuteOfCrossingWord bottomCount positions) index)
      (permuteOfCrossingWord bottomCount positions) = true :=
    memBool_ofMem _ _ entryMem
  rw [memBool_permuteOfCrossingWord bottomCount positions] at memBoolTrue
  exact lt_ofMemRange bottomCount _ (mem_ofMemBool (List.range bottomCount) _ memBoolTrue)

/-- `natIndexOfValue` roundtrip: on an occurring value it returns an in-range index reading back the value. -/
private theorem natIndexOfValue_roundtrip : (perm : List Nat) → (value : Nat) → memBool value perm = true →
    natListGetAt perm (natIndexOfValue perm value) = value ∧ natIndexOfValue perm value < perm.length
  | [], value, memTrue => Bool.noConfusion memTrue
  | head :: rest, value, memTrue => by
      cases hbeq : (head == value) with
      | true =>
          have headEq : head = value := of_decide_eq_true hbeq
          have indexZero : natIndexOfValue (head :: rest) value = 0 := by
            show (match head == value with | true => 0 | false => natIndexOfValue rest value + 1) = 0
            rw [hbeq]
          refine ⟨?_, ?_⟩
          · rw [indexZero]; exact headEq
          · rw [indexZero]; exact Nat.succ_pos rest.length
      | false =>
          have headNe : head ≠ value := fun headEq => by
            have selfTrue : (value == value) = true := decideNatTrueOfEq value value rfl
            rw [headEq, selfTrue] at hbeq
            exact Bool.noConfusion hbeq
          have memRest : memBool value rest = true := by
            have split : memBool value (head :: rest) = (Nat.beq head value || memBool value rest) := rfl
            have beqFalse : Nat.beq head value = false := beqFalseOfNe head value headNe
            rw [split, beqFalse, Bool.false_or] at memTrue; exact memTrue
          have ih := natIndexOfValue_roundtrip rest value memRest
          have indexSucc : natIndexOfValue (head :: rest) value = natIndexOfValue rest value + 1 := by
            show (match head == value with | true => 0 | false => natIndexOfValue rest value + 1)
              = natIndexOfValue rest value + 1
            rw [hbeq]
          refine ⟨?_, ?_⟩
          · rw [indexSucc]; exact ih.1
          · rw [indexSucc]; exact Nat.succ_lt_succ ih.2

/-- Distinctness makes `natListGetAt` injective on `[0, length)`. -/
private theorem perm_getAt_injective : (perm : List Nat) → isDistinctList perm = true →
    (indexLeft indexRight : Nat) → indexLeft < perm.length → indexRight < perm.length →
    natListGetAt perm indexLeft = natListGetAt perm indexRight → indexLeft = indexRight
  | [], _, _, _, leftBelow, _, _ => absurd leftBelow (Nat.not_lt_zero _)
  | head :: rest, distinct, indexLeft, indexRight, leftBelow, rightBelow, getEq => by
      have headNotMem : memBool head rest = false := by
        have split : isDistinctList (head :: rest) = (not (memBool head rest) && isDistinctList rest) := rfl
        rw [split] at distinct
        cases hmem : memBool head rest with
        | false => rfl
        | true => rw [hmem] at distinct; exact Bool.noConfusion (andLeftTrue _ _ distinct)
      have distRest : isDistinctList rest = true := by
        have split : isDistinctList (head :: rest) = (not (memBool head rest) && isDistinctList rest) := rfl
        rw [split] at distinct; exact andRightTrue _ _ distinct
      match indexLeft, indexRight with
      | 0, 0 => rfl
      | 0, indexR + 1 =>
          -- getAt (head::rest) 0 = head = getAt rest indexR, but head ∉ rest — contradiction
          have restBelow : indexR < rest.length := Nat.lt_of_succ_lt_succ rightBelow
          have headEqEntry : head = natListGetAt rest indexR := getEq
          have entryMem : natListGetAt rest indexR ∈ rest := getAt_mem rest indexR restBelow
          have headMem : memBool head rest = true := by
            rw [headEqEntry]; exact memBool_ofMem rest _ entryMem
          rw [headMem] at headNotMem; exact Bool.noConfusion headNotMem
      | indexL + 1, 0 =>
          have restBelow : indexL < rest.length := Nat.lt_of_succ_lt_succ leftBelow
          have headEqEntry : head = natListGetAt rest indexL := getEq.symm
          have entryMem : natListGetAt rest indexL ∈ rest := getAt_mem rest indexL restBelow
          have headMem : memBool head rest = true := by
            rw [headEqEntry]; exact memBool_ofMem rest _ entryMem
          rw [headMem] at headNotMem; exact Bool.noConfusion headNotMem
      | indexL + 1, indexR + 1 =>
          have leftRest : indexL < rest.length := Nat.lt_of_succ_lt_succ leftBelow
          have rightRest : indexR < rest.length := Nat.lt_of_succ_lt_succ rightBelow
          have restEq : natListGetAt rest indexL = natListGetAt rest indexR := getEq
          exact congrArg (· + 1)
            (perm_getAt_injective rest distRest indexL indexR leftRest rightRest restEq)

/-! ## The generic first-match scan with a unique satisfier -/

/-- **Unique-satisfier scan.**  If `target` is in the candidate list, passes the scan test, and is the ONLY candidate
that passes, `findPartnerScan` returns it — structural on the candidate list. -/
private theorem findPartnerScan_returnsUnique (links : List (Nat × Nat)) (boundaryNodes : List Nat)
    (rootHere excludeIndex target : Nat) :
    (candidates : List Nat) → target ∈ candidates →
    (target != excludeIndex
        && unionFindRootOf links (natListGetAt boundaryNodes target) == rootHere) = true →
    (∀ candidate ∈ candidates,
        (candidate != excludeIndex
          && unionFindRootOf links (natListGetAt boundaryNodes candidate) == rootHere) = true →
        candidate = target) →
    findPartnerScan links boundaryNodes rootHere excludeIndex candidates = target
  | [], memTarget, _, _ => nomatch memTarget
  | candidate :: rest, memTarget, testTarget, uniq => by
      rw [findPartnerScan_cons]
      cases hcond : (candidate != excludeIndex
          && unionFindRootOf links (natListGetAt boundaryNodes candidate) == rootHere) with
      | true =>
          exact uniq candidate (List.Mem.head rest) hcond
      | false =>
          have memRest : target ∈ rest := by
            cases memTarget with
            | head =>
                rw [hcond] at testTarget
                exact Bool.noConfusion testTarget
            | tail _ memRest => exact memRest
          exact findPartnerScan_returnsUnique links boundaryNodes rootHere excludeIndex target rest memRest
            testTarget (fun candidate memCandidate => uniq candidate (List.Mem.tail _ memCandidate))

/-! ## The permutation-forced partner + the read-off -/

/-- The permutation-forced boundary partner of `index`: the top port `n + perm⁻¹(index)` for a bottom port, the
bottom port `perm[index - n]` for a top port. -/
def permPartnerAt (bottomCount : Nat) (perm : List Nat) (index : Nat) : Nat :=
  if index < bottomCount then bottomCount + natIndexOfValue perm index
  else natListGetAt perm (index - bottomCount)

/-- The boundary node the append `List.range bottomCount ++ openWires` reads at `index` IS `boundaryNodeAt`. -/
private theorem boundaryNodes_getAt (bottomCount : Nat) (state : WireState)
    (openLen : state.openWires.length = bottomCount) (index : Nat) (indexBelow : index < bottomCount + bottomCount) :
    natListGetAt (List.range bottomCount ++ state.openWires) index = boundaryNodeAt bottomCount state index := by
  show natListGetAt (List.range bottomCount ++ state.openWires) index
    = (if index < bottomCount then index else natListGetAt state.openWires (index - bottomCount))
  cases Nat.lt_or_ge index bottomCount with
  | inl below =>
      rw [if_pos below,
        getAt_appendLeft (List.range bottomCount) state.openWires index ((range_length bottomCount).symm ▸ below),
        getAt_rangeTop bottomCount index below]
  | inr atLeast =>
      rw [if_neg (Nat.not_lt.mpr atLeast)]
      have rewriteIndex : index = (List.range bottomCount).length + (index - bottomCount) := by
        rw [range_length]; exact (addSubSelfLocal atLeast).symm
      exact (congrArg (natListGetAt (List.range bottomCount ++ state.openWires)) rewriteIndex).trans
        (getAt_appendRight (List.range bottomCount) state.openWires (index - bottomCount))

/-- ★ **The pointwise read-off.**  Under the permutation-graph invariant, the canonical `partnerIndexOf` scan returns
exactly `permPartnerAt`.  Assembles: boundary-node read-off, the boundView strand identification, `permPartnerAt`
validity + uniqueness (bijection facts), and the unique-satisfier scan. -/
private theorem partnerIndexOf_eq_permPartnerAt (bottomCount : Nat) (positions : List Nat) (state : WireState)
    (permGraph : StateIsPermGraph bottomCount positions state)
    (openLen : state.openWires.length = bottomCount) (index : Nat)
    (indexBelow : index < bottomCount + bottomCount) :
    partnerIndexOf state.links (List.range bottomCount ++ state.openWires) (bottomCount + bottomCount) index
      = permPartnerAt bottomCount (permuteOfCrossingWord bottomCount positions) index := by
  let perm := permuteOfCrossingWord bottomCount positions
  have permLen : perm.length = bottomCount := permuteOfCrossingWord_length bottomCount positions
  have distinct : isDistinctList perm = true := isDistinctList_permuteOfCrossingWord bottomCount positions
  -- the strand carried at a boundary index
  have strandUnfold : ∀ candidate,
      boundaryStrand bottomCount perm candidate
        = (if candidate < bottomCount then candidate else natListGetAt perm (candidate - bottomCount)) :=
    fun candidate => rfl
  -- the scan test at any in-range candidate reduces to a strand-equality decision
  have testEq : ∀ candidate, candidate < bottomCount + bottomCount →
      (unionFindRootOf state.links (natListGetAt (List.range bottomCount ++ state.openWires) candidate)
          == unionFindRootOf state.links (natListGetAt (List.range bottomCount ++ state.openWires) index))
        = decide (boundaryStrand bottomCount perm candidate = boundaryStrand bottomCount perm index) := by
    intro candidate candidateBelow
    rw [boundaryNodes_getAt bottomCount state openLen candidate candidateBelow,
      boundaryNodes_getAt bottomCount state openLen index indexBelow]
    exact permGraph.boundView candidate index candidateBelow indexBelow
  -- the strand at `index`
  have strandIndex : boundaryStrand bottomCount perm index
      = (if index < bottomCount then index else natListGetAt perm (index - bottomCount)) := rfl
  -- permPartnerAt validity: below-bound, distinct strand-partner, distinct from index
  have partnerBelow : permPartnerAt bottomCount perm index < bottomCount + bottomCount := by
    show (if index < bottomCount then bottomCount + natIndexOfValue perm index
          else natListGetAt perm (index - bottomCount)) < bottomCount + bottomCount
    cases Nat.lt_or_ge index bottomCount with
    | inl below =>
        rw [if_pos below]
        have memIndex : memBool index perm = true := perm_mem_ofLt bottomCount positions index below
        have indexOfLt : natIndexOfValue perm index < perm.length := (natIndexOfValue_roundtrip perm index memIndex).2
        exact Nat.add_lt_add_left (permLen ▸ indexOfLt) bottomCount
    | inr atLeast =>
        rw [if_neg (Nat.not_lt.mpr atLeast)]
        have subBelow : index - bottomCount < bottomCount := by
          have : index - bottomCount < bottomCount + bottomCount - bottomCount :=
            subLtSubRightLocal atLeast indexBelow
          rwa [addSubCancelLeftLocal] at this
        exact Nat.lt_of_lt_of_le (perm_getAt_lt bottomCount positions (index - bottomCount) subBelow)
          (Nat.le_add_left bottomCount bottomCount)
  have strandPartner : boundaryStrand bottomCount perm (permPartnerAt bottomCount perm index)
      = boundaryStrand bottomCount perm index := by
    cases Nat.lt_or_ge index bottomCount with
    | inl below =>
        have memIndex : memBool index perm = true := perm_mem_ofLt bottomCount positions index below
        have roundtrip := natIndexOfValue_roundtrip perm index memIndex
        have indexOfBelow : natIndexOfValue perm index < bottomCount := permLen ▸ roundtrip.2
        have partnerForm : permPartnerAt bottomCount perm index = bottomCount + natIndexOfValue perm index := by
          show (if index < bottomCount then bottomCount + natIndexOfValue perm index else _)
            = bottomCount + natIndexOfValue perm index
          rw [if_pos below]
        rw [partnerForm]
        show (if bottomCount + natIndexOfValue perm index < bottomCount then _
              else natListGetAt perm (bottomCount + natIndexOfValue perm index - bottomCount))
          = (if index < bottomCount then index else _)
        rw [if_neg (Nat.not_lt.mpr (Nat.le_add_right bottomCount (natIndexOfValue perm index))), if_pos below,
          addSubCancelLeftLocal]
        exact roundtrip.1
    | inr atLeast =>
        have subBelow : index - bottomCount < bottomCount := by
          have : index - bottomCount < bottomCount + bottomCount - bottomCount :=
            subLtSubRightLocal atLeast indexBelow
          rwa [addSubCancelLeftLocal] at this
        have valueBelow : natListGetAt perm (index - bottomCount) < bottomCount :=
          perm_getAt_lt bottomCount positions (index - bottomCount) subBelow
        have partnerForm : permPartnerAt bottomCount perm index = natListGetAt perm (index - bottomCount) := by
          show (if index < bottomCount then _ else natListGetAt perm (index - bottomCount))
            = natListGetAt perm (index - bottomCount)
          rw [if_neg (Nat.not_lt.mpr atLeast)]
        rw [partnerForm]
        show (if natListGetAt perm (index - bottomCount) < bottomCount then natListGetAt perm (index - bottomCount)
              else _)
          = (if index < bottomCount then _ else natListGetAt perm (index - bottomCount))
        rw [if_pos valueBelow, if_neg (Nat.not_lt.mpr atLeast)]
  have partnerNeIndex : permPartnerAt bottomCount perm index ≠ index := by
    cases Nat.lt_or_ge index bottomCount with
    | inl below =>
        have partnerForm : permPartnerAt bottomCount perm index = bottomCount + natIndexOfValue perm index := by
          show (if index < bottomCount then bottomCount + natIndexOfValue perm index else _)
            = bottomCount + natIndexOfValue perm index
          rw [if_pos below]
        rw [partnerForm]
        exact fun eq => Nat.lt_irrefl index
          (Nat.lt_of_lt_of_le below (eq ▸ Nat.le_add_right bottomCount (natIndexOfValue perm index)))
    | inr atLeast =>
        have subBelow : index - bottomCount < bottomCount := by
          have : index - bottomCount < bottomCount + bottomCount - bottomCount :=
            subLtSubRightLocal atLeast indexBelow
          rwa [addSubCancelLeftLocal] at this
        have valueBelow : natListGetAt perm (index - bottomCount) < bottomCount :=
          perm_getAt_lt bottomCount positions (index - bottomCount) subBelow
        have partnerForm : permPartnerAt bottomCount perm index = natListGetAt perm (index - bottomCount) := by
          show (if index < bottomCount then _ else natListGetAt perm (index - bottomCount))
            = natListGetAt perm (index - bottomCount)
          rw [if_neg (Nat.not_lt.mpr atLeast)]
        rw [partnerForm]
        exact fun eq => Nat.lt_irrefl index (Nat.lt_of_lt_of_le (eq ▸ valueBelow) atLeast)
  -- uniqueness: any in-range candidate with matching strand, distinct from index, is permPartnerAt
  have uniqueStrand : ∀ candidate, candidate < bottomCount + bottomCount → candidate ≠ index →
      boundaryStrand bottomCount perm candidate = boundaryStrand bottomCount perm index →
      candidate = permPartnerAt bottomCount perm index := by
    intro candidate candidateBelow candidateNe strandEq
    have candSub : candidate ≥ bottomCount → candidate - bottomCount < bottomCount := by
      intro atLeast
      have : candidate - bottomCount < bottomCount + bottomCount - bottomCount :=
        subLtSubRightLocal atLeast candidateBelow
      rwa [addSubCancelLeftLocal] at this
    have indexSub : index ≥ bottomCount → index - bottomCount < bottomCount := by
      intro atLeast
      have : index - bottomCount < bottomCount + bottomCount - bottomCount :=
        subLtSubRightLocal atLeast indexBelow
      rwa [addSubCancelLeftLocal] at this
    cases Nat.lt_or_ge index bottomCount with
    | inl indexLow =>
        -- strand index = index
        have strandIndexVal : boundaryStrand bottomCount perm index = index := by
          rw [strandIndex, if_pos indexLow]
        have partnerForm : permPartnerAt bottomCount perm index = bottomCount + natIndexOfValue perm index := by
          show (if index < bottomCount then bottomCount + natIndexOfValue perm index else _)
            = bottomCount + natIndexOfValue perm index
          rw [if_pos indexLow]
        cases Nat.lt_or_ge candidate bottomCount with
        | inl candLow =>
            have strandCand : boundaryStrand bottomCount perm candidate = candidate := by
              rw [strandUnfold candidate, if_pos candLow]
            rw [strandCand, strandIndexVal] at strandEq
            exact absurd strandEq candidateNe
        | inr candHigh =>
            have candSubLt : candidate - bottomCount < bottomCount := candSub candHigh
            have strandCand : boundaryStrand bottomCount perm candidate
                = natListGetAt perm (candidate - bottomCount) := by
              rw [strandUnfold candidate, if_neg (Nat.not_lt.mpr candHigh)]
            rw [strandCand, strandIndexVal] at strandEq
            -- perm[candidate - n] = index = perm[natIndexOfValue perm index]
            have memIndex : memBool index perm = true := perm_mem_ofLt bottomCount positions index indexLow
            have roundtrip := natIndexOfValue_roundtrip perm index memIndex
            have indexOfBelow : natIndexOfValue perm index < perm.length := roundtrip.2
            have entriesEq : natListGetAt perm (candidate - bottomCount)
                = natListGetAt perm (natIndexOfValue perm index) := by rw [strandEq, roundtrip.1]
            have injEq : candidate - bottomCount = natIndexOfValue perm index :=
              perm_getAt_injective perm distinct (candidate - bottomCount) (natIndexOfValue perm index)
                (permLen ▸ candSubLt) indexOfBelow entriesEq
            rw [partnerForm]
            calc candidate = bottomCount + (candidate - bottomCount) := (addSubSelfLocal candHigh).symm
              _ = bottomCount + natIndexOfValue perm index := by rw [injEq]
    | inr indexHigh =>
        have indexSubLt : index - bottomCount < bottomCount := indexSub indexHigh
        have strandIndexVal : boundaryStrand bottomCount perm index = natListGetAt perm (index - bottomCount) := by
          rw [strandIndex, if_neg (Nat.not_lt.mpr indexHigh)]
        have valueBelow : natListGetAt perm (index - bottomCount) < bottomCount :=
          perm_getAt_lt bottomCount positions (index - bottomCount) indexSubLt
        have partnerForm : permPartnerAt bottomCount perm index = natListGetAt perm (index - bottomCount) := by
          show (if index < bottomCount then _ else natListGetAt perm (index - bottomCount))
            = natListGetAt perm (index - bottomCount)
          rw [if_neg (Nat.not_lt.mpr indexHigh)]
        cases Nat.lt_or_ge candidate bottomCount with
        | inl candLow =>
            have strandCand : boundaryStrand bottomCount perm candidate = candidate := by
              rw [strandUnfold candidate, if_pos candLow]
            rw [strandCand, strandIndexVal] at strandEq
            rw [partnerForm]; exact strandEq
        | inr candHigh =>
            have candSubLt : candidate - bottomCount < bottomCount := candSub candHigh
            have strandCand : boundaryStrand bottomCount perm candidate
                = natListGetAt perm (candidate - bottomCount) := by
              rw [strandUnfold candidate, if_neg (Nat.not_lt.mpr candHigh)]
            rw [strandCand, strandIndexVal] at strandEq
            have injEq : candidate - bottomCount = index - bottomCount :=
              perm_getAt_injective perm distinct (candidate - bottomCount) (index - bottomCount)
                (permLen ▸ candSubLt) (permLen ▸ indexSubLt) strandEq
            have candEqIndex : candidate = index := by
              calc candidate = bottomCount + (candidate - bottomCount) := (addSubSelfLocal candHigh).symm
                _ = bottomCount + (index - bottomCount) := by rw [injEq]
                _ = index := addSubSelfLocal indexHigh
            exact absurd candEqIndex candidateNe
  -- assemble via the unique-satisfier scan
  show findPartnerScan state.links (List.range bottomCount ++ state.openWires)
      (unionFindRootOf state.links (natListGetAt (List.range bottomCount ++ state.openWires) index)) index
      (List.range (bottomCount + bottomCount))
    = permPartnerAt bottomCount perm index
  apply findPartnerScan_returnsUnique state.links (List.range bottomCount ++ state.openWires)
    (unionFindRootOf state.links (natListGetAt (List.range bottomCount ++ state.openWires) index)) index
    (permPartnerAt bottomCount perm index)
    (List.range (bottomCount + bottomCount))
  · exact memRange_ofLt (bottomCount + bottomCount) (permPartnerAt bottomCount perm index) partnerBelow
  · apply andBothTrue
    · exact bneTrueOfNe (permPartnerAt bottomCount perm index) index partnerNeIndex
    · rw [testEq (permPartnerAt bottomCount perm index) partnerBelow]
      exact decideNatTrueOfEq _ _ strandPartner
  · intro candidate memCandidate candTest
    have candidateBelow : candidate < bottomCount + bottomCount :=
      lt_ofMemRange (bottomCount + bottomCount) candidate memCandidate
    have candNe : candidate ≠ index :=
      neOfBneTrue candidate index (andLeftTrue _ _ candTest)
    have strandDecide : decide (boundaryStrand bottomCount perm candidate = boundaryStrand bottomCount perm index)
        = true := by
      rw [← testEq candidate candidateBelow]; exact andRightTrue _ _ candTest
    exact uniqueStrand candidate candidateBelow candNe (eqOfDecideNatTrue _ _ strandDecide)

/-! ## The diagram equality + the corrected readback -/

/-- Congruence for `DiagramType` component literals. -/
private theorem diagramType_ext {bottomLeft topLeft loopsLeft : Nat} {partnerLeft : List Nat}
    {bottomRight topRight loopsRight : Nat} {partnerRight : List Nat}
    (bottomEq : bottomLeft = bottomRight) (topEq : topLeft = topRight)
    (partnerEq : partnerLeft = partnerRight) (loopsEq : loopsLeft = loopsRight) :
    (⟨bottomLeft, topLeft, partnerLeft, loopsLeft⟩ : DiagramType) = ⟨bottomRight, topRight, partnerRight, loopsRight⟩ := by
  rw [bottomEq, topEq, partnerEq, loopsEq]

/-- ★ **The read-off diagram equality.**  Under the permutation-graph invariant, the extracted Brauer diagram IS the
permutation diagram of the through-strand permutation. -/
theorem extractDiagram_eq_permutationDiagram_ofPermGraph (bottomCount : Nat) (positions : List Nat)
    (state : WireState) (permGraph : StateIsPermGraph bottomCount positions state) :
    extractDiagram bottomCount state
      = permutationDiagram bottomCount (permuteOfCrossingWord bottomCount positions) := by
  let perm := permuteOfCrossingWord bottomCount positions
  have openLen : state.openWires.length = bottomCount := permGraph.openLen
  have loopsZero : state.loops = 0 := permGraph.noLoops
  -- partner list equality by extensionality
  have partnerEq :
      (List.range (bottomCount + state.openWires.length)).map
          (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
            (bottomCount + state.openWires.length))
        = (List.range bottomCount).map (fun bottomPort => bottomCount + natIndexOfValue perm bottomPort)
          ++ (List.range bottomCount).map (natListGetAt perm) := by
    rw [openLen]
    apply listExtGetAt
    · rw [map_length, range_length,
        listLengthAppendLocal, map_length, map_length, range_length]
    · intro index indexBelow
      have indexRange : index < bottomCount + bottomCount := by
        rw [map_length, range_length] at indexBelow; exact indexBelow
      -- left side
      have leftGet : natListGetAt ((List.range (bottomCount + bottomCount)).map
            (partnerIndexOf state.links (List.range bottomCount ++ state.openWires) (bottomCount + bottomCount)))
            index
          = permPartnerAt bottomCount perm index := by
        rw [getAt_map _ (List.range (bottomCount + bottomCount)) index
            ((range_length (bottomCount + bottomCount)).symm ▸ indexRange),
          getAt_rangeTop (bottomCount + bottomCount) index indexRange]
        exact partnerIndexOf_eq_permPartnerAt bottomCount positions state permGraph openLen index indexRange
      -- right side split by append
      have rightGet : natListGetAt
            ((List.range bottomCount).map (fun bottomPort => bottomCount + natIndexOfValue perm bottomPort)
              ++ (List.range bottomCount).map (natListGetAt perm)) index
          = permPartnerAt bottomCount perm index := by
        cases Nat.lt_or_ge index bottomCount with
        | inl below =>
            have leftLenEq : ((List.range bottomCount).map
                (fun bottomPort => bottomCount + natIndexOfValue perm bottomPort)).length = bottomCount := by
              rw [map_length, range_length]
            rw [getAt_appendLeft _ _ index (leftLenEq.symm ▸ below),
              getAt_map _ (List.range bottomCount) index ((range_length bottomCount).symm ▸ below),
              getAt_rangeTop bottomCount index below]
            show bottomCount + natIndexOfValue perm index = permPartnerAt bottomCount perm index
            rw [show permPartnerAt bottomCount perm index = bottomCount + natIndexOfValue perm index from by
                show (if index < bottomCount then bottomCount + natIndexOfValue perm index else _)
                  = bottomCount + natIndexOfValue perm index
                rw [if_pos below]]
        | inr atLeast =>
            have subBelow : index - bottomCount < bottomCount := by
              have step : index - bottomCount < bottomCount + bottomCount - bottomCount :=
                subLtSubRightLocal atLeast indexRange
              rwa [addSubCancelLeftLocal] at step
            have partnerForm : permPartnerAt bottomCount perm index = natListGetAt perm (index - bottomCount) := by
              show (if index < bottomCount then _ else natListGetAt perm (index - bottomCount))
                = natListGetAt perm (index - bottomCount)
              rw [if_neg (Nat.not_lt.mpr atLeast)]
            have indexForm : ((List.range bottomCount).map
                (fun bottomPort => bottomCount + natIndexOfValue perm bottomPort)).length + (index - bottomCount)
                = index := by
              rw [map_length, range_length]; exact addSubSelfLocal atLeast
            rw [partnerForm]
            refine (congrArg (natListGetAt ((List.range bottomCount).map
                (fun bottomPort => bottomCount + natIndexOfValue perm bottomPort)
              ++ (List.range bottomCount).map (natListGetAt perm))) indexForm.symm).trans ?_
            rw [getAt_appendRight _ _ (index - bottomCount),
              getAt_map _ (List.range bottomCount) (index - bottomCount)
                ((range_length bottomCount).symm ▸ subBelow),
              getAt_rangeTop bottomCount (index - bottomCount) subBelow]
      rw [leftGet, rightGet]
  -- assemble the diagram equality
  show (⟨bottomCount, state.openWires.length,
        (List.range (bottomCount + state.openWires.length)).map
          (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
            (bottomCount + state.openWires.length)),
        state.loops⟩ : DiagramType)
    = ⟨bottomCount, bottomCount,
        (List.range bottomCount).map (fun bottomPort => bottomCount + natIndexOfValue perm bottomPort)
          ++ (List.range bottomCount).map (natListGetAt perm), 0⟩
  exact diagramType_ext rfl openLen partnerEq loopsZero

/-- ★★ **The corrected crossing-only readback, PROVEN.**  For every strand count and every in-range crossing word, the
extracted Brauer diagram equals the permutation diagram of the through-strand permutation.  The `bottomCount = 0`
degenerate case forces an empty word; otherwise the state invariant `stateIsPermGraph_ofInRange` feeds the read-off. -/
theorem brauerCrossingOnlyReadbackInRange_proof : BrauerCrossingOnlyReadbackInRange := by
  intro bottomCount positions inRange
  cases bottomCount with
  | zero =>
      have positionsNil : positions = [] := by
        cases positions with
        | nil => rfl
        | cons head _ => exact absurd (inRange head (List.Mem.head _)) (Nat.not_succ_le_zero (head + 1))
      rw [positionsNil]; rfl
  | succ pred =>
      exact extractDiagram_eq_permutationDiagram_ofPermGraph (pred + 1) positions
        (processBrauer (brauerSeed (pred + 1)) (crossingWord positions))
        (stateIsPermGraph_ofInRange (pred + 1) (Nat.succ_pos pred) positions inRange)

/-- ★ **Honesty marker — the crossing-only readback bridge is PROVEN (the r4 residual discharged).**
`extractDiagram_eq_permutationDiagram_ofPermGraph` reads the T2 state invariant off into the diagram equality, and
`brauerCrossingOnlyReadbackInRange_proof` closes the corrected boundary-width-aware `BrauerCrossingOnlyReadbackInRange`
UNCONDITIONALLY (no readback hypothesis).  The read-off is the `findPartnerScan`/`partnerIndexOf` uniqueness argument
over the now-proven permutation graph (`findPartnerScan_returnsUnique` + `permPartnerAt` validity/uniqueness from the
`permuteOfCrossingWord` bijection facts).  Zero-axiom, structural.  This is the V2-scoped node the r4 recon named as
"the single realistically-shippable r2 node".  `= true`. -/
def fxBrauer_hasCrossingOnlyReadbackProof : Bool := true

end FX1Poly.Polygraph
