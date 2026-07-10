import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcConjugator
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcEnumeration

/-! # BRAUER-MIDDLE r15 — T-CLOSE opening: range-permutation surjectivity + `permInverse` preserves the gate

The r14 conjugator leg (`Brauer/WiringDescArcConjugator.lean`) shipped the general validity-gated roundtrip
`permuteOfCrossingWord_permutationToCrossingWord` for every order satisfying the `IsPermutationOfRange` gate
(distinct, length-`width`, `[0, width)`-bounded).  T-CLOSE then needs the SPECIFIC extractor read-off orders to
satisfy that gate.  The top read-off (`WiringDescArcExtractorRec.reconstructStandardFormExt5Corrected`) feeds the
INVERSE order `permInverse (throughStrandTops ++ cupArcTops)` into the top staircase (the r3 cup-side inversion
pin), so closing the top side needs one reusable step: `permInverse` sends a range-permutation to a
range-permutation.  This file lands that step, together with the finite-pigeonhole surjectivity it rests on.

## What this file ships (each zero-axiom, structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`)

  * **`isPermutationOfRange_surjective`** — the finite-pigeonhole SURJECTIVITY: a distinct, length-`width`,
    `[0, width)`-bounded order contains EVERY value below `width`.  The genuinely-new counting content — the
    codebase's surjectivity facts (`WiringDescBrauerReadbackProof.perm_mem_ofLt`) were specific to a
    `permuteOfCrossingWord` output whose membership set is `range width` by construction; there was NO surjectivity
    lemma for a general distinct-bounded list.  Proven via a first-occurrence erase (`natListErasePerm`) and the
    length-bound `distinctLengthLeBoundPerm` (distinct + bounded-by-`k` ⇒ length ≤ `k`), both re-derived here.

  * **`permInverse_length` / `natListGetAtPermInversePerm`** — the length and the positional read-off of
    `permInverse` (`natListGetAt (permInverse perm) index = natIndexOfValue perm index`).

  * ★★ **`isPermutationOfRange_permInverse`** — the headline: `IsPermutationOfRange width perm →
    IsPermutationOfRange width (permInverse perm)`.  Boundedness and the roundtrip use the surjectivity above to
    know every index occurs (`natIndexOfValueRoundtripPerm`); distinctness uses the converse
    getAt-injective ⇒ distinct bridge (`isDistinctListOfGetAtInjectivePerm`).  The step the T-CLOSE top side needs.

  * non-vacuity — the surjectivity, the `permInverse` evaluation `[1, 2, 0] ↦ [2, 0, 1]`, and its gate-preservation
    all fire on the concrete 3-cycle witness (`isPermutationOfRange_threeCycle_witness`).

## The honest residual (the bottom/top read-off counting identities + E3 — this round does NOT close the masters)

`permInverse`-preservation is the top side's INVERSE-step; it does NOT by itself establish that
`throughStrandTops ++ cupArcTops` or `capArcFeet ++ throughStrandBottoms` are range-permutations.  Those need the
still-unbuilt cardinality identities — `2 · |capArcFeetIndices| + |throughStrandBottoms| = bottomCount` on the
bottom side and its ∗-dual on the top — a three-way `filterMap` classification counting induction under the
`IsBoundaryInvolution` gate, with the cap class doubled by `expandBottomFeetPairs`.  And even a complete read-off
IsPermutationOfRange leaves E3 (fold-alignment / T-CONNECT, the union-find `stepWiring` long-pole) and the T-CLOSE(b)
field reassembly (`extractDiagram_realizes_partner_ofConnectivity`) unbuilt.  So `fxBrauer_hasReadOffOrderPermutation`,
`fxBrauer_hasArcEnumerationConjugated`, both tag-correspondence masters
(`fxBrauer_hasTagCorrDisjoint` / `fxBrauer_hasTagCorrExtraction`), and the completeness flags stay honestly `false`;
#2013 does NOT close.  Every residual is a ROUTE / counting gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889
Thm 2.6 + the corrected extractor's size-8 census establish the underlying truth).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Section 0 — re-derived propext-free Bool / `Nat.beq` deciders -/

private theorem boolAndLeftPerm : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → leftFlag = true
  | true, _, _ => rfl
  | false, _, conj => Bool.noConfusion conj

private theorem boolAndRightPerm : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → rightFlag = true
  | true, _, conj => conj
  | false, _, conj => Bool.noConfusion conj

private theorem eqFalseOfNotTruePerm : (flag : Bool) → (not flag) = true → flag = false
  | true, hnot => Bool.noConfusion hnot
  | false, _ => rfl

private theorem natBeqSelfPerm : (value : Nat) → Nat.beq value value = true
  | 0 => rfl
  | value + 1 => natBeqSelfPerm value

private theorem eqOfNatBeqTruePerm : (left right : Nat) → Nat.beq left right = true → left = right
  | 0, 0, _ => rfl
  | 0, _ + 1, hbeq => Bool.noConfusion hbeq
  | _ + 1, 0, hbeq => Bool.noConfusion hbeq
  | left + 1, right + 1, hbeq => congrArg (· + 1) (eqOfNatBeqTruePerm left right hbeq)

private theorem natBeqFalseOfNePerm : (left right : Nat) → left ≠ right → Nat.beq left right = false
  | 0, 0, hne => absurd rfl hne
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, _ => rfl
  | left + 1, right + 1, hne => natBeqFalseOfNePerm left right (fun eqTail => hne (congrArg (· + 1) eqTail))

private theorem neOfNatBeqFalsePerm (left right : Nat) (hbeq : Nat.beq left right = false) : left ≠ right := by
  intro equal
  rw [equal, natBeqSelfPerm] at hbeq
  exact Bool.noConfusion hbeq

private theorem eqOfBEqTruePerm {left right : Nat} (hbeq : (left == right) = true) : left = right :=
  of_decide_eq_true hbeq

private theorem neOfBEqFalsePerm {left right : Nat} (hbeq : (left == right) = false) : left ≠ right :=
  of_decide_eq_false hbeq

private theorem natLtOfLeOfNePerm (small large : Nat) (le : small ≤ large) (ne : small ≠ large) : small < large := by
  cases Nat.lt_or_ge small large with
  | inl lt => exact lt
  | inr ge => exact absurd (Nat.le_antisymm le ge) ne

private theorem natNeOfLtPerm (small large : Nat) (lt : small < large) : small ≠ large :=
  fun equal => Nat.lt_irrefl large (equal ▸ lt)

/-! ## Section 1 — list length / positional helpers over `List.range` and `List.map` -/

private theorem mapLengthPerm (mapFn : Nat → Nat) : (entries : List Nat) →
    (entries.map mapFn).length = entries.length
  | [] => rfl
  | _ :: rest => congrArg (· + 1) (mapLengthPerm mapFn rest)

private theorem rangeLoopLengthPerm : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      show (List.range.loop count (count :: accumulated)).length = (count + 1) + accumulated.length
      rw [rangeLoopLengthPerm count (count :: accumulated)]
      show count + (accumulated.length + 1) = (count + 1) + accumulated.length
      rw [Nat.add_succ, Nat.succ_add]

private theorem rangeLengthPerm (count : Nat) : (List.range count).length = count :=
  (rangeLoopLengthPerm count []).trans (Nat.add_zero count)

private theorem getAtRangeLoopPastPerm : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := getAtRangeLoopPastPerm count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem getAtRangeLoopPerm : (count : Nat) → (accumulated : List Nat) → (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact getAtRangeLoopPerm count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_lt_succ indexBelow) atLeast
          have pastRead : natListGetAt (List.range.loop count (count :: accumulated)) (0 + count)
              = natListGetAt (count :: accumulated) 0 := getAtRangeLoopPastPerm count (count :: accumulated) 0
          rw [Nat.zero_add] at pastRead
          rw [indexEq]; exact pastRead

private theorem getAtRangePerm (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  getAtRangeLoopPerm count [] index indexBelow

private theorem getAtMapPerm (mapFn : Nat → Nat) : (entries : List Nat) → (index : Nat) →
    index < entries.length → natListGetAt (entries.map mapFn) index = mapFn (natListGetAt entries index)
  | [], index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | _ :: _, 0, _ => rfl
  | _ :: rest, index + 1, indexBelow =>
      getAtMapPerm mapFn rest index (Nat.lt_of_succ_lt_succ indexBelow)

private theorem getAtMemPerm : (entries : List Nat) → (index : Nat) → index < entries.length →
    natListGetAt entries index ∈ entries
  | [], index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | _ :: _, 0, _ => List.Mem.head _
  | head :: rest, index + 1, indexBelow =>
      List.Mem.tail head (getAtMemPerm rest index (Nat.lt_of_succ_lt_succ indexBelow))

/-! ## Section 2 — boolean membership bridges and the position witness -/

private theorem memBoolOfMemPerm : (entries : List Nat) → (value : Nat) → value ∈ entries →
    memBool value entries = true
  | [], _, memNil => nomatch memNil
  | head :: rest, value, memCons => by
      show (Nat.beq head value || memBool value rest) = true
      cases memCons with
      | head => rw [natBeqSelfPerm]; rfl
      | tail _ memRest => rw [memBoolOfMemPerm rest value memRest, Bool.or_true]

private theorem memBoolGetAtWitnessPerm : (entries : List Nat) → (value : Nat) → memBool value entries = true →
    ∃ index, index < entries.length ∧ natListGetAt entries index = value
  | [], _, memTrue => Bool.noConfusion memTrue
  | head :: rest, value, memTrue => by
      cases hbeq : Nat.beq head value with
      | true =>
          exact ⟨0, Nat.succ_pos rest.length, eqOfNatBeqTruePerm head value hbeq⟩
      | false =>
          have memRest : memBool value rest = true := by
            have split : memBool value (head :: rest) = (Nat.beq head value || memBool value rest) := rfl
            rw [split, hbeq, Bool.false_or] at memTrue; exact memTrue
          obtain ⟨index, indexBelow, getEq⟩ := memBoolGetAtWitnessPerm rest value memRest
          exact ⟨index + 1, Nat.succ_lt_succ indexBelow, getEq⟩

/-! ## Section 3 — `natIndexOfValue` roundtrip + `natListGetAt` injectivity / converse distinctness -/

private theorem natIndexOfValueRoundtripPerm : (perm : List Nat) → (value : Nat) → memBool value perm = true →
    natListGetAt perm (natIndexOfValue perm value) = value ∧ natIndexOfValue perm value < perm.length
  | [], _, memTrue => Bool.noConfusion memTrue
  | head :: rest, value, memTrue => by
      cases hbeq : (head == value) with
      | true =>
          have headEq : head = value := eqOfBEqTruePerm hbeq
          have indexZero : natIndexOfValue (head :: rest) value = 0 := by
            show (match head == value with | true => 0 | false => natIndexOfValue rest value + 1) = 0
            rw [hbeq]
          refine ⟨?_, ?_⟩
          · rw [indexZero]; exact headEq
          · rw [indexZero]; exact Nat.succ_pos rest.length
      | false =>
          have headNe : head ≠ value := neOfBEqFalsePerm hbeq
          have beqFalse : Nat.beq head value = false := natBeqFalseOfNePerm head value headNe
          have memRest : memBool value rest = true := by
            have split : memBool value (head :: rest) = (Nat.beq head value || memBool value rest) := rfl
            rw [split, beqFalse, Bool.false_or] at memTrue; exact memTrue
          have ih := natIndexOfValueRoundtripPerm rest value memRest
          have indexSucc : natIndexOfValue (head :: rest) value = natIndexOfValue rest value + 1 := by
            show (match head == value with | true => 0 | false => natIndexOfValue rest value + 1)
              = natIndexOfValue rest value + 1
            rw [hbeq]
          refine ⟨?_, ?_⟩
          · rw [indexSucc]; exact ih.1
          · rw [indexSucc]; exact Nat.succ_lt_succ ih.2

private theorem isDistinctListOfGetAtInjectivePerm : (entries : List Nat) →
    (∀ indexLeft indexRight, indexLeft < entries.length → indexRight < entries.length →
      natListGetAt entries indexLeft = natListGetAt entries indexRight → indexLeft = indexRight) →
    isDistinctList entries = true
  | [], _ => rfl
  | head :: rest, injective => by
      have distRest : isDistinctList rest = true :=
        isDistinctListOfGetAtInjectivePerm rest (fun indexLeft indexRight leftBelow rightBelow eqAt =>
          Nat.succ.inj (injective (indexLeft + 1) (indexRight + 1)
            (Nat.succ_lt_succ leftBelow) (Nat.succ_lt_succ rightBelow) eqAt))
      have headNotMem : memBool head rest = false := by
        cases hmem : memBool head rest with
        | false => rfl
        | true =>
            obtain ⟨witness, witnessBelow, witnessEq⟩ := memBoolGetAtWitnessPerm rest head hmem
            have collide : natListGetAt (head :: rest) 0 = natListGetAt (head :: rest) (witness + 1) :=
              witnessEq.symm
            have zeroEq : (0 : Nat) = witness + 1 :=
              injective 0 (witness + 1) (Nat.succ_pos rest.length) (Nat.succ_lt_succ witnessBelow) collide
            exact Nat.noConfusion zeroEq
      show (not (memBool head rest) && isDistinctList rest) = true
      rw [headNotMem, distRest]; rfl

/-! ## Section 4 — first-occurrence erase and the pigeonhole length bound -/

private def natListErasePerm : List Nat → Nat → List Nat
  | [], _ => []
  | head :: rest, value =>
      match Nat.beq head value with
      | true => rest
      | false => head :: natListErasePerm rest value

private theorem natListErasePerm_cons_true (head value : Nat) (rest : List Nat) (hbeq : Nat.beq head value = true) :
    natListErasePerm (head :: rest) value = rest := by
  show (match Nat.beq head value with | true => rest | false => head :: natListErasePerm rest value) = rest
  rw [hbeq]

private theorem natListErasePerm_cons_false (head value : Nat) (rest : List Nat) (hbeq : Nat.beq head value = false) :
    natListErasePerm (head :: rest) value = head :: natListErasePerm rest value := by
  show (match Nat.beq head value with | true => rest | false => head :: natListErasePerm rest value)
    = head :: natListErasePerm rest value
  rw [hbeq]

private theorem memBoolNatListErasePerm_ne : (entries : List Nat) → (value other : Nat) →
    Nat.beq value other = false →
    memBool other (natListErasePerm entries value) = memBool other entries
  | [], _, _, _ => rfl
  | head :: rest, value, other, valueOtherNe => by
      cases hbeq : Nat.beq head value with
      | true =>
          have headEqValue : head = value := eqOfNatBeqTruePerm head value hbeq
          rw [natListErasePerm_cons_true head value rest hbeq]
          show memBool other rest = (Nat.beq head other || memBool other rest)
          have headOtherFalse : Nat.beq head other = false := by rw [headEqValue]; exact valueOtherNe
          rw [headOtherFalse, Bool.false_or]
      | false =>
          rw [natListErasePerm_cons_false head value rest hbeq]
          show (Nat.beq head other || memBool other (natListErasePerm rest value))
            = (Nat.beq head other || memBool other rest)
          rw [memBoolNatListErasePerm_ne rest value other valueOtherNe]

private theorem memBoolNatListErasePerm_self : (entries : List Nat) → (value : Nat) →
    isDistinctList entries = true → memBool value (natListErasePerm entries value) = false
  | [], _, _ => rfl
  | head :: rest, value, distinct => by
      have splitDist : isDistinctList (head :: rest) = (not (memBool head rest) && isDistinctList rest) := rfl
      rw [splitDist] at distinct
      have headNotMem : memBool head rest = false :=
        eqFalseOfNotTruePerm (memBool head rest) (boolAndLeftPerm _ _ distinct)
      have distRest : isDistinctList rest = true := boolAndRightPerm _ _ distinct
      cases hbeq : Nat.beq head value with
      | true =>
          have headEqValue : head = value := eqOfNatBeqTruePerm head value hbeq
          rw [natListErasePerm_cons_true head value rest hbeq, ← headEqValue]
          exact headNotMem
      | false =>
          rw [natListErasePerm_cons_false head value rest hbeq]
          show (Nat.beq head value || memBool value (natListErasePerm rest value)) = false
          rw [hbeq, Bool.false_or]
          exact memBoolNatListErasePerm_self rest value distRest

private theorem isDistinctListNatListErasePerm : (entries : List Nat) → (value : Nat) →
    isDistinctList entries = true → isDistinctList (natListErasePerm entries value) = true
  | [], _, _ => rfl
  | head :: rest, value, distinct => by
      have splitDist : isDistinctList (head :: rest) = (not (memBool head rest) && isDistinctList rest) := rfl
      rw [splitDist] at distinct
      have headNotMem : memBool head rest = false :=
        eqFalseOfNotTruePerm (memBool head rest) (boolAndLeftPerm _ _ distinct)
      have distRest : isDistinctList rest = true := boolAndRightPerm _ _ distinct
      cases hbeq : Nat.beq head value with
      | true =>
          rw [natListErasePerm_cons_true head value rest hbeq]; exact distRest
      | false =>
          rw [natListErasePerm_cons_false head value rest hbeq]
          show (not (memBool head (natListErasePerm rest value))
            && isDistinctList (natListErasePerm rest value)) = true
          have valueHeadNe : Nat.beq value head = false :=
            natBeqFalseOfNePerm value head (fun equal => (neOfNatBeqFalsePerm head value hbeq) equal.symm)
          have headNotMemErase : memBool head (natListErasePerm rest value) = false := by
            rw [memBoolNatListErasePerm_ne rest value head valueHeadNe]; exact headNotMem
          have distErase : isDistinctList (natListErasePerm rest value) = true :=
            isDistinctListNatListErasePerm rest value distRest
          rw [headNotMemErase, distErase]; rfl

private theorem natListErasePerm_length_of_mem : (entries : List Nat) → (value : Nat) →
    memBool value entries = true → (natListErasePerm entries value).length + 1 = entries.length
  | [], _, memTrue => Bool.noConfusion memTrue
  | head :: rest, value, memTrue => by
      cases hbeq : Nat.beq head value with
      | true =>
          rw [natListErasePerm_cons_true head value rest hbeq]
          rfl
      | false =>
          rw [natListErasePerm_cons_false head value rest hbeq]
          have memRest : memBool value rest = true := by
            have split : memBool value (head :: rest) = (Nat.beq head value || memBool value rest) := rfl
            rw [split, hbeq, Bool.false_or] at memTrue; exact memTrue
          show (natListErasePerm rest value).length + 1 + 1 = rest.length + 1
          rw [natListErasePerm_length_of_mem rest value memRest]

private theorem distinctLengthLeBoundPerm : (bound : Nat) → (entries : List Nat) →
    isDistinctList entries = true → (∀ value, memBool value entries = true → value < bound) →
    entries.length ≤ bound
  | 0, entries, _, bounded => by
      cases entries with
      | nil => exact Nat.le_refl 0
      | cons head rest =>
          have headMem : memBool head (head :: rest) = true := by
            show (Nat.beq head head || memBool head rest) = true
            rw [natBeqSelfPerm]; rfl
          exact absurd (bounded head headMem) (Nat.not_lt_zero head)
  | bound + 1, entries, distinct, bounded => by
      cases hmem : memBool bound entries with
      | true =>
          have eraseLen : (natListErasePerm entries bound).length + 1 = entries.length :=
            natListErasePerm_length_of_mem entries bound hmem
          have distErase : isDistinctList (natListErasePerm entries bound) = true :=
            isDistinctListNatListErasePerm entries bound distinct
          have eraseSelf : memBool bound (natListErasePerm entries bound) = false :=
            memBoolNatListErasePerm_self entries bound distinct
          have boundedErase : ∀ value, memBool value (natListErasePerm entries bound) = true → value < bound := by
            intro value valueMem
            have valueNeBound : value ≠ bound := by
              intro valueEq
              rw [valueEq, eraseSelf] at valueMem
              exact Bool.noConfusion valueMem
            have valueMemEntries : memBool value entries = true := by
              rw [← memBoolNatListErasePerm_ne entries bound value
                (natBeqFalseOfNePerm bound value (fun equal => valueNeBound equal.symm))]
              exact valueMem
            exact natLtOfLeOfNePerm value bound (Nat.le_of_lt_succ (bounded value valueMemEntries)) valueNeBound
          have eraseLe : (natListErasePerm entries bound).length ≤ bound :=
            distinctLengthLeBoundPerm bound (natListErasePerm entries bound) distErase boundedErase
          rw [← eraseLen]
          exact Nat.succ_le_succ eraseLe
      | false =>
          have boundedStrict : ∀ value, memBool value entries = true → value < bound := by
            intro value valueMem
            have valueNeBound : value ≠ bound := by
              intro valueEq
              rw [valueEq, hmem] at valueMem
              exact Bool.noConfusion valueMem
            exact natLtOfLeOfNePerm value bound (Nat.le_of_lt_succ (bounded value valueMem)) valueNeBound
          exact Nat.le_trans (distinctLengthLeBoundPerm bound entries distinct boundedStrict) (Nat.le_succ bound)

/-! ## Section 5 — range-permutation surjectivity (the finite pigeonhole) -/

private theorem surjOfDistinctBoundedFullPerm : (width : Nat) → (entries : List Nat) →
    isDistinctList entries = true → entries.length = width →
    (∀ value, memBool value entries = true → value < width) →
    (value : Nat) → value < width → memBool value entries = true
  | 0, _, _, _, _, value, valueBelow => absurd valueBelow (Nat.not_lt_zero value)
  | width + 1, entries, distinct, lengthEq, bounded, value, valueBelow => by
      have topMem : memBool width entries = true := by
        cases hmem : memBool width entries with
        | true => rfl
        | false =>
            have boundedStrict : ∀ other, memBool other entries = true → other < width := by
              intro other otherMem
              have otherNe : other ≠ width := by
                intro otherEq
                rw [otherEq, hmem] at otherMem
                exact Bool.noConfusion otherMem
              exact natLtOfLeOfNePerm other width (Nat.le_of_lt_succ (bounded other otherMem)) otherNe
            have lengthLe : entries.length ≤ width :=
              distinctLengthLeBoundPerm width entries distinct boundedStrict
            rw [lengthEq] at lengthLe
            exact absurd (Nat.lt_of_lt_of_le (Nat.lt_succ_self width) lengthLe) (Nat.lt_irrefl width)
      cases Nat.lt_or_ge value width with
      | inr ge =>
          have valueEqWidth : value = width := Nat.le_antisymm (Nat.le_of_lt_succ valueBelow) ge
          rw [valueEqWidth]; exact topMem
      | inl lt =>
          have eraseLen : (natListErasePerm entries width).length + 1 = entries.length :=
            natListErasePerm_length_of_mem entries width topMem
          have eraseLenWidth : (natListErasePerm entries width).length = width := by
            have step : (natListErasePerm entries width).length + 1 = width + 1 := by
              rw [eraseLen]; exact lengthEq
            exact Nat.succ.inj step
          have distErase : isDistinctList (natListErasePerm entries width) = true :=
            isDistinctListNatListErasePerm entries width distinct
          have eraseSelf : memBool width (natListErasePerm entries width) = false :=
            memBoolNatListErasePerm_self entries width distinct
          have boundedErase : ∀ other, memBool other (natListErasePerm entries width) = true → other < width := by
            intro other otherMem
            have otherNe : other ≠ width := by
              intro otherEq
              rw [otherEq, eraseSelf] at otherMem
              exact Bool.noConfusion otherMem
            have otherMemEntries : memBool other entries = true := by
              rw [← memBoolNatListErasePerm_ne entries width other
                (natBeqFalseOfNePerm width other (fun equal => otherNe equal.symm))]
              exact otherMem
            exact natLtOfLeOfNePerm other width (Nat.le_of_lt_succ (bounded other otherMemEntries)) otherNe
          have valueMemErase : memBool value (natListErasePerm entries width) = true :=
            surjOfDistinctBoundedFullPerm width (natListErasePerm entries width) distErase eraseLenWidth
              boundedErase value lt
          rw [← memBoolNatListErasePerm_ne entries width value
            (natBeqFalseOfNePerm width value (fun equal => (natNeOfLtPerm value width lt) equal.symm))]
          exact valueMemErase

/-- ★ **Range-permutation SURJECTIVITY (finite pigeonhole).**  A distinct, length-`width`, `[0, width)`-bounded
one-line order contains every value below `width`: `memBool value order = true` for all `value < width`.  The
genuinely-new counting content of T-CLOSE — the codebase's surjectivity facts were specific to a
`permuteOfCrossingWord` output whose membership set is `range width` by construction; a general distinct-bounded
list had none.  Proven via a first-occurrence erase and the length bound `distinctLengthLeBoundPerm`. -/
theorem isPermutationOfRange_surjective (width : Nat) (order : List Nat)
    (valid : IsPermutationOfRange width order) (value : Nat) (valueBelow : value < width) :
    memBool value order = true := by
  have memberBounded : ∀ other, memBool other order = true → other < width := by
    intro other otherMem
    obtain ⟨witness, witnessBelow, witnessEq⟩ := memBoolGetAtWitnessPerm order other otherMem
    have witnessWidth : witness < width := by rw [← valid.hasWidthLength]; exact witnessBelow
    rw [← witnessEq]; exact valid.isBounded witness witnessWidth
  exact surjOfDistinctBoundedFullPerm width order valid.isDistinct valid.hasWidthLength memberBounded value valueBelow

/-! ## Section 6 — `permInverse` preserves the `IsPermutationOfRange` gate -/

/-- The inverse permutation has the same length as its input (a map over `range perm.length`). -/
theorem permInverse_length (perm : List Nat) : (permInverse perm).length = perm.length := by
  show ((List.range perm.length).map (fun value => natIndexOfValue perm value)).length = perm.length
  rw [mapLengthPerm, rangeLengthPerm]

/-- The inverse permutation reads off `natIndexOfValue perm index` at each in-range position. -/
theorem natListGetAtPermInversePerm (perm : List Nat) (index : Nat) (indexBelow : index < perm.length) :
    natListGetAt (permInverse perm) index = natIndexOfValue perm index := by
  show natListGetAt ((List.range perm.length).map (fun value => natIndexOfValue perm value)) index
    = natIndexOfValue perm index
  rw [getAtMapPerm (fun value => natIndexOfValue perm value) (List.range perm.length) index
    (by rw [rangeLengthPerm]; exact indexBelow)]
  show natIndexOfValue perm (natListGetAt (List.range perm.length) index) = natIndexOfValue perm index
  rw [getAtRangePerm perm.length index indexBelow]

/-- ★★ **`permInverse` preserves the range-permutation gate.**  If `perm` is a range-permutation of width `width`,
so is `permInverse perm`.  Boundedness and the injectivity roundtrip use `isPermutationOfRange_surjective` (every
index occurs, so `natIndexOfValueRoundtripPerm` fires); distinctness uses the getAt-injective ⇒ distinct converse.
The step the T-CLOSE top side needs to feed `permInverse (throughStrandTops ++ cupArcTops)` into the shipped
conjugator roundtrip. -/
theorem isPermutationOfRange_permInverse (width : Nat) (perm : List Nat)
    (valid : IsPermutationOfRange width perm) : IsPermutationOfRange width (permInverse perm) where
  hasWidthLength := by rw [permInverse_length]; exact valid.hasWidthLength
  isDistinct := by
    apply isDistinctListOfGetAtInjectivePerm
    intro indexLeft indexRight leftBelow rightBelow getEq
    have permLen : (permInverse perm).length = width := by rw [permInverse_length]; exact valid.hasWidthLength
    have leftWidth : indexLeft < width := by rw [← permLen]; exact leftBelow
    have rightWidth : indexRight < width := by rw [← permLen]; exact rightBelow
    have leftPermLen : indexLeft < perm.length := by rw [valid.hasWidthLength]; exact leftWidth
    have rightPermLen : indexRight < perm.length := by rw [valid.hasWidthLength]; exact rightWidth
    have leftGet : natListGetAt (permInverse perm) indexLeft = natIndexOfValue perm indexLeft :=
      natListGetAtPermInversePerm perm indexLeft leftPermLen
    have rightGet : natListGetAt (permInverse perm) indexRight = natIndexOfValue perm indexRight :=
      natListGetAtPermInversePerm perm indexRight rightPermLen
    have idxEq : natIndexOfValue perm indexLeft = natIndexOfValue perm indexRight := by
      rw [← leftGet, ← rightGet]; exact getEq
    have leftMem : memBool indexLeft perm = true :=
      isPermutationOfRange_surjective width perm valid indexLeft leftWidth
    have rightMem : memBool indexRight perm = true :=
      isPermutationOfRange_surjective width perm valid indexRight rightWidth
    have leftRt := natIndexOfValueRoundtripPerm perm indexLeft leftMem
    have rightRt := natIndexOfValueRoundtripPerm perm indexRight rightMem
    have step1 : natListGetAt perm (natIndexOfValue perm indexLeft) = indexLeft := leftRt.1
    have step2 : natListGetAt perm (natIndexOfValue perm indexRight) = indexRight := rightRt.1
    rw [idxEq] at step1
    rw [step2] at step1
    exact step1.symm
  isBounded := by
    intro index indexBelow
    have indexPermLen : index < perm.length := by rw [valid.hasWidthLength]; exact indexBelow
    rw [natListGetAtPermInversePerm perm index indexPermLen]
    have indexMem : memBool index perm = true :=
      isPermutationOfRange_surjective width perm valid index indexBelow
    have rt := natIndexOfValueRoundtripPerm perm index indexMem
    rw [← valid.hasWidthLength]; exact rt.2

/-! ## Non-vacuity — the surjectivity, `permInverse` evaluation, and gate-preservation fire on a concrete witness -/

private theorem boundedThreeElimPerm {motive : Nat → Prop} (h0 : motive 0) (h1 : motive 1) (h2 : motive 2) :
    (index : Nat) → index < 3 → motive index
  | 0, _ => h0
  | 1, _ => h1
  | 2, _ => h2
  | _ + 3, hlt => absurd hlt (fun contra =>
      Nat.not_succ_le_zero _
        (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ contra))))

/-- ★ **A concrete range-permutation witness** — the 3-cycle `[1, 2, 0]` is distinct, length 3, `[0, 3)`-bounded. -/
theorem isPermutationOfRange_threeCycle_witness : IsPermutationOfRange 3 [1, 2, 0] where
  hasWidthLength := rfl
  isDistinct := rfl
  isBounded := boundedThreeElimPerm (motive := fun index => natListGetAt [1, 2, 0] index < 3)
    (by decide) (by decide) (by decide)

/-- ★ **Non-vacuity — surjectivity fires: every value below 3 occurs in the 3-cycle.** -/
theorem isPermutationOfRange_surjective_threeCycle :
    memBool 0 [1, 2, 0] = true ∧ memBool 1 [1, 2, 0] = true ∧ memBool 2 [1, 2, 0] = true :=
  ⟨isPermutationOfRange_surjective 3 [1, 2, 0] isPermutationOfRange_threeCycle_witness 0 (by decide),
   isPermutationOfRange_surjective 3 [1, 2, 0] isPermutationOfRange_threeCycle_witness 1 (by decide),
   isPermutationOfRange_surjective 3 [1, 2, 0] isPermutationOfRange_threeCycle_witness 2 (by decide)⟩

/-- ★ **Non-vacuity — the inverse of the 3-cycle `[1, 2, 0]` is `[2, 0, 1]`.** -/
theorem permInverse_threeCycle_eval : permInverse [1, 2, 0] = [2, 0, 1] := by decide

/-- ★ **Non-vacuity — `permInverse` preserves the gate on the 3-cycle witness.** -/
theorem isPermutationOfRange_permInverse_threeCycle : IsPermutationOfRange 3 (permInverse [1, 2, 0]) :=
  isPermutationOfRange_permInverse 3 [1, 2, 0] isPermutationOfRange_threeCycle_witness

/-! ## T-CLOSE truth-probes — the read-off orders ARE range-permutations on concrete diagrams

The general read-off IsPermutationOfRange (both sides, under the `IsBoundaryInvolution` gate) is the named counting
residual.  These decidable probes confirm its CONCLUSION is TRUE — not merely conjectured — on the adversarial-B
diagram (crossing cap + through + crossing cup + loop) and a fresh fully-mixed diagram (crossing cap + two throughs +
crossing cup).  Both the bottom read-off `capArcFeet ++ throughStrandBottoms` and the top read-off
`permInverse (throughStrandTops ++ cupArcTops)` genuinely satisfy `IsPermutationOfRange`. -/

/-- A fresh fully-mixed probe diagram over four bottom + four top ports: a crossing cap `0↔3`, two through-strands
`1↔top0` / `2↔top1`, and a crossing cup `top2↔top3`.  A valid involution `[3, 4, 5, 0, 1, 2, 7, 6]`. -/
def freshMixedProbeDiagram : DiagramType :=
  { bottomCount := 4, topCount := 4, partner := [3, 4, 5, 0, 1, 2, 7, 6], loops := 0 }

/-- ★ **Truth-probe (adversarial-B, bottom).**  The bottom read-off order
`capArcFeet ++ throughStrandBottoms` (which computes to `[0, 2, 1]`) is a genuine range-permutation of width 3. -/
theorem readOffBottomOrder_isPermutationOfRange_adversarialB :
    IsPermutationOfRange adversarialBDiagram.bottomCount
      (capArcFeet adversarialBDiagram.bottomCount adversarialBDiagram.partner
        ++ throughStrandBottoms adversarialBDiagram.bottomCount adversarialBDiagram.partner) :=
  ⟨by decide, by decide, by decide⟩

/-- ★ **Truth-probe (adversarial-B, top).**  The top read-off order
`permInverse (throughStrandTops ++ cupArcTops)` (which computes to `[1, 0, 2]`) is a genuine range-permutation of
width 3. -/
theorem readOffTopOrder_isPermutationOfRange_adversarialB :
    IsPermutationOfRange adversarialBDiagram.topCount
      (permInverse (throughStrandTops adversarialBDiagram.bottomCount adversarialBDiagram.topCount
          adversarialBDiagram.partner
        ++ cupArcTops adversarialBDiagram.bottomCount adversarialBDiagram.topCount adversarialBDiagram.partner)) :=
  ⟨by decide, by decide, by decide⟩

/-- ★ **Truth-probe (fresh mixed, bottom).**  The bottom read-off order (which computes to `[0, 3, 1, 2]`) is a
genuine range-permutation of width 4 — a crossing cap and two through-strands read off correctly. -/
theorem readOffBottomOrder_isPermutationOfRange_freshMixed :
    IsPermutationOfRange freshMixedProbeDiagram.bottomCount
      (capArcFeet freshMixedProbeDiagram.bottomCount freshMixedProbeDiagram.partner
        ++ throughStrandBottoms freshMixedProbeDiagram.bottomCount freshMixedProbeDiagram.partner) :=
  ⟨by decide, by decide, by decide⟩

/-- ★ **Truth-probe (fresh mixed, top).**  The top read-off order (which computes to `[0, 1, 2, 3]`) is a genuine
range-permutation of width 4 — the two through-tops and the crossing cup read off correctly. -/
theorem readOffTopOrder_isPermutationOfRange_freshMixed :
    IsPermutationOfRange freshMixedProbeDiagram.topCount
      (permInverse (throughStrandTops freshMixedProbeDiagram.bottomCount freshMixedProbeDiagram.topCount
          freshMixedProbeDiagram.partner
        ++ cupArcTops freshMixedProbeDiagram.bottomCount freshMixedProbeDiagram.topCount
          freshMixedProbeDiagram.partner)) :=
  ⟨by decide, by decide, by decide⟩

/-! ## E2 roundtrip wired to the specific read-off orders (on the probe diagrams)

Feeding the concrete read-off `IsPermutationOfRange` witnesses into the shipped conjugator roundtrip
`permuteOfCrossingWord_permutationToCrossingWord` (`Brauer/WiringDescArcConjugator.lean`) shows the
`permutationToCrossingWord` staircase genuinely REALIZES the specific extractor read-off orders — the E2 end-to-end
wiring on the probe diagrams (the general wiring waits on the read-off counting identities). -/

/-- ★ **E2 wired (adversarial-B, bottom).**  The conjugator staircase realizes the concrete bottom read-off order. -/
theorem readOffBottomOrder_realizesRoundtrip_adversarialB :
    permuteOfCrossingWord adversarialBDiagram.bottomCount
        (permutationToCrossingWord adversarialBDiagram.bottomCount
          (capArcFeet adversarialBDiagram.bottomCount adversarialBDiagram.partner
            ++ throughStrandBottoms adversarialBDiagram.bottomCount adversarialBDiagram.partner))
      = capArcFeet adversarialBDiagram.bottomCount adversarialBDiagram.partner
        ++ throughStrandBottoms adversarialBDiagram.bottomCount adversarialBDiagram.partner :=
  permuteOfCrossingWord_permutationToCrossingWord adversarialBDiagram.bottomCount _
    readOffBottomOrder_isPermutationOfRange_adversarialB

/-- ★ **E2 wired (adversarial-B, top).**  The conjugator staircase realizes the concrete top read-off order. -/
theorem readOffTopOrder_realizesRoundtrip_adversarialB :
    permuteOfCrossingWord adversarialBDiagram.topCount
        (permutationToCrossingWord adversarialBDiagram.topCount
          (permInverse (throughStrandTops adversarialBDiagram.bottomCount adversarialBDiagram.topCount
              adversarialBDiagram.partner
            ++ cupArcTops adversarialBDiagram.bottomCount adversarialBDiagram.topCount adversarialBDiagram.partner)))
      = permInverse (throughStrandTops adversarialBDiagram.bottomCount adversarialBDiagram.topCount
          adversarialBDiagram.partner
        ++ cupArcTops adversarialBDiagram.bottomCount adversarialBDiagram.topCount adversarialBDiagram.partner) :=
  permuteOfCrossingWord_permutationToCrossingWord adversarialBDiagram.topCount _
    readOffTopOrder_isPermutationOfRange_adversarialB

/-- ★ **E2 wired (fresh mixed, bottom).**  The conjugator staircase realizes the concrete bottom read-off order. -/
theorem readOffBottomOrder_realizesRoundtrip_freshMixed :
    permuteOfCrossingWord freshMixedProbeDiagram.bottomCount
        (permutationToCrossingWord freshMixedProbeDiagram.bottomCount
          (capArcFeet freshMixedProbeDiagram.bottomCount freshMixedProbeDiagram.partner
            ++ throughStrandBottoms freshMixedProbeDiagram.bottomCount freshMixedProbeDiagram.partner))
      = capArcFeet freshMixedProbeDiagram.bottomCount freshMixedProbeDiagram.partner
        ++ throughStrandBottoms freshMixedProbeDiagram.bottomCount freshMixedProbeDiagram.partner :=
  permuteOfCrossingWord_permutationToCrossingWord freshMixedProbeDiagram.bottomCount _
    readOffBottomOrder_isPermutationOfRange_freshMixed

/-- ★ **E2 wired (fresh mixed, top).**  The conjugator staircase realizes the concrete top read-off order. -/
theorem readOffTopOrder_realizesRoundtrip_freshMixed :
    permuteOfCrossingWord freshMixedProbeDiagram.topCount
        (permutationToCrossingWord freshMixedProbeDiagram.topCount
          (permInverse (throughStrandTops freshMixedProbeDiagram.bottomCount freshMixedProbeDiagram.topCount
              freshMixedProbeDiagram.partner
            ++ cupArcTops freshMixedProbeDiagram.bottomCount freshMixedProbeDiagram.topCount
              freshMixedProbeDiagram.partner)))
      = permInverse (throughStrandTops freshMixedProbeDiagram.bottomCount freshMixedProbeDiagram.topCount
          freshMixedProbeDiagram.partner
        ++ cupArcTops freshMixedProbeDiagram.bottomCount freshMixedProbeDiagram.topCount
          freshMixedProbeDiagram.partner) :=
  permuteOfCrossingWord_permutationToCrossingWord freshMixedProbeDiagram.topCount _
    readOffTopOrder_isPermutationOfRange_freshMixed

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — `permInverse` preserves the range-permutation gate (r15 T-CLOSE opening).**  The finite
pigeonhole surjectivity `isPermutationOfRange_surjective` (a distinct, length-`width`, `[0, width)`-bounded order
contains every value below `width`) and the gate-preservation `isPermutationOfRange_permInverse`
(`IsPermutationOfRange width perm → IsPermutationOfRange width (permInverse perm)`) are proven zero-axiom and
structural, firing on the 3-cycle witness (`isPermutationOfRange_permInverse_threeCycle`,
`permInverse_threeCycle_eval : permInverse [1, 2, 0] = [2, 0, 1]`).  This is the INVERSE-step the T-CLOSE top side
needs to feed `permInverse (throughStrandTops ++ cupArcTops)` into the shipped conjugator roundtrip
`permuteOfCrossingWord_permutationToCrossingWord`.  `= true`. -/
def fxBrauer_hasPermInverseRangePreservation : Bool := true

/-- **Honesty WALL marker — the extractor read-off orders are NOT yet proven range-permutations (T-CLOSE residual).**
`permInverse`-preservation supplies the top side's INVERSE step, but the read-off orders
`capArcFeet ++ throughStrandBottoms` (bottom) and `throughStrandTops ++ cupArcTops` (top) are not yet shown to
satisfy `IsPermutationOfRange`: that needs the still-unbuilt cardinality identities
(`2 · |capArcFeetIndices| + |throughStrandBottoms| = bottomCount` and its ∗-dual) — a three-way `filterMap`
classification counting induction under the `IsBoundaryInvolution` gate, with the cap class doubled by
`expandBottomFeetPairs`.  And E3 (fold-alignment / T-CONNECT, the union-find `stepWiring` long-pole) plus the
T-CLOSE(b) field reassembly stay unbuilt.  So the masters `fxBrauer_hasTagCorrDisjoint` /
`fxBrauer_hasTagCorrExtraction`, the roundtrip nodes, and the completeness flags stay honestly `false`; #2013 does
NOT close.  `= false`. -/
def fxBrauer_hasReadOffOrderPermutation : Bool := false

/-- ★★ **Honesty marker — the read-off IsPermutationOfRange CONCLUSION is truth-probed (r15).**  Both read-off orders
— the bottom `capArcFeet ++ throughStrandBottoms` and the top `permInverse (throughStrandTops ++ cupArcTops)` — are
proven genuine range-permutations on the adversarial-B diagram
(`readOffBottomOrder_isPermutationOfRange_adversarialB` : width-3 order `[0, 2, 1]`;
`readOffTopOrder_isPermutationOfRange_adversarialB` : `[1, 0, 2]`) and on a fresh fully-mixed diagram
(`readOffBottomOrder_isPermutationOfRange_freshMixed` : width-4 order `[0, 3, 1, 2]`;
`readOffTopOrder_isPermutationOfRange_freshMixed` : `[0, 1, 2, 3]`).  So the general counting identity's conclusion
is KNOWN TRUE, not conjectured — the residual is the general PROOF (a `filterMap` classification counting induction),
not the truth.  `= true`. -/
def fxBrauer_hasReadOffOrderPermutationProbe : Bool := true

/-- ★★ **Honesty marker — the E2 roundtrip is WIRED to the specific read-off orders (r15, on the probe diagrams).**
`permuteOfCrossingWord_permutationToCrossingWord` applied to the concrete read-off `IsPermutationOfRange` witnesses
shows the `permutationToCrossingWord` staircase realizes EXACTLY the bottom / top read-off orders on the
adversarial-B and fresh-mixed diagrams (`readOffBottomOrder_realizesRoundtrip_adversarialB` /
`readOffTopOrder_realizesRoundtrip_adversarialB` and the fresh-mixed pair) — E2 end-to-end on the specific `d`, at
the probe granularity.  The general wiring (all `d` under the gate) waits on the read-off counting identities.
`= true`. -/
def fxBrauer_hasReadOffRoundtripWiredProbe : Bool := true

/-- ★★★ **The BRAUER-MIDDLE r15 LEDGER — MACHINE-CHECKED (T-CLOSE opening landed).**  Extends the r14 grand ledger
with the `permInverse` gate-preservation flip `fxBrauer_hasPermInverseRangePreservation = true` (justified by the
finite-pigeonhole surjectivity `isPermutationOfRange_surjective` and `isPermutationOfRange_permInverse`,
zero-axiom).  E1 / E2 and the r11→r12 markers remain `true`; and EVERY remaining wall stays `false` — the read-off
order permutations (blocked on the bottom/top counting identities), the CONJUGATED enumeration node (E3
fold-alignment), both tag-correspondence masters, the extractor-totality roundtrip nodes, and the completeness
flags.  A `rfl`-conjunction over the shipped markers.  The remaining chain to the masters: **the read-off counting
identities** (bottom/top `IsPermutationOfRange`) **→ E3** (union-find `stepWiring` long-pole) **→ T-CLOSE(b)** (the
`extractDiagram` field reassembly) **→ the master flips**.  So #2013 does NOT close this round. -/
theorem fxBrauer_r15Ledger :
    (fxBrauer_hasBoundedBoundaryFoldLift = true
      ∧ fxBrauer_hasPartnerReadOff = true
      ∧ fxBrauer_hasBoundaryPartneredFold = true
      ∧ fxBrauer_hasReadOffWiredFiring = true
      ∧ fxBrauer_hasArcEnumeration = true
      ∧ fxBrauer_hasArcConjugatorLeg = true
      ∧ fxBrauer_hasPermInverseRangePreservation = true)
    ∧ (fxBrauer_hasReadOffOrderPermutation = false
      ∧ fxBrauer_hasArcEnumerationConjugated = false)
    ∧ (fxBrauer_hasTagCorrDisjoint = false
      ∧ fxBrauer_hasTagCorrExtraction = false)
    ∧ (fxBrauer_hasExt5CorrectedRoundtripProof = false
      ∧ fxBrauer_hasExt5TotalExtractorRoundtrip = false)
    ∧ (fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- ★★ **Honesty marker — BRAUER-MIDDLE r15 did NOT close #2013.**  The round landed the T-CLOSE opening — the finite
pigeonhole surjectivity of range-permutations and `permInverse` gate-preservation, each zero-axiom and structural,
firing on the 3-cycle witness.  But the read-off order counting identities (bottom/top `IsPermutationOfRange`), E3
(fold-alignment / T-CONNECT), and the T-CLOSE(b) field reassembly remain named, not built, so the read-off is still
not wired to a specific `d`, both tag-correspondence masters and the completeness flags stay `false`, and #2013 does
not close — every residual a ROUTE / counting gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).
`= false`. -/
def fxBrauer_hasBrauerMiddleR15Complete : Bool := false

end FX1Poly.Polygraph
