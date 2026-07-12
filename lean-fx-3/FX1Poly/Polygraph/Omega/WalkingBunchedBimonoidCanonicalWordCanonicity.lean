import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordStaircase

/-! # Polygraph/Omega/WalkingBunchedBimonoidCanonicalWordCanonicity — the recursive-comb STAIRCASE CANONICITY:
equal permutations reach equal recursive-comb staircases (WP-PROP r18, goal-chain item 2 of `CoxeterWordUnique`)

★ **THE r18 CANONICITY LEG — the Omega mirror of the Brauer `combCanonicity`, the pure `List Nat` node
`permOfWord w1 = permOfWord w2 -> recComb (W-1) w1 = recComb (W-1) w2`.**  The base staircase file (C0+C1) shipped
the DATA engine (`bunchedBimonoidRecComb`) and its DATA-level soundness leg
(`bunchedBimonoidCombNormalizeFormPreservesPerm`: one comb level preserves the through-strand permutation).  This
file lands the CANONICITY: two in-range words with the SAME through-strand permutation have the SAME recursive-comb
staircase.  Structural induction on the generator count reading the top-strand run length off the permutation — the
STRAND PIN (`bunchedBimonoidPermTopIndexOfPrefixRun` + `bunchedBimonoidNatSubInjCanon`) — then stripping the top
strand (`bunchedBimonoidFoldlSwapInjective` / `bunchedBimonoidSnocInjectiveCanon`) to feed the level-below induction
hypothesis.  This is the section property of the Regev–Roichman canonical presentation: the recursive-comb staircase
is determined by the permutation (Matsumoto for `S_n`; Björner–Brenti Prop. 2.4.4).

All PURE `List Nat` over the shipped Omega symmetric-group engine (`bunchedBimonoidApplyAdjacentSwap` /
`bunchedBimonoidPermOfWord`).  ZERO CONV: no cell / `SaturatedConvOver` layer touched.  The two new engine primitives
`bunchedBimonoidNatIndexOfValue` (first-occurrence index) and `bunchedBimonoidMemBool` (boolean membership) are the
port surface the base file did not yet carry; everything else reuses the base staircase publics.  Mirror of the
Brauer canonicity lane (`WiringDescStaircaseCanonical`); never imported from it (mirror = per-file clones).

## What this round is NOT (the honest scope)

This is the pure-permutation CANONICITY leg, NOT the CONV-fold.  The `recCombConv`-over-cells lift (the whole-word
`BrauerConvFree7` straightening mirror) stays gated on the three whisker-coherence residuals
(`WalkingBunchedBimonoidCanonicalWordRunCommuteConv`, r17 wall); this file does not touch that wall.  The star does
NOT flip: no hypothesis-free inhabitant of `bunchedBimonoidStarStatementAdditiveWellTyped` is produced, and every
star / residual marker stays byte-intact.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent `#print axioms`
gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

/-! The width-4/5 permutation round-trip `rfl` pins inherit the base staircase heartbeat budget; the raise is a
compute allowance only, the proof terms stay `Eq.refl` / structural, axiom-free. -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # P0 — THE TWO ENGINE PRIMITIVES the canonicity strand-pin reads (natIndexOfValue + memBool)
    # =========================================================================================

★ Verbatim ports (renamed into the Omega namespace) of the Brauer `natIndexOfValue` / `memBool` /
`memBool_applyAdjacentSwap`, over the SHIPPED Omega symmetric-group engine.  Both `propext`-free full-enum matches. -/

/-- ★ **Boolean membership in a `Nat` list** — full-enum `Nat.beq` fold, `propext`-free (unlike `List.elem`). -/
def bunchedBimonoidMemBool (value : Nat) : List Nat → Bool
  | [] => false
  | head :: rest => Nat.beq head value || bunchedBimonoidMemBool value rest

/-- ★ **The 0-based index of the first occurrence of `target`** (`0` if absent — for a genuine permutation every
value in `[0, width)` occurs, so the fallback is never taken).  Full-enum match on the `Bool` equality,
`propext`-free. -/
def bunchedBimonoidNatIndexOfValue : List Nat → Nat → Nat
  | [], _ => 0
  | head :: rest, target =>
      match head == target with
      | true => 0
      | false => bunchedBimonoidNatIndexOfValue rest target + 1

/-! # =========================================================================================
    # P0 — TRUTH-PROBES (the two primitives compute; run standalone BEFORE any proof)
    # =========================================================================================
-/

#eval bunchedBimonoidNatIndexOfValue [3, 1, 0, 2] 0   -- value 0 sits at index 2
#eval bunchedBimonoidNatIndexOfValue [3, 1, 0, 2] 2   -- value 2 sits at index 3
#eval bunchedBimonoidNatIndexOfValue [3, 1, 0, 2] 3   -- value 3 sits at index 0
#eval bunchedBimonoidMemBool 5 [3, 1, 0, 2]           -- 5 absent -> false
#eval bunchedBimonoidMemBool 2 [3, 1, 0, 2]           -- 2 present -> true

/-- Reassociate-and-commute a triple boolean disjunction — full-enum, `propext`-free. -/
private theorem bunchedBimonoidBoolOrLeftCommCanon (leftFlag midFlag rightFlag : Bool) :
    (leftFlag || (midFlag || rightFlag)) = (midFlag || (leftFlag || rightFlag)) := by
  cases leftFlag <;> cases midFlag <;> cases rightFlag <;> rfl

/-- ★ **Membership is invariant under an adjacent swap** — the swap only reorders two entries, so the multiset
(hence `memBool`) is unchanged.  Structural on the swap's own matcher. -/
theorem bunchedBimonoidMemBoolApplyAdjacentSwap : (value : Nat) → (perm : List Nat) → (position : Nat) →
    bunchedBimonoidMemBool value (bunchedBimonoidApplyAdjacentSwap perm position)
      = bunchedBimonoidMemBool value perm
  | _, [], _ => rfl
  | _, _ :: [], _ => rfl
  | value, first :: second :: rest, 0 =>
      bunchedBimonoidBoolOrLeftCommCanon (Nat.beq second value) (Nat.beq first value)
        (bunchedBimonoidMemBool value rest)
  | value, first :: second :: rest, position + 1 =>
      congrArg (Nat.beq first value || ·)
        (bunchedBimonoidMemBoolApplyAdjacentSwap value (second :: rest) position)

/-! # =========================================================================================
    # P1 — the `propext`-clean arithmetic / bool / range backbone (re-ported, `Canon`-suffixed)
    # =========================================================================================
-/

private theorem bunchedBimonoidPredSuccCanon : (index : Nat) → 1 ≤ index → index - 1 + 1 = index
  | 0, positive => absurd positive (by decide)
  | _ + 1, _ => rfl

private theorem bunchedBimonoidNatLePredCanon : (lower top : Nat) → lower + 1 ≤ top → lower ≤ top - 1
  | lower, 0, h => absurd h (Nat.not_succ_le_zero lower)
  | _, _ + 1, h => Nat.le_of_succ_le_succ h

private theorem bunchedBimonoidSubOneCommCanon : (top count : Nat) → top - count - 1 = top - 1 - count
  | _, 0 => rfl
  | top, count + 1 => congrArg Nat.pred (bunchedBimonoidSubOneCommCanon top count)

private theorem bunchedBimonoidBoolAndLeftCanon :
    (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → leftFlag = true
  | true, _, _ => rfl
  | false, _, conj => Bool.noConfusion conj

private theorem bunchedBimonoidBoolAndRightCanon :
    (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → rightFlag = true
  | true, _, conj => conj
  | false, _, conj => Bool.noConfusion conj

private theorem bunchedBimonoidBoolOrFalseLeftCanon :
    (leftFlag rightFlag : Bool) → (leftFlag || rightFlag) = false → leftFlag = false
  | false, _, _ => rfl
  | true, _, hFalse => Bool.noConfusion hFalse

private theorem bunchedBimonoidBoolOrFalseRightCanon :
    (leftFlag rightFlag : Bool) → (leftFlag || rightFlag) = false → rightFlag = false
  | false, _, hFalse => hFalse
  | true, _, hFalse => Bool.noConfusion hFalse

private theorem bunchedBimonoidNatBleOfLeCanon : (lower upper : Nat) → lower ≤ upper → Nat.ble lower upper = true
  | 0, _, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | lower + 1, upper + 1, h => bunchedBimonoidNatBleOfLeCanon lower upper (Nat.le_of_succ_le_succ h)

private theorem bunchedBimonoidNatLtOfBltCanon (lower upper : Nat) (h : Nat.blt lower upper = true) :
    lower < upper := by
  have hble : Nat.ble (lower + 1) upper = true := h
  clear h
  induction lower generalizing upper with
  | zero => cases upper with
    | zero => exact Bool.noConfusion hble
    | succ u => exact Nat.succ_le_succ (Nat.zero_le u)
  | succ l ih => cases upper with
    | zero => exact Bool.noConfusion hble
    | succ u => exact Nat.succ_le_succ (ih u hble)

private theorem bunchedBimonoidNatBeqFalseOfLtCanon : (lower upper : Nat) → lower < upper → Nat.beq lower upper = false
  | 0, 0, h => absurd h (Nat.lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | lower + 1, upper + 1, h => bunchedBimonoidNatBeqFalseOfLtCanon lower upper (Nat.lt_of_succ_lt_succ h)

private theorem bunchedBimonoidNatBeqSelfCanon : (n : Nat) → Nat.beq n n = true
  | 0 => rfl
  | n + 1 => bunchedBimonoidNatBeqSelfCanon n

/-- `(value == value) = true` — `Nat`'s `==` is `decide`-based, so `decide_eq_true rfl` closes it (`propext`-free). -/
private theorem bunchedBimonoidBeqSelfCanon (value : Nat) : (value == value) = true := decide_eq_true rfl

private theorem bunchedBimonoidAppendSnocConsCanon : (front rest : List Nat) → (value : Nat) →
    front ++ (value :: rest) = (front ++ [value]) ++ rest
  | [], _, _ => rfl
  | head :: tail, rest, value => congrArg (head :: ·) (bunchedBimonoidAppendSnocConsCanon tail rest value)

private theorem bunchedBimonoidRangeLoopAppendCanon : (count : Nat) → (accumulated : List Nat) →
    List.range.loop count accumulated = List.range.loop count [] ++ accumulated
  | 0, _ => rfl
  | count + 1, accumulated => by
      show List.range.loop count (count :: accumulated)
         = List.range.loop count (count :: []) ++ accumulated
      rw [bunchedBimonoidRangeLoopAppendCanon count (count :: accumulated),
          bunchedBimonoidRangeLoopAppendCanon count (count :: [])]
      exact bunchedBimonoidAppendSnocConsCanon (List.range.loop count []) accumulated count

/-- `List.range (n + 1) = List.range n ++ [n]` — the `propext`-free replacement for `List.range_succ`. -/
private theorem bunchedBimonoidRangeSuccCanon (n : Nat) : List.range (n + 1) = List.range n ++ [n] := by
  show List.range.loop n (n :: []) = List.range.loop n [] ++ [n]
  exact bunchedBimonoidRangeLoopAppendCanon n (n :: [])

/-! # =========================================================================================
    # P2 — R2.A: the strand pin (swap moves a value down, the descending run bubbles it, the prefix fixes the top)
    # =========================================================================================
-/

/-- The one-step `natIndexOfValue` unfold on a cons — `rfl`, driving the `Bool`-equality case splits without a
fragile inline `match` in `show`. -/
private theorem bunchedBimonoidNatIndexOfValueCons (head target : Nat) (rest : List Nat) :
    bunchedBimonoidNatIndexOfValue (head :: rest) target
      = (match head == target with | true => 0 | false => bunchedBimonoidNatIndexOfValue rest target + 1) := rfl

/-- ★ **A swap moves a value down one index** — if `value` sits at a genuine index `top + 1` of `perm`, then
`applyAdjacentSwap perm top` puts `value` at index `top`.  Structural on `(perm, top)`; the in-range index rules out
the fallback. -/
theorem bunchedBimonoidSwapMovesValueDown : (perm : List Nat) → (top : Nat) → (value : Nat) →
    bunchedBimonoidNatIndexOfValue perm value = top + 1 → top + 1 < perm.length →
    bunchedBimonoidNatIndexOfValue (bunchedBimonoidApplyAdjacentSwap perm top) value = top
  | [], top, value, hIdx, _ => Nat.noConfusion (show (0 : Nat) = top + 1 from hIdx)
  | [_], top, _, _, hbound => absurd (Nat.le_of_succ_le_succ hbound) (Nat.not_succ_le_zero top)
  | first :: second :: rest, 0, value, hIdx, _ => by
      rw [bunchedBimonoidNatIndexOfValueCons] at hIdx
      cases hfv : (first == value) with
      | true => rw [hfv] at hIdx; exact Nat.noConfusion hIdx
      | false =>
          rw [hfv] at hIdx
          have hSecond : bunchedBimonoidNatIndexOfValue (second :: rest) value = 0 := Nat.succ.inj hIdx
          rw [bunchedBimonoidNatIndexOfValueCons] at hSecond
          cases hsv : (second == value) with
          | true =>
              show bunchedBimonoidNatIndexOfValue (second :: first :: rest) value = 0
              rw [bunchedBimonoidNatIndexOfValueCons, hsv]
          | false => rw [hsv] at hSecond; exact Nat.noConfusion hSecond.symm
  | first :: second :: rest, top + 1, value, hIdx, hbound => by
      rw [bunchedBimonoidNatIndexOfValueCons] at hIdx
      cases hfv : (first == value) with
      | true => rw [hfv] at hIdx; exact Nat.noConfusion hIdx
      | false =>
          rw [hfv] at hIdx
          have hTail : bunchedBimonoidNatIndexOfValue (second :: rest) value = top + 1 := Nat.succ.inj hIdx
          have hboundTail : top + 1 < (second :: rest).length := Nat.lt_of_succ_lt_succ hbound
          have moved : bunchedBimonoidNatIndexOfValue (bunchedBimonoidApplyAdjacentSwap (second :: rest) top) value = top :=
            bunchedBimonoidSwapMovesValueDown (second :: rest) top value hTail hboundTail
          show bunchedBimonoidNatIndexOfValue (first :: bunchedBimonoidApplyAdjacentSwap (second :: rest) top) value = top + 1
          rw [bunchedBimonoidNatIndexOfValueCons, hfv, moved]

/-- ★ **The descending run bubbles the top value down by its length** — if `value` sits at index `index` of `perm`
(a genuine in-range index) and `count ≤ index`, folding the descending run `[index-1, …, index-count]` moves `value`
to index `index - count`.  Structural on `count`; each head swap `s_{index-1}` moves `value` one step down. -/
theorem bunchedBimonoidRunBubblesFromIndex : (index count : Nat) → (perm : List Nat) → (value : Nat) →
    bunchedBimonoidNatIndexOfValue perm value = index → index < perm.length → count ≤ index →
    bunchedBimonoidNatIndexOfValue
        ((bunchedBimonoidDescendingPositions (index - 1) count).foldl bunchedBimonoidApplyAdjacentSwap perm) value
      = index - count
  | index, 0, _, _, hIdx, _, _ => hIdx
  | index, count + 1, perm, value, hIdx, hbound, hk => by
      have idxPos : 1 ≤ index := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le count)) hk
      have idxPred : (index - 1) + 1 = index := bunchedBimonoidPredSuccCanon index idxPos
      have moved : bunchedBimonoidNatIndexOfValue (bunchedBimonoidApplyAdjacentSwap perm (index - 1)) value = index - 1 :=
        bunchedBimonoidSwapMovesValueDown perm (index - 1) value (idxPred ▸ hIdx) (idxPred ▸ hbound)
      show bunchedBimonoidNatIndexOfValue
          ((bunchedBimonoidDescendingPositions ((index - 1) - 1) count).foldl bunchedBimonoidApplyAdjacentSwap
            (bunchedBimonoidApplyAdjacentSwap perm (index - 1))) value = index - (count + 1)
      have ih := bunchedBimonoidRunBubblesFromIndex (index - 1) count (bunchedBimonoidApplyAdjacentSwap perm (index - 1)) value moved
        (by rw [bunchedBimonoidApplyAdjacentSwapLength perm (index - 1)]
            exact Nat.lt_of_le_of_lt (Nat.sub_le index 1) hbound)
        (bunchedBimonoidNatLePredCanon count index (idxPred ▸ hk))
      rw [ih]
      show (index - 1) - count = index - count - 1
      exact (bunchedBimonoidSubOneCommCanon index count).symm

/-- One `applyAdjacentSwap` on a snoc, when the swap window is inside the front, leaves the last element. -/
private theorem bunchedBimonoidApplyAdjacentSwapFixesLast : (front : List Nat) → (last : Nat) → (position : Nat) →
    position + 1 < front.length →
    bunchedBimonoidApplyAdjacentSwap (front ++ [last]) position
      = bunchedBimonoidApplyAdjacentSwap front position ++ [last]
  | [], _, position, h => absurd h (Nat.not_lt_zero (position + 1))
  | [_], _, position, h => absurd (Nat.le_of_succ_le_succ h) (Nat.not_succ_le_zero position)
  | _ :: _ :: _, _, 0, _ => rfl
  | first :: second :: rest, last, position + 1, h =>
      congrArg (first :: ·)
        (bunchedBimonoidApplyAdjacentSwapFixesLast (second :: rest) last position (Nat.lt_of_succ_lt_succ h))

/-- The fold of swaps whose positions are all `< bound` leaves the appended last element (`bound + 1 = front.length`
so the swaps never reach the last index). -/
private theorem bunchedBimonoidFoldlSwapFixesLast : (word : List Nat) → (front : List Nat) → (last : Nat) → (bound : Nat) →
    bunchedBimonoidMentionsOnlyBelow bound word = true → bound + 1 = front.length →
    word.foldl bunchedBimonoidApplyAdjacentSwap (front ++ [last])
      = word.foldl bunchedBimonoidApplyAdjacentSwap front ++ [last]
  | [], _, _, _, _, _ => rfl
  | position :: rest, front, last, bound, hRange, hLen => by
      have positionLt : position < bound :=
        bunchedBimonoidNatLtOfBltCanon position bound (bunchedBimonoidBoolAndLeftCanon _ _ hRange)
      have posP1LtLen : position + 1 < front.length := by rw [← hLen]; exact Nat.succ_lt_succ positionLt
      show rest.foldl bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidApplyAdjacentSwap (front ++ [last]) position)
         = rest.foldl bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidApplyAdjacentSwap front position) ++ [last]
      rw [bunchedBimonoidApplyAdjacentSwapFixesLast front last position posP1LtLen]
      exact bunchedBimonoidFoldlSwapFixesLast rest (bunchedBimonoidApplyAdjacentSwap front position) last bound
        (bunchedBimonoidBoolAndRightCanon _ _ hRange)
        (by rw [bunchedBimonoidApplyAdjacentSwapLength front position]; exact hLen)

/-- ★ **The prefix fixes the top strand.**  A word mentioning only positions `< bound` fixes strand `bound + 1`:
`permOfWord word (bound + 2) = permOfWord word (bound + 1) ++ [bound + 1]`. -/
theorem bunchedBimonoidPermExtendFixedTop (bound : Nat) (word : List Nat)
    (hBelow : bunchedBimonoidMentionsOnlyBelow bound word = true) :
    bunchedBimonoidPermOfWord word (bound + 2)
      = bunchedBimonoidPermOfWord word (bound + 1) ++ [bound + 1] := by
  show word.foldl bunchedBimonoidApplyAdjacentSwap (List.range (bound + 2))
     = word.foldl bunchedBimonoidApplyAdjacentSwap (List.range (bound + 1)) ++ [bound + 1]
  rw [show List.range (bound + 2) = List.range (bound + 1) ++ [bound + 1] from bunchedBimonoidRangeSuccCanon (bound + 1)]
  exact bunchedBimonoidFoldlSwapFixesLast word (List.range (bound + 1)) (bound + 1) bound hBelow
    (bunchedBimonoidRangeLength (bound + 1)).symm

/-! # =========================================================================================
    # P3 — R2.B: canonicity — equal permutations reach equal recursive-comb staircases
    # =========================================================================================
-/

/-- Bridge `Nat.beq` (the `memBool` spelling) to `==` (the `natIndexOfValue` `decide`-based spelling). -/
private theorem bunchedBimonoidBeqFalseOfNatBeqFalseCanon (leftValue rightValue : Nat)
    (h : Nat.beq leftValue rightValue = false) : (leftValue == rightValue) = false :=
  decide_eq_false (fun hEq => Bool.noConfusion
    (h.symm.trans ((congrArg (Nat.beq leftValue) hEq).symm.trans (bunchedBimonoidNatBeqSelfCanon leftValue))))

/-- Subtraction from a fixed `bound` is injective on the `≤ bound` interval — structural on `(bound, left, right)`,
`propext`-free (avoids the `propext`-leaking `Nat.sub_sub_self`). -/
private theorem bunchedBimonoidNatSubInjCanon : (bound left right : Nat) →
    bound - left = bound - right → left ≤ bound → right ≤ bound → left = right
  | 0, 0, 0, _, _, _ => rfl
  | 0, left + 1, _, _, hLeft, _ => absurd hLeft (Nat.not_succ_le_zero left)
  | 0, 0, right + 1, _, _, hRight => absurd hRight (Nat.not_succ_le_zero right)
  | _ + 1, 0, 0, _, _, _ => rfl
  | bound + 1, left + 1, 0, hEq, _, _ => by
      have hbad : bound - left = bound + 1 := (Nat.succ_sub_succ bound left).symm.trans hEq
      have hle : bound - left ≤ bound := Nat.sub_le bound left
      rw [hbad] at hle
      exact absurd hle (Nat.not_succ_le_self bound)
  | bound + 1, 0, right + 1, hEq, _, _ => by
      have hbad : bound + 1 = bound - right := hEq.trans (Nat.succ_sub_succ bound right)
      have hle : bound - right ≤ bound := Nat.sub_le bound right
      rw [← hbad] at hle
      exact absurd hle (Nat.not_succ_le_self bound)
  | bound + 1, left + 1, right + 1, hEq, hLeft, hRight =>
      congrArg Nat.succ (bunchedBimonoidNatSubInjCanon bound left right
        ((Nat.succ_sub_succ bound left).symm.trans (hEq.trans (Nat.succ_sub_succ bound right)))
        (Nat.le_of_succ_le_succ hLeft) (Nat.le_of_succ_le_succ hRight))

/-- The fold of adjacent swaps is injective — each swap is an involution (`applyAdjacentSwapInvolutive`). -/
private theorem bunchedBimonoidFoldlSwapInjective : (word : List Nat) → (leftPerm rightPerm : List Nat) →
    word.foldl bunchedBimonoidApplyAdjacentSwap leftPerm = word.foldl bunchedBimonoidApplyAdjacentSwap rightPerm →
    leftPerm = rightPerm
  | [], _, _, hEq => hEq
  | position :: rest, leftPerm, rightPerm, hEq => by
      have step : bunchedBimonoidApplyAdjacentSwap leftPerm position = bunchedBimonoidApplyAdjacentSwap rightPerm position :=
        bunchedBimonoidFoldlSwapInjective rest _ _ hEq
      have lifted : bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidApplyAdjacentSwap leftPerm position) position
                  = bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidApplyAdjacentSwap rightPerm position) position :=
        congrArg (bunchedBimonoidApplyAdjacentSwap · position) step
      rw [bunchedBimonoidApplyAdjacentSwapInvolutive leftPerm position,
          bunchedBimonoidApplyAdjacentSwapInvolutive rightPerm position] at lifted
      exact lifted

/-- A snoc is never nil. -/
private theorem bunchedBimonoidAppendSnocNeNilCanon : (front : List Nat) → (value : Nat) → front ++ [value] ≠ []
  | [], _ => fun hNil => nomatch hNil
  | _ :: _, _ => fun hNil => nomatch hNil

/-- A snoc of the SAME last element is left-cancellable — structural on both lists, `propext`-free. -/
private theorem bunchedBimonoidSnocInjectiveCanon : (leftList rightList : List Nat) → (value : Nat) →
    leftList ++ [value] = rightList ++ [value] → leftList = rightList
  | [], [], _, _ => rfl
  | [], _ :: rightTail, value, hEq => by
      injection hEq with _ hTail
      exact absurd hTail.symm (bunchedBimonoidAppendSnocNeNilCanon rightTail value)
  | _ :: leftTail, [], value, hEq => by
      injection hEq with _ hTail
      exact absurd hTail (bunchedBimonoidAppendSnocNeNilCanon leftTail value)
  | leftHead :: leftTail, rightHead :: rightTail, value, hEq => by
      injection hEq with hHead hTail
      exact hHead ▸ congrArg (leftHead :: ·) (bunchedBimonoidSnocInjectiveCanon leftTail rightTail value hTail)

/-- Membership is invariant under a fold of adjacent swaps (`memBoolApplyAdjacentSwap` at each step). -/
private theorem bunchedBimonoidMemBoolFoldlSwapCanon : (word : List Nat) → (init : List Nat) → (value : Nat) →
    bunchedBimonoidMemBool value (word.foldl bunchedBimonoidApplyAdjacentSwap init)
      = bunchedBimonoidMemBool value init
  | [], _, _ => rfl
  | position :: rest, init, value => by
      show bunchedBimonoidMemBool value (rest.foldl bunchedBimonoidApplyAdjacentSwap
              (bunchedBimonoidApplyAdjacentSwap init position)) = bunchedBimonoidMemBool value init
      rw [bunchedBimonoidMemBoolFoldlSwapCanon rest (bunchedBimonoidApplyAdjacentSwap init position) value,
          bunchedBimonoidMemBoolApplyAdjacentSwap value init position]

/-- The `range.loop` counter never contains a value at or above itself — the prepended block is `[count-1, …, 0]`. -/
private theorem bunchedBimonoidMemBoolRangeLoopGeCanon : (count : Nat) → (accumulated : List Nat) → (value : Nat) →
    count ≤ value → bunchedBimonoidMemBool value accumulated = false →
    bunchedBimonoidMemBool value (List.range.loop count accumulated) = false
  | 0, _, _, _, hAcc => hAcc
  | count + 1, accumulated, value, hLe, hAcc => by
      have countLt : count < value := hLe
      have hHead : bunchedBimonoidMemBool value (count :: accumulated) = false := by
        show (Nat.beq count value || bunchedBimonoidMemBool value accumulated) = false
        rw [bunchedBimonoidNatBeqFalseOfLtCanon count value countLt]
        exact hAcc
      exact bunchedBimonoidMemBoolRangeLoopGeCanon count (count :: accumulated) value (Nat.le_of_lt countLt) hHead

/-- `List.range bound` contains no value `≥ bound`. -/
private theorem bunchedBimonoidMemBoolRangeGeCanon (bound value : Nat) (hLe : bound ≤ value) :
    bunchedBimonoidMemBool value (List.range bound) = false :=
  bunchedBimonoidMemBoolRangeLoopGeCanon bound [] value hLe rfl

/-- `natIndexOfValue` of a value freshly snoc'd onto a list not already containing it is the front length. -/
private theorem bunchedBimonoidNatIndexOfValueSnocFreshCanon : (front : List Nat) → (value : Nat) →
    bunchedBimonoidMemBool value front = false →
    bunchedBimonoidNatIndexOfValue (front ++ [value]) value = front.length
  | [], value, _ => by
      show (match value == value with | true => 0 | false => bunchedBimonoidNatIndexOfValue [] value + 1) = 0
      rw [bunchedBimonoidBeqSelfCanon value]
  | head :: tail, value, hMem => by
      have parts : (Nat.beq head value || bunchedBimonoidMemBool value tail) = false := hMem
      have headFalse : (head == value) = false :=
        bunchedBimonoidBeqFalseOfNatBeqFalseCanon head value (bunchedBimonoidBoolOrFalseLeftCanon _ _ parts)
      have tailFalse : bunchedBimonoidMemBool value tail = false := bunchedBimonoidBoolOrFalseRightCanon _ _ parts
      show bunchedBimonoidNatIndexOfValue (head :: (tail ++ [value])) value = tail.length + 1
      rw [bunchedBimonoidNatIndexOfValueCons, headFalse,
          bunchedBimonoidNatIndexOfValueSnocFreshCanon tail value tailFalse]

/-- ★ **The top-strand pin.**  With `statePrefix` mentioning only positions `< generatorCount` and
`runLen ≤ generatorCount + 1`, the top strand `generatorCount + 1` lands at index `(generatorCount + 1) - runLen` in
the permutation of `statePrefix ++ descendingPositions generatorCount runLen`: the prefix fixes strand
`generatorCount + 1` (`permExtendFixedTop`) and the descending run bubbles it down (`runBubblesFromIndex`). -/
theorem bunchedBimonoidPermTopIndexOfPrefixRun (generatorCount runLen : Nat) (statePrefix : List Nat)
    (hBelow : bunchedBimonoidMentionsOnlyBelow generatorCount statePrefix = true) (hRun : runLen ≤ generatorCount + 1) :
    bunchedBimonoidNatIndexOfValue
        (bunchedBimonoidPermOfWord (statePrefix ++ bunchedBimonoidDescendingPositions generatorCount runLen)
          (generatorCount + 2))
        (generatorCount + 1)
      = (generatorCount + 1) - runLen := by
  have notMem : bunchedBimonoidMemBool (generatorCount + 1)
      (bunchedBimonoidPermOfWord statePrefix (generatorCount + 1)) = false := by
    show bunchedBimonoidMemBool (generatorCount + 1)
      (statePrefix.foldl bunchedBimonoidApplyAdjacentSwap (List.range (generatorCount + 1))) = false
    rw [bunchedBimonoidMemBoolFoldlSwapCanon statePrefix (List.range (generatorCount + 1)) (generatorCount + 1)]
    exact bunchedBimonoidMemBoolRangeGeCanon (generatorCount + 1) (generatorCount + 1) (Nat.le_refl _)
  have topAt : bunchedBimonoidNatIndexOfValue
      (bunchedBimonoidPermOfWord statePrefix (generatorCount + 2)) (generatorCount + 1) = generatorCount + 1 := by
    rw [bunchedBimonoidPermExtendFixedTop generatorCount statePrefix hBelow,
        bunchedBimonoidNatIndexOfValueSnocFreshCanon (bunchedBimonoidPermOfWord statePrefix (generatorCount + 1))
          (generatorCount + 1) notMem,
        bunchedBimonoidPermOfWordLength statePrefix (generatorCount + 1)]
  have lenBound : generatorCount + 1 < (bunchedBimonoidPermOfWord statePrefix (generatorCount + 2)).length := by
    rw [bunchedBimonoidPermOfWordLength statePrefix (generatorCount + 2)]
    exact Nat.lt_succ_self (generatorCount + 1)
  have bubbled := bunchedBimonoidRunBubblesFromIndex (generatorCount + 1) runLen
    (bunchedBimonoidPermOfWord statePrefix (generatorCount + 2)) (generatorCount + 1) topAt lenBound hRun
  rw [bunchedBimonoidPermOfWordAppendSplit (generatorCount + 2) statePrefix
    (bunchedBimonoidDescendingPositions generatorCount runLen)]
  exact bubbled

/-! # =========================================================================================
    # P4 — the DATA comb fold's final-state invariants (the `mentionsOnlyBelow` + run bound the pin reads)
    # =========================================================================================
-/

/-- ★ **The DATA comb fold preserves the state invariants.**  Folding `rest` (in range) onto a state whose prefix is
`mentionsOnlyBelow (gc-1)` and whose run is `≤ gc` yields a final prefix `mentionsOnlyBelow (gc-1)` and a final run
`≤ gc`.  Structural on `rest`, threading `bunchedBimonoidCombInsertPreservesInvariants`. -/
theorem bunchedBimonoidCombFoldInvariants (generatorCount : Nat) (genPos : 1 ≤ generatorCount) :
    (rest : List Nat) → (statePrefix : List Nat) → (stateRun : Nat) →
    bunchedBimonoidMentionsOnlyBelow (generatorCount - 1) statePrefix = true → stateRun ≤ generatorCount →
    bunchedBimonoidMentionsOnlyBelow generatorCount rest = true →
    bunchedBimonoidMentionsOnlyBelow (generatorCount - 1)
        (rest.foldl (bunchedBimonoidCombInsertData generatorCount) (statePrefix, stateRun)).1 = true
      ∧ (rest.foldl (bunchedBimonoidCombInsertData generatorCount) (statePrefix, stateRun)).2 ≤ generatorCount
  | [], statePrefix, stateRun, uBelow, runLe, _ => ⟨uBelow, runLe⟩
  | letter :: restTail, statePrefix, stateRun, uBelow, runLe, hRange => by
      have letterLt : letter < generatorCount :=
        bunchedBimonoidNatLtOfBltCanon letter generatorCount (bunchedBimonoidBoolAndLeftCanon _ _ hRange)
      obtain ⟨belowMid, runLeMid⟩ :=
        bunchedBimonoidCombInsertPreservesInvariants generatorCount genPos statePrefix stateRun uBelow runLe
          letter letterLt
      exact bunchedBimonoidCombFoldInvariants generatorCount genPos restTail
        (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).1
        (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).2 belowMid runLeMid
        (bunchedBimonoidBoolAndRightCanon _ _ hRange)

/-! # =========================================================================================
    # P5 — THE CANONICITY: equal permutations ⟹ equal recursive-comb staircases
    # =========================================================================================
-/

/-- ★★ **Canonicity: equal permutations ⟹ equal recursive-comb staircases.**  Structural on `generatorCount`.  Each
level reads the top run length off the permutation (`permTopIndexOfPrefixRun` + `natSubInjCanon`), then
`foldlSwap`/snoc injectivity strips the top strand to feed the `generatorCount`-level induction hypothesis.  The
section property of the Regev–Roichman canonical presentation: the recursive-comb staircase is determined by the
through-strand permutation — goal-chain item 2 of `CoxeterWordUnique`. -/
theorem bunchedBimonoidCombCanonicity : (generatorCount : Nat) → (word1 word2 : List Nat) →
    bunchedBimonoidMentionsOnlyBelow generatorCount word1 = true →
    bunchedBimonoidMentionsOnlyBelow generatorCount word2 = true →
    bunchedBimonoidPermOfWord word1 (generatorCount + 1) = bunchedBimonoidPermOfWord word2 (generatorCount + 1) →
    bunchedBimonoidRecComb generatorCount word1 = bunchedBimonoidRecComb generatorCount word2
  | 0, _, _, _, _, _ => rfl
  | generatorCount + 1, word1, word2, hRange1, hRange2, permEq => by
      have inv1 := bunchedBimonoidCombFoldInvariants (generatorCount + 1)
        (Nat.succ_le_succ (Nat.zero_le generatorCount)) word1 [] 0 rfl (Nat.zero_le (generatorCount + 1)) hRange1
      have inv2 := bunchedBimonoidCombFoldInvariants (generatorCount + 1)
        (Nat.succ_le_succ (Nat.zero_le generatorCount)) word2 [] 0 rfl (Nat.zero_le (generatorCount + 1)) hRange2
      have below1 := inv1.1
      have runLe1 := inv1.2
      have below2 := inv2.1
      have runLe2 := inv2.2
      have top1 := bunchedBimonoidPermTopIndexOfPrefixRun generatorCount
        (word1.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).2
        (word1.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).1 below1 runLe1
      have top2 := bunchedBimonoidPermTopIndexOfPrefixRun generatorCount
        (word2.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).2
        (word2.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).1 below2 runLe2
      have sound1 : bunchedBimonoidPermOfWord
          ((word1.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).1
            ++ bunchedBimonoidDescendingPositions generatorCount
                (word1.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).2)
          (generatorCount + 2)
          = bunchedBimonoidPermOfWord word1 (generatorCount + 2) :=
        bunchedBimonoidCombNormalizeFormPreservesPerm (generatorCount + 1)
          (Nat.succ_le_succ (Nat.zero_le generatorCount)) word1 hRange1
      have sound2 : bunchedBimonoidPermOfWord
          ((word2.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).1
            ++ bunchedBimonoidDescendingPositions generatorCount
                (word2.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).2)
          (generatorCount + 2)
          = bunchedBimonoidPermOfWord word2 (generatorCount + 2) :=
        bunchedBimonoidCombNormalizeFormPreservesPerm (generatorCount + 1)
          (Nat.succ_le_succ (Nat.zero_le generatorCount)) word2 hRange2
      rw [sound1] at top1
      rw [sound2] at top2
      have idxEq : (generatorCount + 1) - (word1.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).2
          = (generatorCount + 1) - (word2.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).2 := by
        rw [← top1, ← top2, permEq]
      have runEq : (word1.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).2
          = (word2.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).2 :=
        bunchedBimonoidNatSubInjCanon (generatorCount + 1) _ _ idxEq runLe1 runLe2
      have prefixPermEq : bunchedBimonoidPermOfWord
            (word1.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).1 (generatorCount + 2)
          = bunchedBimonoidPermOfWord
            (word2.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).1 (generatorCount + 2) := by
        apply bunchedBimonoidFoldlSwapInjective (bunchedBimonoidDescendingPositions generatorCount
          (word1.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).2)
        rw [← bunchedBimonoidPermOfWordAppendSplit, ← bunchedBimonoidPermOfWordAppendSplit,
          sound1, permEq, runEq, ← sound2]
      have prefixPermEqSmall : bunchedBimonoidPermOfWord
            (word1.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).1 (generatorCount + 1)
          = bunchedBimonoidPermOfWord
            (word2.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).1 (generatorCount + 1) := by
        apply bunchedBimonoidSnocInjectiveCanon _ _ (generatorCount + 1)
        rw [← bunchedBimonoidPermExtendFixedTop generatorCount _ below1,
            ← bunchedBimonoidPermExtendFixedTop generatorCount _ below2]
        exact prefixPermEq
      have ih := bunchedBimonoidCombCanonicity generatorCount
        (word1.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).1
        (word2.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).1 below1 below2 prefixPermEqSmall
      show bunchedBimonoidRecComb generatorCount
            (word1.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).1
            ++ bunchedBimonoidDescendingPositions generatorCount
                (word1.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).2
          = bunchedBimonoidRecComb generatorCount
            (word2.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).1
            ++ bunchedBimonoidDescendingPositions generatorCount
                (word2.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).2
      rw [ih, runEq]

/-! # =========================================================================================
    # P6 — non-vacuity fires (r14 data samples + fresh pairs) + the honesty marker
    # =========================================================================================

★ Canonicity fires on the r9 jam pair, the r11 residual pair, the r9 braid pair, and a fresh width-3 pair; each
input pair shares its through-strand permutation (`rfl`) and canonicity collapses both to the SAME recursive-comb
staircase.  A separated unequal-permutation pair witnesses the hypothesis is not vacuous. -/

/-- Non-vacuity — the r9 jam pair `[2,0,1,2]` / `[0,1,2,1]` (both realizing `[1,3,2,0]` on four strands) reaches the
SAME recursive-comb staircase: the exact standing jam the insertion route could not close, decided by canonicity. -/
theorem bunchedBimonoidCombCanonicity_r9 :
    bunchedBimonoidRecComb 3 [2, 0, 1, 2] = bunchedBimonoidRecComb 3 [0, 1, 2, 1] :=
  bunchedBimonoidCombCanonicity 3 [2, 0, 1, 2] [0, 1, 2, 1] rfl rfl rfl

/-- Non-vacuity — the r11 residual pair `[1,2,0,1,2]` / `[0,1,2,0,1]` (both realizing `[2,3,1,0,4]` on five strands)
reaches the SAME staircase — the one-level comb keeps them distinct, canonicity unifies them. -/
theorem bunchedBimonoidCombCanonicity_r11 :
    bunchedBimonoidRecComb 4 [1, 2, 0, 1, 2] = bunchedBimonoidRecComb 4 [0, 1, 2, 0, 1] :=
  bunchedBimonoidCombCanonicity 4 [1, 2, 0, 1, 2] [0, 1, 2, 0, 1] rfl rfl rfl

/-- Non-vacuity — the r9 braid pair `[0,1,0]` / `[1,0,1]` (both realizing the width-3 reversal `[2,1,0]`) reaches the
SAME staircase. -/
theorem bunchedBimonoidCombCanonicity_braidPair :
    bunchedBimonoidRecComb 2 [0, 1, 0] = bunchedBimonoidRecComb 2 [1, 0, 1] :=
  bunchedBimonoidCombCanonicity 2 [0, 1, 0] [1, 0, 1] rfl rfl rfl

/-- Non-vacuity (fresh pair) — a width-5 pair `[3,1,2,0,3,1]` / `[1,0,2,3,2,1]` (the second is the first's staircase)
sharing its permutation reaches the SAME staircase. -/
theorem bunchedBimonoidCombCanonicity_width5 :
    bunchedBimonoidRecComb 5 [3, 1, 2, 0, 3, 1] = bunchedBimonoidRecComb 5 [1, 0, 2, 3, 2, 1] :=
  bunchedBimonoidCombCanonicity 5 [3, 1, 2, 0, 3, 1] [1, 0, 2, 3, 2, 1] rfl rfl rfl

/-- Separation — an UNEQUAL-permutation pair is genuinely rejected by the hypothesis: `[0,1]` and `[1,0]` realize
different permutations on three strands (`[1,2,0]` vs `[2,0,1]`), so the perm-invariant hypothesis of
`bunchedBimonoidCombCanonicity` fails — the theorem is not vacuous. -/
theorem bunchedBimonoidCombCanonicity_unequalSeparated :
    bunchedBimonoidPermOfWord [0, 1] 3 ≠ bunchedBimonoidPermOfWord [1, 0] 3 := by
  intro hEq
  exact absurd hEq (by decide)

/-! ## The r18 canonicity honesty marker -/

/-- ★★★ **ESTABLISHED (r18) — the recursive-comb STAIRCASE CANONICITY is SHIPPED and zero-axiom.**  `= true` records
`bunchedBimonoidCombCanonicity`: two in-range words with the SAME through-strand permutation have the SAME
recursive-comb staircase, over the SHIPPED Omega symmetric-group engine.  Built on the two new engine primitives
(`bunchedBimonoidNatIndexOfValue`, `bunchedBimonoidMemBool`) + the strand-pin infrastructure
(`bunchedBimonoidSwapMovesValueDown` / `bunchedBimonoidRunBubblesFromIndex` / `bunchedBimonoidPermExtendFixedTop` /
`bunchedBimonoidPermTopIndexOfPrefixRun`) + the injectivity kit (`bunchedBimonoidFoldlSwapInjective` /
`bunchedBimonoidSnocInjectiveCanon` / `bunchedBimonoidNatSubInjCanon`) and the base staircase's DATA soundness
(`bunchedBimonoidCombNormalizeFormPreservesPerm`).  This is goal-chain item 2 of `CoxeterWordUnique`
(`permOfWord w1 = permOfWord w2 -> recComb (W-1) w1 = recComb (W-1) w2`).  Non-vacuous: it fires on the r9 jam pair,
the r11 residual pair, the r9 braid pair, and a fresh width-5 pair (`_r9` / `_r11` / `_braidPair` / `_width5`), and a
separated unequal-perm pair (`_unequalSeparated`) witnesses the hypothesis is genuine.  PURE `List Nat`, ZERO CONV —
the `recCombConv`-over-cells CONV lift stays gated on the r17 whisker-coherence wall (untouched here).  The four star
owners keep their name and `= false` value byte-intact (cross-file, not edited); NO fabricated star flip.  Zero-axiom
(per-decl `#assert_no_axioms` + independent `#print axioms` in the twin); STRUCTURAL only. -/
def fxBunchedBimonoid_hasRecursiveCombStaircaseCanonicity : Bool := true

end FX1Poly.Polygraph.Omega
