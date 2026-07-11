import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescThroughStrandPerm

/-! # BRAUER r27 — THE THROUGH-STRAND ROUNDTRIP CRUX: `arcMiddleCountBelow` inverts `natListGetAt` on the through bottoms

The THROUGH per-arc five-phase T-CONNECT (`Brauer/WiringDescTConnectThroughChain.lean`) closes its P1 seam (the seed
`bottomPerm` tracker landing the through wire on its bottom foot) with ONE rank ↔ position identity on the ascending,
distinct list `throughStrandBottoms`: reading it at the count-strictly-below-`value` rank reads back `value`.  Concretely
`r := throughStrandPerm[topRank] = arcMiddleCountBelow throughStrandBottoms i` (the middle permutation's payload is that
count), so P1's `throughStrandBottoms[r] = i` IS this roundtrip at `value := i`.

This is the direction-DUAL of the r26 rank ↔ position keystone (`natIndexOfValue order (natListGetAt order position) =
position`, `WiringDescRankPositionDuality.lean`): that keystone is value → position under `natIndexOfValue`; here we
need position → value under `arcMiddleCountBelow` (count-strictly-below).  The two agree only because the list is
STRICTLY ASCENDING — `arcMiddleCountBelow` counts the elements below a member, which on an ascending list is exactly
its position.  So the genuine new content is: (1) `throughStrandBottoms` is strictly ascending (a filterMap over
`List.range` keeps the strict ascent), and (2) on an ascending list, count-strictly-below reads back the value.

## What this file ships

  * `throughStrandBottoms_getAt_arcMiddleCountBelow` — for every `value ∈ throughStrandBottoms bottomCount partner`,
    `natListGetAt (throughStrandBottoms …) (arcMiddleCountBelow (throughStrandBottoms …) value) = value`.  THE crux.
  * the ascending infrastructure (`isAscendingListRT`, the filterMap-preserves-ascent lemma, `List.range` ascending)
    and the count-below-inverts-getAt roundtrip on an arbitrary ascending list, all private and structural.

Raw Lean 4 + Init; structural recursion, `Nat.blt` / `Nat.beq` full-enum kit re-derived propext-free (the shipped
`*Count` bridges are `private`), no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.  `decide` only on the
closed-literal firing probes.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Propext-free `Nat.ble` / `Nat.blt` / `Nat.beq` kit (private re-proofs of the shipped `*Count` bridges) -/

private theorem natBleTrueOfLeRT : (small large : Nat) → small ≤ large → Nat.ble small large = true
  | 0, _, _ => rfl
  | _ + 1, 0, le => absurd le (Nat.not_succ_le_zero _)
  | small + 1, large + 1, le => natBleTrueOfLeRT small large (Nat.le_of_succ_le_succ le)

private theorem natBleFalseOfGtRT : (small large : Nat) → large < small → Nat.ble small large = false
  | 0, large, gt => absurd gt (Nat.not_lt_zero large)
  | _ + 1, 0, _ => rfl
  | small + 1, large + 1, gt => natBleFalseOfGtRT small large (Nat.lt_of_succ_lt_succ gt)

private theorem natLeOfBleTrueRT : (small large : Nat) → Nat.ble small large = true → small ≤ large
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => Bool.noConfusion h
  | small + 1, large + 1, h => Nat.succ_le_succ (natLeOfBleTrueRT small large h)

private theorem natBltTrueOfLtRT (small large : Nat) (lt : small < large) : Nat.blt small large = true :=
  natBleTrueOfLeRT (small + 1) large lt

private theorem natBltFalseOfLeRT (small large : Nat) (le : large ≤ small) : Nat.blt small large = false :=
  natBleFalseOfGtRT (small + 1) large (Nat.lt_succ_of_le le)

private theorem natLtOfBltTrueRT (small large : Nat) (h : Nat.blt small large = true) : small < large :=
  natLeOfBleTrueRT (small + 1) large h

private theorem natEqOfBeqTrueRT : (a b : Nat) → Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => Bool.noConfusion h
  | _ + 1, 0, h => Bool.noConfusion h
  | a + 1, b + 1, h => congrArg (· + 1) (natEqOfBeqTrueRT a b h)

private theorem natBeqSelfTrueRT : (n : Nat) → Nat.beq n n = true
  | 0 => rfl
  | n + 1 => natBeqSelfTrueRT n

private theorem boolAndLeftRT : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → leftFlag = true
  | true, _, _ => rfl
  | false, _, h => Bool.noConfusion h

private theorem boolAndRightRT : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → rightFlag = true
  | true, true, _ => rfl
  | true, false, h => Bool.noConfusion h
  | false, _, h => Bool.noConfusion h

/-! ## `memBool` from membership (private re-proof) -/

private theorem memBoolTrueOfMemRT : (entries : List Nat) → (value : Nat) → value ∈ entries →
    memBool value entries = true
  | [], _, mem => by cases mem
  | head :: rest, value, mem => by
      cases mem with
      | head =>
          show (Nat.beq head head || memBool head rest) = true
          rw [natBeqSelfTrueRT head]; rfl
      | tail _ hr =>
          show (Nat.beq head value || memBool value rest) = true
          rw [memBoolTrueOfMemRT rest value hr]
          exact Bool.or_true _

/-! ## `List.filterMap` cons reductions (private re-proofs of the shipped `filterMapCons*Count`) -/

private theorem filterMapConsNoneRT (sel : Nat → Option Nat) (head : Nat) (rest : List Nat)
    (hnone : sel head = none) : (head :: rest).filterMap sel = rest.filterMap sel := by
  dsimp only [List.filterMap]; rw [hnone]

private theorem filterMapConsSomeRT (sel : Nat → Option Nat) (head picked : Nat) (rest : List Nat)
    (hsome : sel head = some picked) : (head :: rest).filterMap sel = picked :: rest.filterMap sel := by
  dsimp only [List.filterMap]; rw [hsome]

/-! ## The strict-ascending predicate + its preservation under filterMap-with-identity-payload -/

/-- Every entry of `entries` is strictly greater than `bound`. -/
private def natListAllAboveRT (bound : Nat) : List Nat → Bool
  | [] => true
  | head :: rest => Nat.blt bound head && natListAllAboveRT bound rest

/-- Every entry of `entries` is greater than or equal to `bound`. -/
private def natListAllAtLeastRT (bound : Nat) : List Nat → Bool
  | [] => true
  | head :: rest => Nat.ble bound head && natListAllAtLeastRT bound rest

/-- The list is strictly ascending: each head strictly below every later entry, and the tail ascending. -/
private def isAscendingListRT : List Nat → Bool
  | [] => true
  | head :: rest => natListAllAboveRT head rest && isAscendingListRT rest

/-- `natListAllAbove bound` is preserved by a filterMap whose selector returns the input element or `none`. -/
private theorem natListAllAboveRT_filterMap (sel : Nat → Option Nat)
    (selIdent : ∀ index picked, sel index = some picked → picked = index) (bound : Nat) :
    (base : List Nat) → natListAllAboveRT bound base = true →
    natListAllAboveRT bound (base.filterMap sel) = true
  | [], _ => rfl
  | head :: rest, hAll => by
      have hAll' : (Nat.blt bound head && natListAllAboveRT bound rest) = true := hAll
      have hbHead : Nat.blt bound head = true := boolAndLeftRT _ _ hAll'
      have hRest : natListAllAboveRT bound rest = true := boolAndRightRT _ _ hAll'
      cases hsel : sel head with
      | none =>
          rw [filterMapConsNoneRT sel head rest hsel]
          exact natListAllAboveRT_filterMap sel selIdent bound rest hRest
      | some picked =>
          have hpEq : picked = head := selIdent head picked hsel
          rw [filterMapConsSomeRT sel head picked rest hsel, hpEq]
          show (Nat.blt bound head && natListAllAboveRT bound (rest.filterMap sel)) = true
          rw [hbHead, natListAllAboveRT_filterMap sel selIdent bound rest hRest]; rfl

/-- Strict ascent is preserved by a filterMap whose selector returns the input element or `none`. -/
private theorem isAscendingListRT_filterMap (sel : Nat → Option Nat)
    (selIdent : ∀ index picked, sel index = some picked → picked = index) :
    (base : List Nat) → isAscendingListRT base = true →
    isAscendingListRT (base.filterMap sel) = true
  | [], _ => rfl
  | head :: rest, hAsc => by
      have hAsc' : (natListAllAboveRT head rest && isAscendingListRT rest) = true := hAsc
      have hAbove : natListAllAboveRT head rest = true := boolAndLeftRT _ _ hAsc'
      have hRestAsc : isAscendingListRT rest = true := boolAndRightRT _ _ hAsc'
      cases hsel : sel head with
      | none =>
          rw [filterMapConsNoneRT sel head rest hsel]
          exact isAscendingListRT_filterMap sel selIdent rest hRestAsc
      | some picked =>
          have hpEq : picked = head := selIdent head picked hsel
          rw [filterMapConsSomeRT sel head picked rest hsel, hpEq]
          show (natListAllAboveRT head (rest.filterMap sel) && isAscendingListRT (rest.filterMap sel)) = true
          rw [natListAllAboveRT_filterMap sel selIdent head rest hAbove,
              isAscendingListRT_filterMap sel selIdent rest hRestAsc]; rfl

/-! ## `List.range` is strictly ascending (loop invariant) -/

private theorem natListAllAboveRT_ofAllAtLeastSuccRT (bound : Nat) : (entries : List Nat) →
    natListAllAtLeastRT (bound + 1) entries = true → natListAllAboveRT bound entries = true
  | [], _ => rfl
  | head :: rest, h => by
      have h' : (Nat.ble (bound + 1) head && natListAllAtLeastRT (bound + 1) rest) = true := h
      have hHead : Nat.ble (bound + 1) head = true := boolAndLeftRT _ _ h'
      have hRest : natListAllAtLeastRT (bound + 1) rest = true := boolAndRightRT _ _ h'
      show (Nat.blt bound head && natListAllAboveRT bound rest) = true
      rw [show Nat.blt bound head = Nat.ble (bound + 1) head from rfl, hHead,
          natListAllAboveRT_ofAllAtLeastSuccRT bound rest hRest]; rfl

private theorem natListAllAtLeastRT_weakenPredRT (bound : Nat) : (entries : List Nat) →
    natListAllAtLeastRT (bound + 1) entries = true → natListAllAtLeastRT bound entries = true
  | [], _ => rfl
  | head :: rest, h => by
      have h' : (Nat.ble (bound + 1) head && natListAllAtLeastRT (bound + 1) rest) = true := h
      have hHead : Nat.ble (bound + 1) head = true := boolAndLeftRT _ _ h'
      have hRest : natListAllAtLeastRT (bound + 1) rest = true := boolAndRightRT _ _ h'
      have hHead' : Nat.ble bound head = true :=
        natBleTrueOfLeRT bound head (Nat.le_of_lt (natLtOfBltTrueRT bound head hHead))
      show (Nat.ble bound head && natListAllAtLeastRT bound rest) = true
      rw [hHead', natListAllAtLeastRT_weakenPredRT bound rest hRest]; rfl

private theorem isAscendingListRT_rangeLoop : (count : Nat) → (accumulated : List Nat) →
    isAscendingListRT accumulated = true → natListAllAtLeastRT count accumulated = true →
    isAscendingListRT (List.range.loop count accumulated) = true
  | 0, accumulated, hAsc, _ => hAsc
  | count + 1, accumulated, hAsc, hGe => by
      show isAscendingListRT (List.range.loop count (count :: accumulated)) = true
      apply isAscendingListRT_rangeLoop count (count :: accumulated)
      · show (natListAllAboveRT count accumulated && isAscendingListRT accumulated) = true
        rw [natListAllAboveRT_ofAllAtLeastSuccRT count accumulated hGe, hAsc]; rfl
      · show (Nat.ble count count && natListAllAtLeastRT count accumulated) = true
        rw [natBleTrueOfLeRT count count (Nat.le_refl count),
            natListAllAtLeastRT_weakenPredRT count accumulated hGe]; rfl

private theorem isAscendingListRT_range (count : Nat) : isAscendingListRT (List.range count) = true := by
  show isAscendingListRT (List.range.loop count []) = true
  exact isAscendingListRT_rangeLoop count [] rfl rfl

/-! ## `throughStrandBottoms` is strictly ascending -/

private theorem throughStrandBottoms_isAscendingRT (bottomCount : Nat) (partner : List Nat) :
    isAscendingListRT (throughStrandBottoms bottomCount partner) = true := by
  show isAscendingListRT ((List.range bottomCount).filterMap (fun index =>
      match Nat.ble bottomCount (natListGetAt partner index) with | true => some index | false => none)) = true
  refine isAscendingListRT_filterMap
    (fun index => match Nat.ble bottomCount (natListGetAt partner index) with | true => some index | false => none)
    (fun index picked hsome => ?_) (List.range bottomCount) (isAscendingListRT_range bottomCount)
  have hsome' : (match Nat.ble bottomCount (natListGetAt partner index) with
      | true => some index | false => none) = some picked := hsome
  revert hsome'
  cases Nat.ble bottomCount (natListGetAt partner index) with
  | true => intro hsome'; exact (Option.some.inj hsome').symm
  | false =>
      intro hsome'
      have hcontra : (none : Option Nat) = some picked := hsome'
      nomatch hcontra

/-! ## The count-below-inverts-getAt roundtrip on an ascending list -/

/-- On an ascending list `entries` with all entries strictly above `bound`, nothing is counted strictly below
`bound`. -/
private theorem arcMiddleCountBelow_zero_ofAllAboveRT (bound : Nat) : (entries : List Nat) →
    natListAllAboveRT bound entries = true → arcMiddleCountBelow entries bound = 0
  | [], _ => rfl
  | head :: rest, hAll => by
      have hAll' : (Nat.blt bound head && natListAllAboveRT bound rest) = true := hAll
      have hbHead : Nat.blt bound head = true := boolAndLeftRT _ _ hAll'
      have hRest : natListAllAboveRT bound rest = true := boolAndRightRT _ _ hAll'
      have hHeadNotBelow : Nat.blt head bound = false :=
        natBltFalseOfLeRT head bound (Nat.le_of_lt (natLtOfBltTrueRT bound head hbHead))
      show cond (Nat.blt head bound) 1 0 + arcMiddleCountBelow rest bound = 0
      rw [hHeadNotBelow]
      show (0 : Nat) + arcMiddleCountBelow rest bound = 0
      rw [Nat.zero_add]
      exact arcMiddleCountBelow_zero_ofAllAboveRT bound rest hRest

/-- If every entry of `entries` is strictly above `bound` and `value` is a member, then `bound < value`. -/
private theorem natBlt_ofAllAbove_memRT (bound : Nat) : (entries : List Nat) → (value : Nat) →
    natListAllAboveRT bound entries = true → memBool value entries = true → Nat.blt bound value = true
  | [], value, _, hmem => Bool.noConfusion hmem
  | head :: rest, value, hAll, hmem => by
      have hAll' : (Nat.blt bound head && natListAllAboveRT bound rest) = true := hAll
      have hbHead : Nat.blt bound head = true := boolAndLeftRT _ _ hAll'
      have hRest : natListAllAboveRT bound rest = true := boolAndRightRT _ _ hAll'
      cases hbeq : Nat.beq head value with
      | true =>
          have hEq : head = value := natEqOfBeqTrueRT head value hbeq
          rw [← hEq]; exact hbHead
      | false =>
          have hmem' : (Nat.beq head value || memBool value rest) = true := hmem
          rw [hbeq] at hmem'
          exact natBlt_ofAllAbove_memRT bound rest value hRest hmem'

/-- ★★ **The count-below roundtrip on an ascending list.**  For a strictly-ascending `order` and any member `value`,
reading `order` at the count-strictly-below-`value` position reads back `value` — because on an ascending list the
count of entries below a member is exactly that member's position.  Structural induction on `order`. -/
private theorem arcMiddleCountBelow_getAt_roundtripRT : (order : List Nat) → isAscendingListRT order = true →
    (value : Nat) → memBool value order = true →
    natListGetAt order (arcMiddleCountBelow order value) = value
  | [], _, _, hmem => Bool.noConfusion hmem
  | head :: rest, hAsc, value, hmem => by
      have hAsc' : (natListAllAboveRT head rest && isAscendingListRT rest) = true := hAsc
      have hAbove : natListAllAboveRT head rest = true := boolAndLeftRT _ _ hAsc'
      have hRestAsc : isAscendingListRT rest = true := boolAndRightRT _ _ hAsc'
      cases hbeq : Nat.beq head value with
      | true =>
          have hEq : head = value := natEqOfBeqTrueRT head value hbeq
          have hcz : arcMiddleCountBelow rest value = 0 := by
            rw [← hEq]; exact arcMiddleCountBelow_zero_ofAllAboveRT head rest hAbove
          have hbltF : Nat.blt head value = false := by
            rw [← hEq]; exact natBltFalseOfLeRT head head (Nat.le_refl head)
          show natListGetAt (head :: rest) (cond (Nat.blt head value) 1 0 + arcMiddleCountBelow rest value) = value
          rw [hbltF, hcz]
          show head = value
          exact hEq
      | false =>
          have hmem' : (Nat.beq head value || memBool value rest) = true := hmem
          rw [hbeq] at hmem'
          have hMemRest : memBool value rest = true := hmem'
          have hbltT : Nat.blt head value = true := natBlt_ofAllAbove_memRT head rest value hAbove hMemRest
          show natListGetAt (head :: rest) (cond (Nat.blt head value) 1 0 + arcMiddleCountBelow rest value) = value
          rw [hbltT]
          show natListGetAt (head :: rest) (1 + arcMiddleCountBelow rest value) = value
          rw [Nat.add_comm 1 (arcMiddleCountBelow rest value)]
          show natListGetAt rest (arcMiddleCountBelow rest value) = value
          exact arcMiddleCountBelow_getAt_roundtripRT rest hRestAsc value hMemRest

/-! ## THE CRUX -/

/-- ★★★ **THE THROUGH-STRAND ROUNDTRIP CRUX.**  For every well-formed through-bottom `value ∈ throughStrandBottoms
bottomCount partner`, reading `throughStrandBottoms` at the count-strictly-below-`value` rank reads back `value`:
`natListGetAt (throughStrandBottoms …) (arcMiddleCountBelow (throughStrandBottoms …) value) = value`.  The through
chain's P1 seam consumes this at `value := i` (the through arc's bottom foot), since the middle permutation carries the
rank `throughStrandPerm[topRank] = arcMiddleCountBelow throughStrandBottoms i`.  The direction-dual of the r26 keystone,
grounded on the strict ascent of `throughStrandBottoms` (a filterMap over `List.range`). -/
theorem throughStrandBottoms_getAt_arcMiddleCountBelow (bottomCount : Nat) (partner : List Nat) (value : Nat)
    (member : value ∈ throughStrandBottoms bottomCount partner) :
    natListGetAt (throughStrandBottoms bottomCount partner)
        (arcMiddleCountBelow (throughStrandBottoms bottomCount partner) value) = value :=
  arcMiddleCountBelow_getAt_roundtripRT (throughStrandBottoms bottomCount partner)
    (throughStrandBottoms_isAscendingRT bottomCount partner) value
    (memBoolTrueOfMemRT (throughStrandBottoms bottomCount partner) value member)

/-! ## Firing probes (the crux exercised, not `decide`d) -/

/-- ★★ **The crux FIRES on the width-12 monster through bottom `4`.**  `throughStrandBottoms = [4, 5]`,
`arcMiddleCountBelow [4,5] 4 = 0`, and the crux reads back `4`. -/
theorem throughStrandBottoms_getAt_arcMiddleCountBelow_firesMonster :
    natListGetAt (throughStrandBottoms 6 [1, 0, 3, 2, 6, 7, 4, 5, 9, 8, 11, 10])
        (arcMiddleCountBelow (throughStrandBottoms 6 [1, 0, 3, 2, 6, 7, 4, 5, 9, 8, 11, 10]) 4) = 4 :=
  throughStrandBottoms_getAt_arcMiddleCountBelow 6 [1, 0, 3, 2, 6, 7, 4, 5, 9, 8, 11, 10] 4
    (by rw [show throughStrandBottoms 6 [1, 0, 3, 2, 6, 7, 4, 5, 9, 8, 11, 10] = [4, 5] from rfl]
        exact List.Mem.head [5])

/-- ★★ **The crux FIRES on the width-12 monster through bottom `5`** (rank `1`, `arcMiddleCountBelow [4,5] 5 = 1`). -/
theorem throughStrandBottoms_getAt_arcMiddleCountBelow_firesMonsterHigh :
    natListGetAt (throughStrandBottoms 6 [1, 0, 3, 2, 6, 7, 4, 5, 9, 8, 11, 10])
        (arcMiddleCountBelow (throughStrandBottoms 6 [1, 0, 3, 2, 6, 7, 4, 5, 9, 8, 11, 10]) 5) = 5 :=
  throughStrandBottoms_getAt_arcMiddleCountBelow 6 [1, 0, 3, 2, 6, 7, 4, 5, 9, 8, 11, 10] 5
    (by rw [show throughStrandBottoms 6 [1, 0, 3, 2, 6, 7, 4, 5, 9, 8, 11, 10] = [4, 5] from rfl]
        exact List.Mem.tail 4 (List.Mem.head []))

/-- ★★ **The crux FIRES on the mutually-crossing 3-through diagram** (`throughStrandBottoms = [0, 1, 2]`, value `2`,
`arcMiddleCountBelow [0,1,2] 2 = 2`, reads back `2`) — the genuine multi-through witness. -/
theorem throughStrandBottoms_getAt_arcMiddleCountBelow_fires3Through :
    natListGetAt (throughStrandBottoms 3 [4, 5, 3, 2, 0, 1])
        (arcMiddleCountBelow (throughStrandBottoms 3 [4, 5, 3, 2, 0, 1]) 2) = 2 :=
  throughStrandBottoms_getAt_arcMiddleCountBelow 3 [4, 5, 3, 2, 0, 1] 2
    (by rw [show throughStrandBottoms 3 [4, 5, 3, 2, 0, 1] = [0, 1, 2] from rfl]
        exact List.Mem.tail 0 (List.Mem.tail 1 (List.Mem.head [])))

/-! ## Honesty marker -/

/-- ★★ **Honesty marker — the THROUGH-STRAND ROUNDTRIP CRUX is SHIPPED (r27).**
`throughStrandBottoms_getAt_arcMiddleCountBelow` proves, zero-axiom and structural, that on the strictly-ascending
distinct list `throughStrandBottoms` the count-strictly-below rank inverts `natListGetAt` — the P1 seam of the THROUGH
per-arc five-phase T-CONNECT.  The direction-dual of the r26 rank ↔ position keystone, grounded on the strict ascent of
`throughStrandBottoms` (filterMap over `List.range` preserves strict ascent).  A NEW ingredient marker; it flips NO
master — the five-phase composition and the all-class dispatch stay ahead.  `= true`. -/
def fxBrauer_hasThroughStrandRoundtrip : Bool := true

end FX1Poly.Polygraph
