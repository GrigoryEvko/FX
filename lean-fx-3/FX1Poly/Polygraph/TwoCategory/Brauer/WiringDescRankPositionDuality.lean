import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcReadOffPermutation

/-! # BRAUER r26 — THE RANK ↔ POSITION DUALITY: the value→position roundtrip on distinct lists (the CUP / THROUGH keystone)

The r26 recon identified ONE shared keystone unlocking the CUP `permInverse` cup-rank arithmetic AND the THROUGH
five-phase seams P3 / P5: the **rank ↔ position duality** for a distinct (range-permutation) list.  The shipped
conjugator already carries the FORWARD roundtrip `natListGetAt order (natIndexOfValue order value) = value` (value in
range) and getAt-injectivity from distinctness — but both are `private` inside `WiringDescArcConjugator`, and only in
the mixed selection-sort fold, never exposed as a standalone reusable fact.  This file re-proves, PUBLICLY and
structurally, the value→position roundtrip

    natIndexOfValue order (natListGetAt order position) = position

for a distinct `order` at any in-range `position`.  It is the exact fact the CUP / THROUGH chains consume:

  * **CUP** (P5 / the `permInverse` cup-rank arithmetic): `permInverse order` read at a cup top leg reads back its
    rank — `natListGetAt (permInverse order) (natListGetAt order position) = position` (via the shipped
    `natListGetAtPermInversePerm` = `natIndexOfValue`, then the duality).
  * **THROUGH** (P3): `throughStrandPerm[topRank] = r` reduces to the through-top value-at-its-own-rank identity, an
    instance of the same duality on the top read-off order.
  * **THROUGH** (P5): `natIndexOfValue order t = topRank` for a through top `t` at rank `topRank`, the duality directly.

## The public re-proofs (propext-free, structural)

  * `natBeqSelfDuality` — `(n == n) = true`, structural on `n` (`beq_self` leaks `propext`; this recursion does not).
  * `natEqOfBeqTrueDuality` — `(a == b) = true → a = b`, full-enum on both (`eq_of_beq` leaks; this does not).
  * `memBoolGetAtSelfDuality` — an in-range `natListGetAt` read is a `memBool` member of the list.
  * `natIndexOfValue_natListGetAt_ofDistinct` — THE keystone, direct induction on `order`: the head/first-occurrence
    structure of `natIndexOfValue` gives `0` at position `0` (the `head == head` arm fires) and drills past the head at
    `position + 1` (the head cannot equal a later member, by distinctness + `memBoolGetAtSelfDuality`).
  * `natIndexOfValue_natListGetAt_ofPermutationOfRange` — the `IsPermutationOfRange` wrapper.
  * `natListGetAtPermInverse_natListGetAt_ofPermutationOfRange` — the CUP form: reading `permInverse order` at a value
    reads back its position (composing the shipped `natListGetAtPermInversePerm` with the keystone).

Raw Lean 4 + Init; structural recursion, `==` full-enum, `memBool`-based, no `omega` / `simp`-AC / `native_decide` /
`WellFounded.fix`.  Per-declaration `#assert_no_axioms` in the audit twin; independent `#print axioms` clean. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Propext-free `Nat`-equality kit -/

/-- `Nat.beq n n = true`, structural on `n` (the `beq_self` simp lemma leaks `propext`; this recursion is clean:
`Nat.beq (n+1) (n+1)` reduces definitionally to `Nat.beq n n`).  Used to fire the `memBool` head arm (`memBool`'s
match is on `Nat.beq`). -/
theorem natBeqSelfDuality : (n : Nat) → Nat.beq n n = true
  | 0 => rfl
  | n + 1 => natBeqSelfDuality n

/-- The `==`-form self equality (`==` for `Nat` is the `DecidableEq`-based `BEq`, not `Nat.beq`, so this goes through
`decide_eq_true`) — used to fire the `natIndexOfValue` head arm (whose match is on `==`). -/
theorem beqSelfTrueDuality (n : Nat) : (n == n) = true := decide_eq_true rfl

/-- `(a == b) = true → a = b` — the `Decidable` bridge (`of_decide_eq_true`, propext-free, matching the conjugator's
`eqOfBEqTrueConj`). -/
theorem eqOfBeqTrueDuality {a b : Nat} (h : (a == b) = true) : a = b := of_decide_eq_true h

/-- An in-range `natListGetAt` read is a `memBool` member of the list — structural on the list then the index.  At
position `0` the read is the head; at `index + 1` it is a member of the tail. -/
theorem memBoolGetAtSelfDuality : (entries : List Nat) → (index : Nat) → index < entries.length →
    memBool (natListGetAt entries index) entries = true
  | [], index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | head :: rest, 0, _ => by
      show (Nat.beq head head || memBool head rest) = true
      rw [natBeqSelfDuality head]
      exact Bool.true_or _
  | head :: rest, index + 1, indexBelow => by
      have restBelow : index < rest.length := Nat.lt_of_succ_lt_succ indexBelow
      show (Nat.beq head (natListGetAt rest index) || memBool (natListGetAt rest index) rest) = true
      rw [memBoolGetAtSelfDuality rest index restBelow]
      exact Bool.or_true _

/-! ## THE KEYSTONE — the value → position roundtrip on distinct lists -/

/-- ★★★ **THE RANK ↔ POSITION DUALITY.**  For a distinct list `order` and any in-range `position`, the first-occurrence
index of the value at `position` IS `position`: `natIndexOfValue order (natListGetAt order position) = position`.
Direct structural induction on `order`.  At `position = 0` the value is the head, and `natIndexOfValue` returns `0`
immediately (the `head == head` arm fires via `natBeqSelfDuality`).  At `position + 1` the value is a member of the tail
(`memBoolGetAtSelfDuality`), so distinctness (`memBool head rest = false`) forces `head ≠ value` — the `natIndexOfValue`
head arm is skipped, `+1` is prepended, and the induction hypothesis closes the tail rank.  This is the single fact the
CUP `permInverse` cup-rank arithmetic and the THROUGH P3 / P5 seams all reduce to. -/
theorem natIndexOfValue_natListGetAt_ofDistinct : (order : List Nat) → isDistinctList order = true →
    (position : Nat) → position < order.length →
    natIndexOfValue order (natListGetAt order position) = position
  | [], _, position, positionBelow => absurd positionBelow (Nat.not_lt_zero position)
  | head :: rest, _, 0, _ => by
      show (match head == head with | true => 0 | false => natIndexOfValue rest head + 1) = 0
      rw [beqSelfTrueDuality head]
  | head :: rest, distinct, position + 1, positionBelow => by
      have restBelow : position < rest.length := Nat.lt_of_succ_lt_succ positionBelow
      have splitDist : isDistinctList (head :: rest)
          = (not (memBool head rest) && isDistinctList rest) := rfl
      rw [splitDist] at distinct
      have headNotMem : memBool head rest = false := by
        cases hmem : memBool head rest with
        | false => rfl
        | true => rw [hmem] at distinct; exact Bool.noConfusion distinct
      have distRest : isDistinctList rest = true := by
        cases hrest : isDistinctList rest with
        | true => rfl
        | false => rw [headNotMem, hrest] at distinct; exact Bool.noConfusion distinct
      have valueMem : memBool (natListGetAt rest position) rest = true :=
        memBoolGetAtSelfDuality rest position restBelow
      have headNe : (head == natListGetAt rest position) = false := by
        cases hbeq : (head == natListGetAt rest position) with
        | false => rfl
        | true =>
            have headEq : head = natListGetAt rest position := eqOfBeqTrueDuality hbeq
            rw [headEq, valueMem] at headNotMem
            exact Bool.noConfusion headNotMem
      have indexSucc : natIndexOfValue (head :: rest) (natListGetAt rest position)
          = natIndexOfValue rest (natListGetAt rest position) + 1 := by
        show (match head == natListGetAt rest position with
                | true => 0 | false => natIndexOfValue rest (natListGetAt rest position) + 1)
            = natIndexOfValue rest (natListGetAt rest position) + 1
        rw [headNe]
      show natIndexOfValue (head :: rest) (natListGetAt rest position) = position + 1
      rw [indexSucc, natIndexOfValue_natListGetAt_ofDistinct rest distRest position restBelow]

/-- ★★ **The keystone, `IsPermutationOfRange` wrapper.**  A range-permutation is distinct and of width `width`, so the
value at any position `< width` reads back its position under `natIndexOfValue`. -/
theorem natIndexOfValue_natListGetAt_ofPermutationOfRange (width : Nat) (order : List Nat)
    (valid : IsPermutationOfRange width order) (position : Nat) (positionLt : position < width) :
    natIndexOfValue order (natListGetAt order position) = position :=
  natIndexOfValue_natListGetAt_ofDistinct order valid.isDistinct position
    (by rw [valid.hasWidthLength]; exact positionLt)

/-- ★★★ **The CUP form — `permInverse` reads back the position.**  For a range-permutation `order`, reading its inverse
at the value `natListGetAt order position` reads back `position`: the shipped `natListGetAtPermInversePerm` turns the
`permInverse` read into `natIndexOfValue`, and the keystone collapses it.  This is EXACTLY the `permInverse` cup-rank
arithmetic the recon named — the cup top leg surfaces at the top port whose inverse-routed position is the leg's rank. -/
theorem natListGetAtPermInverse_natListGetAt_ofPermutationOfRange (width : Nat) (order : List Nat)
    (valid : IsPermutationOfRange width order) (position : Nat) (positionLt : position < width) :
    natListGetAt (permInverse order) (natListGetAt order position) = position := by
  have valueBound : natListGetAt order position < width := valid.isBounded position positionLt
  have valueLtLen : natListGetAt order position < order.length := by
    rw [valid.hasWidthLength]; exact valueBound
  rw [natListGetAtPermInversePerm order (natListGetAt order position) valueLtLen]
  exact natIndexOfValue_natListGetAt_ofPermutationOfRange width order valid position positionLt

/-! ## Honesty marker -/

/-- ★★ **Honesty marker — the RANK ↔ POSITION DUALITY is SHIPPED (r26 keystone).**
`natIndexOfValue_natListGetAt_ofDistinct` proves, publicly and structurally, the value→position roundtrip on a distinct
list; `…_ofPermutationOfRange` wraps it for range-permutations; and `natListGetAtPermInverse_natListGetAt_ofPermutationOfRange`
delivers the CUP `permInverse` cup-rank arithmetic form.  This is the single shared keystone the recon named — unlocking
the CUP cup-rank arithmetic and the THROUGH P3 / P5 seams.  A NEW ingredient marker; it flips NO master.  `= true`. -/
def fxBrauer_hasRankPositionDuality : Bool := true

end FX1Poly.Polygraph
