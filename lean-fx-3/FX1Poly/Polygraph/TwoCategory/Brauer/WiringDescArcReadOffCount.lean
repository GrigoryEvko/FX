import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcReadOffPermutation

/-! # BRAUER-MIDDLE r16 — the counting round: the read-off order length identities (T-CLOSE bottom side)

The r15 leg (`Brauer/WiringDescArcReadOffPermutation.lean`) shipped the finite-pigeonhole surjectivity of
range-permutations and `permInverse` gate-preservation, and truth-PROBED that the extractor read-off orders satisfy
`IsPermutationOfRange` on two concrete diagrams (`by decide`).  What the general `IsPermutationOfRange` still lacks is
its `hasWidthLength` field: that `(capArcFeet ++ throughStrandBottoms).length = bottomCount` for EVERY well-formed
involution partner.  This file lands the counting content that identity rests on — the three-way partition count over
`List.range bottomCount` and the involution pairing bijection `|larger cap feet| = |smaller cap feet|` — the recon's
named crux and crux-of-crux.

## What this file ships (each zero-axiom, structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`)

  * **`countTrue` + `partitionCountThree`** — the three-way partition count: three guards that are mutually-exclusive
    and exhaustive per element of a list sum their `countTrue`s to the list length.  The general counting engine.
  * **`partitionThree_of_involution`** — the per-index discharge under the `IsBoundaryInvolution` gate: each bottom
    port is exactly one of SMALLER cap foot / LARGER cap foot / THROUGH bottom.  The classification the count needs.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Section 0 — re-derived propext-free `Nat.blt` / `Nat.ble` deciders (the zero-dep discipline) -/

private theorem natBleOfLeCount : (small large : Nat) → small ≤ large → Nat.ble small large = true
  | 0, _, _ => rfl
  | _ + 1, 0, le => absurd le (Nat.not_succ_le_zero _)
  | small + 1, large + 1, le => natBleOfLeCount small large (Nat.le_of_succ_le_succ le)

private theorem natBleFalseOfGtCount : (small large : Nat) → large < small → Nat.ble small large = false
  | 0, large, gt => absurd gt (Nat.not_lt_zero large)
  | _ + 1, 0, _ => rfl
  | small + 1, large + 1, gt => natBleFalseOfGtCount small large (Nat.lt_of_succ_lt_succ gt)

private theorem natBltOfLtCount (small large : Nat) (lt : small < large) : Nat.blt small large = true :=
  natBleOfLeCount (small + 1) large lt

private theorem natBltFalseOfLeCount (small large : Nat) (le : large ≤ small) : Nat.blt small large = false :=
  natBleFalseOfGtCount (small + 1) large (Nat.lt_succ_of_le le)

private theorem natLtOfLeOfNeCount (small large : Nat) (le : small ≤ large) (ne : small ≠ large) : small < large := by
  cases Nat.lt_or_ge small large with
  | inl lt => exact lt
  | inr ge => exact absurd (Nat.le_antisymm le ge) ne

private theorem andEqTrueCount : (leftFlag rightFlag : Bool) → leftFlag = true → rightFlag = true →
    (leftFlag && rightFlag) = true
  | true, true, _, _ => rfl
  | true, false, _, rightTrue => Bool.noConfusion rightTrue
  | false, _, leftTrue, _ => Bool.noConfusion leftTrue

private theorem andEqFalseLeftCount : (leftFlag rightFlag : Bool) → leftFlag = false →
    (leftFlag && rightFlag) = false
  | false, _, _ => rfl
  | true, _, leftFalse => Bool.noConfusion leftFalse

private theorem andEqFalseRightCount : (leftFlag rightFlag : Bool) → rightFlag = false →
    (leftFlag && rightFlag) = false
  | true, false, _ => rfl
  | false, _, _ => rfl
  | true, true, rightFalse => Bool.noConfusion rightFalse

private theorem memRangeLoopCount {target : Nat} :
    (count : Nat) → (accumulated : List Nat) → target ∈ List.range.loop count accumulated →
    target < count ∨ target ∈ accumulated
  | 0, _, membership => Or.inr membership
  | count + 1, accumulated, membership => by
      cases memRangeLoopCount count (count :: accumulated) membership with
      | inl isBelow => exact Or.inl (Nat.lt_succ_of_lt isBelow)
      | inr consMembership =>
          cases consMembership with
          | head => exact Or.inl (Nat.lt_succ_self _)
          | tail _ tailMembership => exact Or.inr tailMembership

private theorem memRangeLtCount {target count : Nat} (membership : target ∈ List.range count) : target < count := by
  cases memRangeLoopCount count [] membership with
  | inl isBelow => exact isBelow
  | inr nilMembership => nomatch nilMembership

/-! ## Section 1 — the arc-class guard functions (definitionally the `filterMap` predicates) -/

/-- The SMALLER cap-foot guard — a bottom port whose partner is a bottom port strictly larger (the smaller foot of a
bottom–bottom cap arc).  Definitionally the `capArcFeetIndices` `filterMap` predicate. -/
def capSmallerGuard (bottomCount : Nat) (partner : List Nat) (index : Nat) : Bool :=
  Nat.blt (natListGetAt partner index) bottomCount && Nat.blt index (natListGetAt partner index)

/-- The LARGER cap-foot guard — a bottom port whose partner is a bottom port strictly smaller (the larger foot of a
bottom–bottom cap arc).  The ∗-mirror of `capSmallerGuard` under swapping the two feet. -/
def capLargerGuard (bottomCount : Nat) (partner : List Nat) (index : Nat) : Bool :=
  Nat.blt (natListGetAt partner index) bottomCount && Nat.blt (natListGetAt partner index) index

/-- The THROUGH-bottom guard — a bottom port whose partner is a top port.  Definitionally the `throughStrandBottoms`
`filterMap` predicate. -/
def throughBottomGuard (bottomCount : Nat) (partner : List Nat) (index : Nat) : Bool :=
  Nat.ble bottomCount (natListGetAt partner index)

/-! ## Section 2 — the three-way partition count -/

/-- Count the list elements the guard sends to `true` — a `cond`-driven fold, `propext`-free. -/
def countTrue (guard : Nat → Bool) : List Nat → Nat
  | [] => 0
  | head :: rest => cond (guard head) 1 0 + countTrue guard rest

/-- Exactly one of three boolean flags is `true` (and the other two `false`). -/
def onlyOneTrueThree (flagSmaller flagLarger flagThrough : Bool) : Prop :=
  (flagSmaller = true ∧ flagLarger = false ∧ flagThrough = false)
    ∨ (flagSmaller = false ∧ flagLarger = true ∧ flagThrough = false)
    ∨ (flagSmaller = false ∧ flagLarger = false ∧ flagThrough = true)

/-- A four-summand commutation `(x+y)+(z+w) = (x+z)+(y+w)` — pure commutative-monoid, built from `Nat.add_comm` /
`Nat.add_assoc` (both `propext`-free). -/
private theorem addFourCommCount (first second third fourth : Nat) :
    (first + second) + (third + fourth) = (first + third) + (second + fourth) := by
  rw [Nat.add_assoc first second (third + fourth), ← Nat.add_assoc second third fourth,
    Nat.add_comm second third, Nat.add_assoc third second fourth,
    ← Nat.add_assoc first third (second + fourth)]

/-- The six-summand rearrangement collecting the per-position contributions from the per-list totals. -/
private theorem sixSumRearrangeCount (leadSmaller tailSmaller leadLarger tailLarger leadThrough tailThrough : Nat) :
    (leadSmaller + tailSmaller) + (leadLarger + tailLarger) + (leadThrough + tailThrough)
      = (leadSmaller + leadLarger + leadThrough) + (tailSmaller + tailLarger + tailThrough) := by
  rw [addFourCommCount leadSmaller tailSmaller leadLarger tailLarger,
    addFourCommCount (leadSmaller + leadLarger) (tailSmaller + tailLarger) leadThrough tailThrough]

/-- ★ **The three-way partition count.**  If three guards are mutually-exclusive and exhaustive per element of
`source` (`onlyOneTrueThree`), then their `countTrue`s over `source` sum to `source.length`.  The general counting
engine — a structural induction summing one contribution per element. -/
theorem partitionCountThree (guardSmaller guardLarger guardThrough : Nat → Bool) : (source : List Nat) →
    (∀ value, value ∈ source →
      onlyOneTrueThree (guardSmaller value) (guardLarger value) (guardThrough value)) →
    countTrue guardSmaller source + countTrue guardLarger source + countTrue guardThrough source = source.length
  | [], _ => rfl
  | head :: rest, discharge => by
      have restCount := partitionCountThree guardSmaller guardLarger guardThrough rest
        (fun value valueMem => discharge value (List.Mem.tail head valueMem))
      have headDischarge := discharge head (List.Mem.head rest)
      show (cond (guardSmaller head) 1 0 + countTrue guardSmaller rest)
          + (cond (guardLarger head) 1 0 + countTrue guardLarger rest)
          + (cond (guardThrough head) 1 0 + countTrue guardThrough rest)
        = rest.length + 1
      rw [sixSumRearrangeCount (cond (guardSmaller head) 1 0) (countTrue guardSmaller rest)
        (cond (guardLarger head) 1 0) (countTrue guardLarger rest)
        (cond (guardThrough head) 1 0) (countTrue guardThrough rest), restCount]
      rcases headDischarge with ⟨hSmaller, hLarger, hThrough⟩ | ⟨hSmaller, hLarger, hThrough⟩
        | ⟨hSmaller, hLarger, hThrough⟩ <;>
        rw [hSmaller, hLarger, hThrough] <;>
        exact Nat.add_comm 1 rest.length

/-- ★ **The per-index classification under the involution gate.**  Each bottom port `index < bottomCount` is exactly
one of a SMALLER cap foot, a LARGER cap foot, or a THROUGH bottom — `capSmallerGuard` / `capLargerGuard` /
`throughBottomGuard` are mutually-exclusive and exhaustive on it, using the involution's fixed-point-freeness to split
the two cap cases.  The classification the partition count ranges over. -/
theorem partitionThree_of_involution (bottomCount total : Nat) (partner : List Nat)
    (bottomLe : bottomCount ≤ total) (wf : IsBoundaryInvolution total partner)
    (index : Nat) (below : index < bottomCount) :
    onlyOneTrueThree (capSmallerGuard bottomCount partner index)
      (capLargerGuard bottomCount partner index)
      (throughBottomGuard bottomCount partner index) := by
  have indexLtTotal : index < total := Nat.lt_of_lt_of_le below bottomLe
  cases Nat.lt_or_ge (natListGetAt partner index) bottomCount with
  | inr geBottom =>
      exact Or.inr (Or.inr
        ⟨andEqFalseLeftCount _ _ (natBltFalseOfLeCount (natListGetAt partner index) bottomCount geBottom),
         andEqFalseLeftCount _ _ (natBltFalseOfLeCount (natListGetAt partner index) bottomCount geBottom),
         natBleOfLeCount bottomCount (natListGetAt partner index) geBottom⟩)
  | inl ltBottom =>
      have partnerNeIndex : natListGetAt partner index ≠ index := wf.isFixedPointFree index indexLtTotal
      cases Nat.lt_or_ge index (natListGetAt partner index) with
      | inl indexLtPartner =>
          exact Or.inl
            ⟨andEqTrueCount _ _ (natBltOfLtCount (natListGetAt partner index) bottomCount ltBottom)
               (natBltOfLtCount index (natListGetAt partner index) indexLtPartner),
             andEqFalseRightCount _ _
               (natBltFalseOfLeCount (natListGetAt partner index) index (Nat.le_of_lt indexLtPartner)),
             natBleFalseOfGtCount bottomCount (natListGetAt partner index) ltBottom⟩
      | inr partnerLeIndex =>
          have partnerLtIndex : natListGetAt partner index < index :=
            natLtOfLeOfNeCount (natListGetAt partner index) index partnerLeIndex partnerNeIndex
          exact Or.inr (Or.inl
            ⟨andEqFalseRightCount _ _
               (natBltFalseOfLeCount index (natListGetAt partner index) (Nat.le_of_lt partnerLtIndex)),
             andEqTrueCount _ _ (natBltOfLtCount (natListGetAt partner index) bottomCount ltBottom)
               (natBltOfLtCount (natListGetAt partner index) index partnerLtIndex),
             natBleFalseOfGtCount bottomCount (natListGetAt partner index) ltBottom⟩)

/-! ## Section 3 — truth-probes: the crux `2·|caps| + |through| = bottomCount` on the recon hand-worked partners

Before proving the general width-length identity, confirm its arithmetic CONCLUSION on the recon's hand-worked valid
involution partners — the `+`-form crux `|caps| + |caps| + |through| = bottomCount` (avoiding `Nat.mul`). -/

/-- ★ **Truth-probe (adversarial-B).**  Partner `[2, 4, 0, 5, 1, 3]`, `bottomCount = 3`: one cap arc, one through —
`1 + 1 + 1 = 3`. -/
theorem cruxCount_probe_adversarialB :
    (capArcFeetIndices 3 [2, 4, 0, 5, 1, 3]).length + (capArcFeetIndices 3 [2, 4, 0, 5, 1, 3]).length
      + (throughStrandBottoms 3 [2, 4, 0, 5, 1, 3]).length = 3 := by decide

/-- ★ **Truth-probe (fresh mixed).**  Partner `[3, 4, 5, 0, 1, 2, 7, 6]`, `bottomCount = 4`: one cap arc, two
throughs — `1 + 1 + 2 = 4`. -/
theorem cruxCount_probe_freshMixed :
    (capArcFeetIndices 4 [3, 4, 5, 0, 1, 2, 7, 6]).length + (capArcFeetIndices 4 [3, 4, 5, 0, 1, 2, 7, 6]).length
      + (throughStrandBottoms 4 [3, 4, 5, 0, 1, 2, 7, 6]).length = 4 := by decide

/-- ★ **Truth-probe (all caps).**  Partner `[1, 0, 3, 2]`, `bottomCount = 2`: two cap feet, no through —
`1 + 1 + 0 = 2`. -/
theorem cruxCount_probe_allCaps :
    (capArcFeetIndices 2 [1, 0, 3, 2]).length + (capArcFeetIndices 2 [1, 0, 3, 2]).length
      + (throughStrandBottoms 2 [1, 0, 3, 2]).length = 2 := by decide

/-- ★ **Truth-probe (all through).**  Partner `[2, 3, 0, 1]`, `bottomCount = 2`: no cap, two throughs —
`0 + 0 + 2 = 2`. -/
theorem cruxCount_probe_allThrough :
    (capArcFeetIndices 2 [2, 3, 0, 1]).length + (capArcFeetIndices 2 [2, 3, 0, 1]).length
      + (throughStrandBottoms 2 [2, 3, 0, 1]).length = 2 := by decide

/-- ★ **Truth-probe (width one).**  Partner `[1, 0]`, `bottomCount = 1`: the sole bottom is a through — `0 + 0 + 1 = 1`. -/
theorem cruxCount_probe_widthOne :
    (capArcFeetIndices 1 [1, 0]).length + (capArcFeetIndices 1 [1, 0]).length
      + (throughStrandBottoms 1 [1, 0]).length = 1 := by decide

/-- ★ **Truth-probe (empty).**  `bottomCount = 0`: every count is `0` — `0 + 0 + 0 = 0`. -/
theorem cruxCount_probe_empty :
    (capArcFeetIndices 0 []).length + (capArcFeetIndices 0 []).length
      + (throughStrandBottoms 0 []).length = 0 := by decide

/-! ## Section 4 — the re-derived `Nat.beq` / `memBool` / `List.map` kit (the zero-dep discipline) -/

private theorem boolAndLeftCount : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → leftFlag = true
  | true, _, _ => rfl
  | false, _, conj => Bool.noConfusion conj

private theorem boolAndRightCount : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → rightFlag = true
  | true, _, conj => conj
  | false, _, conj => Bool.noConfusion conj

private theorem eqFalseOfNotTrueCount : (flag : Bool) → (not flag) = true → flag = false
  | true, hnot => Bool.noConfusion hnot
  | false, _ => rfl

private theorem natBeqSelfCount : (value : Nat) → Nat.beq value value = true
  | 0 => rfl
  | value + 1 => natBeqSelfCount value

private theorem eqOfNatBeqTrueCount : (left right : Nat) → Nat.beq left right = true → left = right
  | 0, 0, _ => rfl
  | 0, _ + 1, hbeq => Bool.noConfusion hbeq
  | _ + 1, 0, hbeq => Bool.noConfusion hbeq
  | left + 1, right + 1, hbeq => congrArg (· + 1) (eqOfNatBeqTrueCount left right hbeq)

private theorem natBeqFalseOfNeCount : (left right : Nat) → left ≠ right → Nat.beq left right = false
  | 0, 0, ne => absurd rfl ne
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, _ => rfl
  | left + 1, right + 1, ne => natBeqFalseOfNeCount left right (fun eqTail => ne (congrArg (· + 1) eqTail))

private theorem neOfNatBeqFalseCount (left right : Nat) (hbeq : Nat.beq left right = false) : left ≠ right := by
  intro equal
  rw [equal, natBeqSelfCount] at hbeq
  exact Bool.noConfusion hbeq

private theorem memBoolOfMemCount : (entries : List Nat) → (value : Nat) → value ∈ entries →
    memBool value entries = true
  | [], _, memNil => nomatch memNil
  | head :: rest, value, memCons => by
      show (Nat.beq head value || memBool value rest) = true
      cases memCons with
      | head => rw [natBeqSelfCount]; rfl
      | tail _ memRest => rw [memBoolOfMemCount rest value memRest, Bool.or_true]

private theorem memBoolMemCount : (entries : List Nat) → (value : Nat) → memBool value entries = true →
    value ∈ entries
  | [], _, memTrue => Bool.noConfusion memTrue
  | head :: rest, value, memTrue => by
      cases hbeq : Nat.beq head value with
      | true =>
          have headEq : head = value := eqOfNatBeqTrueCount head value hbeq
          rw [← headEq]; exact List.Mem.head rest
      | false =>
          have memRest : memBool value rest = true := by
            have split : memBool value (head :: rest) = (Nat.beq head value || memBool value rest) := rfl
            rw [split, hbeq, Bool.false_or] at memTrue; exact memTrue
          exact List.Mem.tail head (memBoolMemCount rest value memRest)

private theorem mapLengthCount (mapFn : Nat → Nat) : (entries : List Nat) →
    (entries.map mapFn).length = entries.length
  | [] => rfl
  | _ :: rest => congrArg (· + 1) (mapLengthCount mapFn rest)

private theorem memBoolMapOfMemCount (mapFn : Nat → Nat) : (entries : List Nat) → (value : Nat) →
    value ∈ entries → memBool (mapFn value) (entries.map mapFn) = true
  | [], _, memNil => nomatch memNil
  | head :: rest, value, memCons => by
      show (Nat.beq (mapFn head) (mapFn value) || memBool (mapFn value) (rest.map mapFn)) = true
      cases memCons with
      | head => rw [natBeqSelfCount]; rfl
      | tail _ memRest => rw [memBoolMapOfMemCount mapFn rest value memRest, Bool.or_true]

private theorem memBoolMapWitnessCount (mapFn : Nat → Nat) : (entries : List Nat) → (value : Nat) →
    memBool value (entries.map mapFn) = true → ∃ preimage, preimage ∈ entries ∧ mapFn preimage = value
  | [], _, memTrue => Bool.noConfusion memTrue
  | head :: rest, value, memTrue => by
      have split : memBool value ((head :: rest).map mapFn)
        = (Nat.beq (mapFn head) value || memBool value (rest.map mapFn)) := rfl
      rw [split] at memTrue
      cases hbeq : Nat.beq (mapFn head) value with
      | true =>
          exact ⟨head, List.Mem.head rest, eqOfNatBeqTrueCount (mapFn head) value hbeq⟩
      | false =>
          have memRest : memBool value (rest.map mapFn) = true := by
            rw [hbeq, Bool.false_or] at memTrue; exact memTrue
          obtain ⟨preimage, preMem, preEq⟩ := memBoolMapWitnessCount mapFn rest value memRest
          exact ⟨preimage, List.Mem.tail head preMem, preEq⟩

private theorem memRangeLoopMemAccCount : (count : Nat) → (accumulated : List Nat) → (target : Nat) →
    target ∈ accumulated → target ∈ List.range.loop count accumulated
  | 0, _, _, mem => mem
  | count + 1, accumulated, target, mem =>
      memRangeLoopMemAccCount count (count :: accumulated) target (List.Mem.tail count mem)

private theorem memRangeLoopOfLtCount : (count : Nat) → (accumulated : List Nat) → (target : Nat) →
    target < count → target ∈ List.range.loop count accumulated
  | 0, _, target, lt => absurd lt (Nat.not_lt_zero target)
  | count + 1, accumulated, target, lt => by
      cases Nat.lt_or_ge target count with
      | inl below => exact memRangeLoopOfLtCount count (count :: accumulated) target below
      | inr ge =>
          have targetEq : target = count := Nat.le_antisymm (Nat.le_of_lt_succ lt) ge
          rw [targetEq]
          exact memRangeLoopMemAccCount count (count :: accumulated) count (List.Mem.head accumulated)

private theorem memRangeOfLtCount (target count : Nat) (lt : target < count) : target ∈ List.range count :=
  memRangeLoopOfLtCount count [] target lt

/-- Global injectivity of a fixed-point-free involution partner on the boundary ports. -/
private theorem involutionInjectiveCount (total : Nat) (partner : List Nat) (wf : IsBoundaryInvolution total partner)
    (left right : Nat) (leftLt : left < total) (rightLt : right < total)
    (partnerEq : natListGetAt partner left = natListGetAt partner right) : left = right := by
  have step : natListGetAt partner (natListGetAt partner left) = natListGetAt partner (natListGetAt partner right) :=
    congrArg (natListGetAt partner) partnerEq
  rw [wf.isSelfInverse left leftLt, wf.isSelfInverse right rightLt] at step
  exact step

/-! ## Section 5 — the guard-shaped `filterMap` reductions and the length ↔ `countTrue` bridge -/

private theorem filterMapConsNoneCount (transform : Nat → Option Nat) (head : Nat) (rest : List Nat)
    (headNone : transform head = none) :
    List.filterMap transform (head :: rest) = List.filterMap transform rest := by
  dsimp only [List.filterMap]; rw [headNone]

private theorem filterMapConsSomeCount (transform : Nat → Option Nat) (head mapped : Nat) (rest : List Nat)
    (headSome : transform head = some mapped) :
    List.filterMap transform (head :: rest) = mapped :: List.filterMap transform rest := by
  dsimp only [List.filterMap]; rw [headSome]

/-- The `.isSome` of a guard-shaped optional recovers the guard. -/
private theorem guardIsSomeAgreeCount (flag : Bool) (emitValue : Nat) :
    (match flag with | true => some emitValue | false => none).isSome = flag := by
  cases flag <;> rfl

/-- ★ **Guard-shaped `filterMap` length equals `countTrue`.**  For any optional-valued `transform` whose `.isSome`
tracks `guard`, the length of the `filterMap` equals the guard's `countTrue`.  The bridge from the read-off
`filterMap` lengths to the partition count. -/
theorem filterMapLength_eq_countTrue (transform : Nat → Option Nat) (guard : Nat → Bool)
    (agree : ∀ value, guard value = (transform value).isSome) : (source : List Nat) →
    (source.filterMap transform).length = countTrue guard source
  | [] => rfl
  | head :: rest => by
      cases headOpt : transform head with
      | none =>
          have guardFalse : guard head = false := by
            have agreeHead := agree head; rw [headOpt] at agreeHead; exact agreeHead
          rw [filterMapConsNoneCount transform head rest headOpt,
            filterMapLength_eq_countTrue transform guard agree rest]
          show countTrue guard rest = cond (guard head) 1 0 + countTrue guard rest
          rw [guardFalse]
          exact (Nat.zero_add (countTrue guard rest)).symm
      | some mapped =>
          have guardTrue : guard head = true := by
            have agreeHead := agree head; rw [headOpt] at agreeHead; exact agreeHead
          rw [filterMapConsSomeCount transform head mapped rest headOpt]
          show (List.filterMap transform rest).length + 1 = cond (guard head) 1 0 + countTrue guard rest
          rw [filterMapLength_eq_countTrue transform guard agree rest, guardTrue]
          exact Nat.add_comm (countTrue guard rest) 1

/-! ## Section 6 — the three read-off lengths as partition counts -/

/-- The smaller cap-foot count equals the `capSmallerGuard` `countTrue` over `List.range bottomCount`. -/
theorem capArcFeetIndices_length_eq_count (bottomCount : Nat) (partner : List Nat) :
    (capArcFeetIndices bottomCount partner).length
      = countTrue (capSmallerGuard bottomCount partner) (List.range bottomCount) :=
  filterMapLength_eq_countTrue
    (fun index => match capSmallerGuard bottomCount partner index with | true => some index | false => none)
    (capSmallerGuard bottomCount partner)
    (fun value => (guardIsSomeAgreeCount (capSmallerGuard bottomCount partner value) value).symm)
    (List.range bottomCount)

/-- The through-bottom count equals the `throughBottomGuard` `countTrue` over `List.range bottomCount`. -/
theorem throughStrandBottoms_length_eq_count (bottomCount : Nat) (partner : List Nat) :
    (throughStrandBottoms bottomCount partner).length
      = countTrue (throughBottomGuard bottomCount partner) (List.range bottomCount) :=
  filterMapLength_eq_countTrue
    (fun index => match throughBottomGuard bottomCount partner index with | true => some index | false => none)
    (throughBottomGuard bottomCount partner)
    (fun value => (guardIsSomeAgreeCount (throughBottomGuard bottomCount partner value) value).symm)
    (List.range bottomCount)

/-- ★ **The larger cap-foot indices** — bottom ports whose partner is a bottom port strictly smaller (the ∗-mirror of
`capArcFeetIndices`, listing the LARGER foot of each cap arc). -/
def capLargerFeetIndices (bottomCount : Nat) (partner : List Nat) : List Nat :=
  (List.range bottomCount).filterMap (fun index =>
    match capLargerGuard bottomCount partner index with | true => some index | false => none)

/-- The larger cap-foot count equals the `capLargerGuard` `countTrue` over `List.range bottomCount`. -/
theorem capLargerFeetIndices_length_eq_count (bottomCount : Nat) (partner : List Nat) :
    (capLargerFeetIndices bottomCount partner).length
      = countTrue (capLargerGuard bottomCount partner) (List.range bottomCount) :=
  filterMapLength_eq_countTrue
    (fun index => match capLargerGuard bottomCount partner index with | true => some index | false => none)
    (capLargerGuard bottomCount partner)
    (fun value => (guardIsSomeAgreeCount (capLargerGuard bottomCount partner value) value).symm)
    (List.range bottomCount)

/-! ## Section 7 — filterMap completeness (K3) + the first-occurrence erase equal-members length bound (K4) -/

private theorem memConsOfNeCount (value head : Nat) (rest : List Nat) (mem : value ∈ head :: rest)
    (ne : value ≠ head) : value ∈ rest := by
  cases mem with
  | head => exact absurd rfl ne
  | tail _ memRest => exact memRest

/-- The identity-guard `filterMap` transform sends a guard-`true` head to `some head`. -/
private def guardIdentityTransform (guard : Nat → Bool) (candidate : Nat) : Option Nat :=
  match guard candidate with | true => some candidate | false => none

private theorem guardIdentityTransform_true (guard : Nat → Bool) (candidate : Nat)
    (guardTrue : guard candidate = true) : guardIdentityTransform guard candidate = some candidate := by
  show (match guard candidate with | true => some candidate | false => none) = some candidate
  rw [guardTrue]

private theorem guardIdentityTransform_false (guard : Nat → Bool) (candidate : Nat)
    (guardFalse : guard candidate = false) : guardIdentityTransform guard candidate = none := by
  show (match guard candidate with | true => some candidate | false => none) = none
  rw [guardFalse]

/-- ★ **Guard-shaped `filterMap` completeness.**  If `guard value = true` and `value ∈ source`, then `value` is
emitted by the identity-guard `filterMap` — the reverse of the enumeration soundness (`memFilterMapInvertedEnum`),
the "no missing arc" direction. -/
theorem memFilterMapGuardComplete (guard : Nat → Bool) : (source : List Nat) → (value : Nat) →
    value ∈ source → guard value = true →
    value ∈ source.filterMap (guardIdentityTransform guard)
  | [], _, memNil, _ => nomatch memNil
  | head :: rest, value, memCons, guardTrue => by
      cases headGuard : guard head with
      | true =>
          rw [filterMapConsSomeCount (guardIdentityTransform guard) head head rest
            (guardIdentityTransform_true guard head headGuard)]
          cases hbeq : Nat.beq head value with
          | true =>
              have headEq : head = value := eqOfNatBeqTrueCount head value hbeq
              rw [headEq]; exact List.Mem.head _
          | false =>
              have valueNeHead : value ≠ head :=
                fun equal => (neOfNatBeqFalseCount head value hbeq) equal.symm
              have memRest : value ∈ rest := memConsOfNeCount value head rest memCons valueNeHead
              exact List.Mem.tail _ (memFilterMapGuardComplete guard rest value memRest guardTrue)
      | false =>
          have valueNeHead : value ≠ head := fun equal => Bool.noConfusion (headGuard.symm.trans (equal ▸ guardTrue))
          have memRest : value ∈ rest := memConsOfNeCount value head rest memCons valueNeHead
          rw [filterMapConsNoneCount (guardIdentityTransform guard) head rest
            (guardIdentityTransform_false guard head headGuard)]
          exact memFilterMapGuardComplete guard rest value memRest guardTrue

private def natListErasePermCount : List Nat → Nat → List Nat
  | [], _ => []
  | head :: rest, value =>
      match Nat.beq head value with
      | true => rest
      | false => head :: natListErasePermCount rest value

private theorem natListErasePermCount_cons_true (head value : Nat) (rest : List Nat)
    (hbeq : Nat.beq head value = true) : natListErasePermCount (head :: rest) value = rest := by
  show (match Nat.beq head value with | true => rest | false => head :: natListErasePermCount rest value) = rest
  rw [hbeq]

private theorem natListErasePermCount_cons_false (head value : Nat) (rest : List Nat)
    (hbeq : Nat.beq head value = false) :
    natListErasePermCount (head :: rest) value = head :: natListErasePermCount rest value := by
  show (match Nat.beq head value with | true => rest | false => head :: natListErasePermCount rest value)
    = head :: natListErasePermCount rest value
  rw [hbeq]

private theorem memBoolNatListErasePermCount_ne : (entries : List Nat) → (value other : Nat) →
    Nat.beq value other = false → memBool other (natListErasePermCount entries value) = memBool other entries
  | [], _, _, _ => rfl
  | head :: rest, value, other, valueOtherNe => by
      cases hbeq : Nat.beq head value with
      | true =>
          have headEqValue : head = value := eqOfNatBeqTrueCount head value hbeq
          rw [natListErasePermCount_cons_true head value rest hbeq]
          show memBool other rest = (Nat.beq head other || memBool other rest)
          have headOtherFalse : Nat.beq head other = false := by rw [headEqValue]; exact valueOtherNe
          rw [headOtherFalse, Bool.false_or]
      | false =>
          rw [natListErasePermCount_cons_false head value rest hbeq]
          show (Nat.beq head other || memBool other (natListErasePermCount rest value))
            = (Nat.beq head other || memBool other rest)
          rw [memBoolNatListErasePermCount_ne rest value other valueOtherNe]

private theorem memBoolNatListErasePermCount_self : (entries : List Nat) → (value : Nat) →
    isDistinctList entries = true → memBool value (natListErasePermCount entries value) = false
  | [], _, _ => rfl
  | head :: rest, value, distinct => by
      have splitDist : isDistinctList (head :: rest) = (not (memBool head rest) && isDistinctList rest) := rfl
      rw [splitDist] at distinct
      have headNotMem : memBool head rest = false :=
        eqFalseOfNotTrueCount (memBool head rest) (boolAndLeftCount _ _ distinct)
      have distRest : isDistinctList rest = true := boolAndRightCount _ _ distinct
      cases hbeq : Nat.beq head value with
      | true =>
          have headEqValue : head = value := eqOfNatBeqTrueCount head value hbeq
          rw [natListErasePermCount_cons_true head value rest hbeq, ← headEqValue]
          exact headNotMem
      | false =>
          rw [natListErasePermCount_cons_false head value rest hbeq]
          show (Nat.beq head value || memBool value (natListErasePermCount rest value)) = false
          rw [hbeq, Bool.false_or]
          exact memBoolNatListErasePermCount_self rest value distRest

private theorem isDistinctListNatListErasePermCount : (entries : List Nat) → (value : Nat) →
    isDistinctList entries = true → isDistinctList (natListErasePermCount entries value) = true
  | [], _, _ => rfl
  | head :: rest, value, distinct => by
      have splitDist : isDistinctList (head :: rest) = (not (memBool head rest) && isDistinctList rest) := rfl
      rw [splitDist] at distinct
      have headNotMem : memBool head rest = false :=
        eqFalseOfNotTrueCount (memBool head rest) (boolAndLeftCount _ _ distinct)
      have distRest : isDistinctList rest = true := boolAndRightCount _ _ distinct
      cases hbeq : Nat.beq head value with
      | true =>
          rw [natListErasePermCount_cons_true head value rest hbeq]; exact distRest
      | false =>
          rw [natListErasePermCount_cons_false head value rest hbeq]
          show (not (memBool head (natListErasePermCount rest value))
            && isDistinctList (natListErasePermCount rest value)) = true
          have valueHeadNe : Nat.beq value head = false :=
            natBeqFalseOfNeCount value head (fun equal => (neOfNatBeqFalseCount head value hbeq) equal.symm)
          have headNotMemErase : memBool head (natListErasePermCount rest value) = false := by
            rw [memBoolNatListErasePermCount_ne rest value head valueHeadNe]; exact headNotMem
          have distErase : isDistinctList (natListErasePermCount rest value) = true :=
            isDistinctListNatListErasePermCount rest value distRest
          rw [headNotMemErase, distErase]; rfl

private theorem natListErasePermCount_length_of_mem : (entries : List Nat) → (value : Nat) →
    memBool value entries = true → (natListErasePermCount entries value).length + 1 = entries.length
  | [], _, memTrue => Bool.noConfusion memTrue
  | head :: rest, value, memTrue => by
      cases hbeq : Nat.beq head value with
      | true =>
          rw [natListErasePermCount_cons_true head value rest hbeq]; rfl
      | false =>
          rw [natListErasePermCount_cons_false head value rest hbeq]
          have memRest : memBool value rest = true := by
            have split : memBool value (head :: rest) = (Nat.beq head value || memBool value rest) := rfl
            rw [split, hbeq, Bool.false_or] at memTrue; exact memTrue
          show (natListErasePermCount rest value).length + 1 + 1 = rest.length + 1
          rw [natListErasePermCount_length_of_mem rest value memRest]

/-- ★★ **Equal-members equal-length (the pigeonhole bijection core).**  Two distinct lists with the same boolean
membership on every value have the same length — the cleanest realization of "an injection with an inverse gives
`|A| = |B|`" over the first-occurrence erase kit.  The load-bearing lemma the pairing bijection rests on. -/
theorem distinctSameMembersLengthEq : (left right : List Nat) →
    isDistinctList left = true → isDistinctList right = true →
    (∀ value, memBool value left = memBool value right) → left.length = right.length
  | [], right, _, _, sameMem => by
      cases right with
      | nil => rfl
      | cons headRight restRight =>
          have h : (false : Bool) = true := by
            have step : memBool headRight ([] : List Nat) = memBool headRight (headRight :: restRight) := sameMem headRight
            rw [memBoolOfMemCount (headRight :: restRight) headRight (List.Mem.head restRight)] at step
            exact step
          exact Bool.noConfusion h
  | headLeft :: restLeft, right, distLeft, distRight, sameMem => by
      have headLeftMemRight : memBool headLeft right = true := by
        rw [← sameMem headLeft]; exact memBoolOfMemCount _ headLeft (List.Mem.head restLeft)
      have distRestLeft : isDistinctList restLeft = true := boolAndRightCount _ _ distLeft
      have distRightErase : isDistinctList (natListErasePermCount right headLeft) = true :=
        isDistinctListNatListErasePermCount right headLeft distRight
      have sameMemErase : ∀ value,
          memBool value restLeft = memBool value (natListErasePermCount right headLeft) := by
        intro value
        cases hbeq : Nat.beq headLeft value with
        | true =>
            have valueEq : headLeft = value := eqOfNatBeqTrueCount headLeft value hbeq
            have headNotRest : memBool headLeft restLeft = false :=
              eqFalseOfNotTrueCount _ (boolAndLeftCount _ _ distLeft)
            have eraseSelf : memBool headLeft (natListErasePermCount right headLeft) = false :=
              memBoolNatListErasePermCount_self right headLeft distRight
            rw [← valueEq, headNotRest, eraseSelf]
        | false =>
            have memLeftSplit : memBool value (headLeft :: restLeft) = memBool value restLeft := by
              show (Nat.beq headLeft value || memBool value restLeft) = memBool value restLeft
              rw [hbeq, Bool.false_or]
            have memEraseEq : memBool value (natListErasePermCount right headLeft) = memBool value right :=
              memBoolNatListErasePermCount_ne right headLeft value hbeq
            rw [← memLeftSplit, sameMem value, ← memEraseEq]
      have ihLen : restLeft.length = (natListErasePermCount right headLeft).length :=
        distinctSameMembersLengthEq restLeft (natListErasePermCount right headLeft)
          distRestLeft distRightErase sameMemErase
      show restLeft.length + 1 = right.length
      rw [ihLen, natListErasePermCount_length_of_mem right headLeft headLeftMemRight]

/-! ## Section 8 — the pairing bijection: `|larger cap feet| = |smaller cap feet|` (the crux-of-crux)

The involution maps the smaller foot of each cap arc to its larger foot bijectively.  Realized over the erase-kit
length equality (`distinctSameMembersLengthEq`) by exhibiting `capLargerFeetIndices` and `capArcFeetIndices.map
partner` as two distinct lists with the same members. -/

private theorem natLeOfBleCount : (small large : Nat) → Nat.ble small large = true → small ≤ large
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, hble => Bool.noConfusion hble
  | small + 1, large + 1, hble => Nat.succ_le_succ (natLeOfBleCount small large hble)

private theorem natLtOfBltCount (small large : Nat) (hblt : Nat.blt small large = true) : small < large :=
  natLeOfBleCount (small + 1) large hblt

private theorem boolEqOfImpCount : (leftFlag rightFlag : Bool) →
    (leftFlag = true → rightFlag = true) → (rightFlag = true → leftFlag = true) → leftFlag = rightFlag
  | true, true, _, _ => rfl
  | true, false, forward, _ => Bool.noConfusion (forward rfl)
  | false, true, _, backward => Bool.noConfusion (backward rfl)
  | false, false, _, _ => rfl

/-- Membership in a guard-shaped `filterMap` inverts to a source member that the guard accepts. -/
private theorem memFilterMapGuardInvertedCount (guard : Nat → Bool) : (source : List Nat) → (value : Nat) →
    value ∈ source.filterMap (guardIdentityTransform guard) → value ∈ source ∧ guard value = true
  | [], _, memNil => nomatch memNil
  | head :: rest, value, mem => by
      cases headGuard : guard head with
      | false =>
          rw [filterMapConsNoneCount (guardIdentityTransform guard) head rest
            (guardIdentityTransform_false guard head headGuard)] at mem
          obtain ⟨memRest, guardVal⟩ := memFilterMapGuardInvertedCount guard rest value mem
          exact ⟨List.Mem.tail head memRest, guardVal⟩
      | true =>
          rw [filterMapConsSomeCount (guardIdentityTransform guard) head head rest
            (guardIdentityTransform_true guard head headGuard)] at mem
          cases mem with
          | head => exact ⟨List.Mem.head rest, headGuard⟩
          | tail _ memRest =>
              obtain ⟨memR, guardVal⟩ := memFilterMapGuardInvertedCount guard rest value memRest
              exact ⟨List.Mem.tail head memR, guardVal⟩

private theorem memBoolFilterMapGuardSubsetCount (guard : Nat → Bool) (source : List Nat) (value : Nat)
    (mem : memBool value (source.filterMap (guardIdentityTransform guard)) = true) : memBool value source = true :=
  memBoolOfMemCount source value
    (memFilterMapGuardInvertedCount guard source value (memBoolMemCount _ value mem)).1

private theorem filterMapGuardIdentityDistinctCount (guard : Nat → Bool) : (source : List Nat) →
    isDistinctList source = true → isDistinctList (source.filterMap (guardIdentityTransform guard)) = true
  | [], _ => rfl
  | head :: rest, srcDistinct => by
      have splitDist : isDistinctList (head :: rest) = (not (memBool head rest) && isDistinctList rest) := rfl
      rw [splitDist] at srcDistinct
      have headNotRest : memBool head rest = false :=
        eqFalseOfNotTrueCount _ (boolAndLeftCount _ _ srcDistinct)
      have distRest : isDistinctList rest = true := boolAndRightCount _ _ srcDistinct
      have distFilterRest : isDistinctList (rest.filterMap (guardIdentityTransform guard)) = true :=
        filterMapGuardIdentityDistinctCount guard rest distRest
      cases headGuard : guard head with
      | false =>
          rw [filterMapConsNoneCount (guardIdentityTransform guard) head rest
            (guardIdentityTransform_false guard head headGuard)]
          exact distFilterRest
      | true =>
          rw [filterMapConsSomeCount (guardIdentityTransform guard) head head rest
            (guardIdentityTransform_true guard head headGuard)]
          show (not (memBool head (rest.filterMap (guardIdentityTransform guard)))
            && isDistinctList (rest.filterMap (guardIdentityTransform guard))) = true
          have headNotFilterRest : memBool head (rest.filterMap (guardIdentityTransform guard)) = false := by
            cases hmem : memBool head (rest.filterMap (guardIdentityTransform guard)) with
            | false => rfl
            | true =>
                have headMemRest : memBool head rest = true :=
                  memBoolFilterMapGuardSubsetCount guard rest head hmem
                rw [headNotRest] at headMemRest; exact Bool.noConfusion headMemRest
          rw [headNotFilterRest, distFilterRest]; rfl

private theorem distinctRangeLoopCount : (count : Nat) → (accumulated : List Nat) →
    isDistinctList accumulated = true → (∀ value, memBool value accumulated = true → count ≤ value) →
    isDistinctList (List.range.loop count accumulated) = true
  | 0, _, accDist, _ => accDist
  | count + 1, accumulated, accDist, accGe => by
      apply distinctRangeLoopCount count (count :: accumulated)
      · show (not (memBool count accumulated) && isDistinctList accumulated) = true
        have countNotAcc : memBool count accumulated = false := by
          cases hmem : memBool count accumulated with
          | false => rfl
          | true => exact absurd (accGe count hmem) (Nat.not_succ_le_self count)
        rw [countNotAcc, accDist]; rfl
      · intro value valueMem
        have split : memBool value (count :: accumulated) = (Nat.beq count value || memBool value accumulated) := rfl
        rw [split] at valueMem
        cases hbeq : Nat.beq count value with
        | true => exact Nat.le_of_eq (eqOfNatBeqTrueCount count value hbeq)
        | false =>
            have valueAcc : memBool value accumulated = true := by rw [hbeq, Bool.false_or] at valueMem; exact valueMem
            exact Nat.le_of_succ_le (accGe value valueAcc)

private theorem isDistinctListRangeCount (count : Nat) : isDistinctList (List.range count) = true :=
  distinctRangeLoopCount count [] rfl (fun _ valueMem => Bool.noConfusion valueMem)

private theorem mapDistinctOfInjOnCount (mapFn : Nat → Nat) : (entries : List Nat) →
    isDistinctList entries = true →
    (∀ left right, left ∈ entries → right ∈ entries → mapFn left = mapFn right → left = right) →
    isDistinctList (entries.map mapFn) = true
  | [], _, _ => rfl
  | head :: rest, distinct, injOn => by
      have splitDist : isDistinctList (head :: rest) = (not (memBool head rest) && isDistinctList rest) := rfl
      rw [splitDist] at distinct
      have headNotRest : memBool head rest = false :=
        eqFalseOfNotTrueCount _ (boolAndLeftCount _ _ distinct)
      have distRest : isDistinctList rest = true := boolAndRightCount _ _ distinct
      have distMapRest : isDistinctList (rest.map mapFn) = true :=
        mapDistinctOfInjOnCount mapFn rest distRest
          (fun left right leftMem rightMem eqMap =>
            injOn left right (List.Mem.tail head leftMem) (List.Mem.tail head rightMem) eqMap)
      show (not (memBool (mapFn head) (rest.map mapFn)) && isDistinctList (rest.map mapFn)) = true
      have headNotMapRest : memBool (mapFn head) (rest.map mapFn) = false := by
        cases hmem : memBool (mapFn head) (rest.map mapFn) with
        | false => rfl
        | true =>
            obtain ⟨preimage, preMem, preEq⟩ := memBoolMapWitnessCount mapFn rest (mapFn head) hmem
            have headEqPre : head = preimage :=
              injOn head preimage (List.Mem.head rest) (List.Mem.tail head preMem) preEq.symm
            have headMemRest : memBool head rest = true := by
              rw [headEqPre]; exact memBoolOfMemCount rest preimage preMem
            rw [headNotRest] at headMemRest; exact Bool.noConfusion headMemRest
      rw [headNotMapRest, distMapRest]; rfl

/-- ★★ **The pairing bijection (crux-of-crux).**  Under the involution gate, the number of LARGER cap feet equals the
number of SMALLER cap feet: `partner` bijects `capArcFeetIndices` onto `capLargerFeetIndices`.  Realized via the
erase-kit length equality on `capLargerFeetIndices` and `capArcFeetIndices.map partner` (two distinct lists with the
same members).  The heart of the width-length identity — `|larger| = |smaller|`. -/
theorem capLargerFeetIndices_length_eq (bottomCount total : Nat) (partner : List Nat)
    (bottomLe : bottomCount ≤ total) (wf : IsBoundaryInvolution total partner) :
    (capLargerFeetIndices bottomCount partner).length = (capArcFeetIndices bottomCount partner).length := by
  have sameMembers : ∀ value, memBool value (capLargerFeetIndices bottomCount partner)
      = memBool value ((capArcFeetIndices bottomCount partner).map (natListGetAt partner)) := by
    intro value
    apply boolEqOfImpCount
    · intro valueMemLarger
      have valueMem : value ∈ capLargerFeetIndices bottomCount partner := memBoolMemCount _ value valueMemLarger
      obtain ⟨valueRange, valueLargerGuard⟩ :=
        memFilterMapGuardInvertedCount (capLargerGuard bottomCount partner) (List.range bottomCount) value valueMem
      have valueLt : value < bottomCount := memRangeLtCount valueRange
      have valueLtTotal : value < total := Nat.lt_of_lt_of_le valueLt bottomLe
      have partnerValueLtBc : natListGetAt partner value < bottomCount :=
        natLtOfBltCount (natListGetAt partner value) bottomCount (boolAndLeftCount _ _ valueLargerGuard)
      have partnerValueLtValue : natListGetAt partner value < value :=
        natLtOfBltCount (natListGetAt partner value) value (boolAndRightCount _ _ valueLargerGuard)
      have selfInv : natListGetAt partner (natListGetAt partner value) = value := wf.isSelfInverse value valueLtTotal
      have partnerValueRange : natListGetAt partner value ∈ List.range bottomCount :=
        memRangeOfLtCount (natListGetAt partner value) bottomCount partnerValueLtBc
      have smallerGuardPartnerValue : capSmallerGuard bottomCount partner (natListGetAt partner value) = true := by
        show (Nat.blt (natListGetAt partner (natListGetAt partner value)) bottomCount
          && Nat.blt (natListGetAt partner value) (natListGetAt partner (natListGetAt partner value))) = true
        rw [selfInv]
        exact andEqTrueCount _ _ (natBltOfLtCount value bottomCount valueLt)
          (natBltOfLtCount (natListGetAt partner value) value partnerValueLtValue)
      have partnerValueMemCap : natListGetAt partner value ∈ capArcFeetIndices bottomCount partner :=
        memFilterMapGuardComplete (capSmallerGuard bottomCount partner) (List.range bottomCount)
          (natListGetAt partner value) partnerValueRange smallerGuardPartnerValue
      have mapMem : memBool (natListGetAt partner (natListGetAt partner value))
          ((capArcFeetIndices bottomCount partner).map (natListGetAt partner)) = true :=
        memBoolMapOfMemCount (natListGetAt partner) (capArcFeetIndices bottomCount partner)
          (natListGetAt partner value) partnerValueMemCap
      rw [selfInv] at mapMem
      exact mapMem
    · intro valueMemMap
      obtain ⟨smallerFoot, smallerFootMemCap, smallerFootPartnerEq⟩ :=
        memBoolMapWitnessCount (natListGetAt partner) (capArcFeetIndices bottomCount partner) value valueMemMap
      have smallerSound := capArcFeetIndices_mem_sound bottomCount partner smallerFoot smallerFootMemCap
      have smallerLtTotal : smallerFoot < total := Nat.lt_of_lt_of_le smallerSound.1 bottomLe
      have selfInvSmaller : natListGetAt partner (natListGetAt partner smallerFoot) = smallerFoot :=
        wf.isSelfInverse smallerFoot smallerLtTotal
      have valueRange : value ∈ List.range bottomCount := by
        rw [← smallerFootPartnerEq]
        exact memRangeOfLtCount (natListGetAt partner smallerFoot) bottomCount smallerSound.2.1
      have largerGuardValue : capLargerGuard bottomCount partner value = true := by
        rw [← smallerFootPartnerEq]
        show (Nat.blt (natListGetAt partner (natListGetAt partner smallerFoot)) bottomCount
          && Nat.blt (natListGetAt partner (natListGetAt partner smallerFoot)) (natListGetAt partner smallerFoot)) = true
        rw [selfInvSmaller]
        exact andEqTrueCount _ _ (natBltOfLtCount smallerFoot bottomCount smallerSound.1)
          (natBltOfLtCount smallerFoot (natListGetAt partner smallerFoot) smallerSound.2.2)
      have valueMemLarger : value ∈ capLargerFeetIndices bottomCount partner :=
        memFilterMapGuardComplete (capLargerGuard bottomCount partner) (List.range bottomCount)
          value valueRange largerGuardValue
      exact memBoolOfMemCount _ value valueMemLarger
  have distinctLarger : isDistinctList (capLargerFeetIndices bottomCount partner) = true :=
    filterMapGuardIdentityDistinctCount (capLargerGuard bottomCount partner) (List.range bottomCount)
      (isDistinctListRangeCount bottomCount)
  have distinctMap : isDistinctList ((capArcFeetIndices bottomCount partner).map (natListGetAt partner)) = true :=
    mapDistinctOfInjOnCount (natListGetAt partner) (capArcFeetIndices bottomCount partner)
      (filterMapGuardIdentityDistinctCount (capSmallerGuard bottomCount partner) (List.range bottomCount)
        (isDistinctListRangeCount bottomCount))
      (fun left right leftMem rightMem eqMap => involutionInjectiveCount total partner wf left right
        (Nat.lt_of_lt_of_le (capArcFeetIndices_mem_sound bottomCount partner left leftMem).1 bottomLe)
        (Nat.lt_of_lt_of_le (capArcFeetIndices_mem_sound bottomCount partner right rightMem).1 bottomLe) eqMap)
  have lengthEq : (capLargerFeetIndices bottomCount partner).length
      = ((capArcFeetIndices bottomCount partner).map (natListGetAt partner)).length :=
    distinctSameMembersLengthEq (capLargerFeetIndices bottomCount partner)
      ((capArcFeetIndices bottomCount partner).map (natListGetAt partner)) distinctLarger distinctMap sameMembers
  rw [lengthEq, mapLengthCount]

end FX1Poly.Polygraph
