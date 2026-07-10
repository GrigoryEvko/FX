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

/-! ## Section 9 — the crux `2·|caps| + |through| = bottomCount` and the bottom read-off width-length identity -/

private theorem appendLengthCount : (left right : List Nat) →
    (left ++ right).length = left.length + right.length
  | [], right => (Nat.zero_add right.length).symm
  | head :: rest, right => by
      show (rest ++ right).length + 1 = (rest.length + 1) + right.length
      rw [appendLengthCount rest right]
      exact (Nat.succ_add rest.length right.length).symm

private theorem twoSuccArithCount (value : Nat) : value + value + 1 + 1 = (value + 1) + (value + 1) := by
  rw [Nat.add_succ (value + 1) value, Nat.succ_add value value]

private theorem rangeLoopLengthCount : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      show (List.range.loop count (count :: accumulated)).length = (count + 1) + accumulated.length
      rw [rangeLoopLengthCount count (count :: accumulated)]
      show count + (accumulated.length + 1) = (count + 1) + accumulated.length
      rw [Nat.add_succ, Nat.succ_add]

private theorem lengthRangeCount (count : Nat) : (List.range count).length = count :=
  (rangeLoopLengthCount count []).trans (Nat.add_zero count)

/-- ★★ **The doubling — `|capArcFeet| = 2·|capArcFeetIndices|`.**  Each cap arc contributes two feet, so the flat foot
list has twice the arc-index length (in `+`-form, avoiding `Nat.mul`). -/
theorem expandBottomFeetPairs_length (partner : List Nat) : (feet : List Nat) →
    (expandBottomFeetPairs partner feet).length = feet.length + feet.length
  | [] => rfl
  | index :: rest => by
      show (expandBottomFeetPairs partner rest).length + 1 + 1 = (rest.length + 1) + (rest.length + 1)
      rw [expandBottomFeetPairs_length partner rest]
      exact twoSuccArithCount rest.length

/-- ★★ **The crux — `2·|capArcFeetIndices| + |throughStrandBottoms| = bottomCount`.**  Assembles the pairing bijection
(`|larger| = |smaller|`) with the three-way partition count over `List.range bottomCount`: the smaller feet, the
larger feet, and the through bottoms exhaust the bottom boundary, and the two cap classes have equal cardinality. -/
theorem capArcFeetTwiceThroughSumsToBottom (bottomCount total : Nat) (partner : List Nat)
    (bottomLe : bottomCount ≤ total) (wf : IsBoundaryInvolution total partner) :
    (capArcFeetIndices bottomCount partner).length + (capArcFeetIndices bottomCount partner).length
      + (throughStrandBottoms bottomCount partner).length = bottomCount := by
  have pairing : countTrue (capLargerGuard bottomCount partner) (List.range bottomCount)
      = countTrue (capSmallerGuard bottomCount partner) (List.range bottomCount) := by
    rw [← capLargerFeetIndices_length_eq_count, ← capArcFeetIndices_length_eq_count]
    exact capLargerFeetIndices_length_eq bottomCount total partner bottomLe wf
  have partition : countTrue (capSmallerGuard bottomCount partner) (List.range bottomCount)
      + countTrue (capLargerGuard bottomCount partner) (List.range bottomCount)
      + countTrue (throughBottomGuard bottomCount partner) (List.range bottomCount)
      = bottomCount :=
    (partitionCountThree (capSmallerGuard bottomCount partner) (capLargerGuard bottomCount partner)
      (throughBottomGuard bottomCount partner) (List.range bottomCount)
      (fun value valueMem => partitionThree_of_involution bottomCount total partner bottomLe wf value
        (memRangeLtCount valueMem))).trans (lengthRangeCount bottomCount)
  rw [capArcFeetIndices_length_eq_count, throughStrandBottoms_length_eq_count]
  exact pairing ▸ partition

/-- ★★★ **The bottom read-off width-length identity (`hasWidthLength`).**  For every well-formed involution partner,
`(capArcFeet ++ throughStrandBottoms).length = bottomCount` — the counting field the general
`IsPermutationOfRange` was missing.  From the doubling (`expandBottomFeetPairs_length`), the append length, and the
crux. -/
theorem bottomReadOffOrderLength (bottomCount total : Nat) (partner : List Nat)
    (bottomLe : bottomCount ≤ total) (wf : IsBoundaryInvolution total partner) :
    (capArcFeet bottomCount partner ++ throughStrandBottoms bottomCount partner).length = bottomCount := by
  rw [appendLengthCount]
  show (expandBottomFeetPairs partner (capArcFeetIndices bottomCount partner)).length
    + (throughStrandBottoms bottomCount partner).length = bottomCount
  rw [expandBottomFeetPairs_length partner (capArcFeetIndices bottomCount partner)]
  exact capArcFeetTwiceThroughSumsToBottom bottomCount total partner bottomLe wf

/-! ## Section 10 — the bottom read-off boundedness (`isBounded`) -/

private theorem memAppendCount (value : Nat) : (left right : List Nat) →
    value ∈ left ++ right → value ∈ left ∨ value ∈ right
  | [], right, mem => Or.inr mem
  | head :: rest, right, mem => by
      have memReduced : value ∈ head :: (rest ++ right) := mem
      cases memReduced with
      | head => exact Or.inl (List.Mem.head rest)
      | tail _ memRest =>
          cases memAppendCount value rest right memRest with
          | inl memLeft => exact Or.inl (List.Mem.tail head memLeft)
          | inr memRight => exact Or.inr memRight

private theorem mem_expandBottomFeetPairsCount (partner : List Nat) : (feet : List Nat) → (value : Nat) →
    value ∈ expandBottomFeetPairs partner feet →
    ∃ foot, foot ∈ feet ∧ (value = foot ∨ value = natListGetAt partner foot)
  | [], _, memNil => nomatch memNil
  | index :: rest, value, mem => by
      have memReduced : value ∈ index :: natListGetAt partner index :: expandBottomFeetPairs partner rest := mem
      cases memReduced with
      | head => exact ⟨index, List.Mem.head rest, Or.inl rfl⟩
      | tail _ memTail =>
          cases memTail with
          | head => exact ⟨index, List.Mem.head rest, Or.inr rfl⟩
          | tail _ memRest =>
              obtain ⟨foot, footMem, footEq⟩ := mem_expandBottomFeetPairsCount partner rest value memRest
              exact ⟨foot, List.Mem.tail index footMem, footEq⟩

private theorem getAtMemCount : (entries : List Nat) → (index : Nat) → index < entries.length →
    natListGetAt entries index ∈ entries
  | [], index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | _ :: _, 0, _ => List.Mem.head _
  | head :: rest, index + 1, indexBelow =>
      List.Mem.tail head (getAtMemCount rest index (Nat.lt_of_succ_lt_succ indexBelow))

/-- Every member of the bottom read-off order is a bottom port (`< bottomCount`) — cap feet by cap soundness (foot and
its partner), through bottoms by through soundness.  Involution-free. -/
theorem memberBoundedBottomReadOff (bottomCount : Nat) (partner : List Nat) (value : Nat)
    (mem : value ∈ capArcFeet bottomCount partner ++ throughStrandBottoms bottomCount partner) :
    value < bottomCount := by
  cases memAppendCount value (capArcFeet bottomCount partner) (throughStrandBottoms bottomCount partner) mem with
  | inl memCap =>
      obtain ⟨foot, footMem, footEq⟩ :=
        mem_expandBottomFeetPairsCount partner (capArcFeetIndices bottomCount partner) value memCap
      have footSound := capArcFeetIndices_mem_sound bottomCount partner foot footMem
      cases footEq with
      | inl valueEqFoot => rw [valueEqFoot]; exact footSound.1
      | inr valueEqPartnerFoot => rw [valueEqPartnerFoot]; exact footSound.2.1
  | inr memThrough =>
      exact (throughStrandBottoms_mem_sound bottomCount partner value memThrough).1

/-- ★ **The bottom read-off boundedness (`isBounded`).**  At every in-range position the bottom read-off order reads a
bottom port.  From the width-length identity (so the index is in range) and member-boundedness. -/
theorem bottomReadOffOrderBounded (bottomCount total : Nat) (partner : List Nat)
    (bottomLe : bottomCount ≤ total) (wf : IsBoundaryInvolution total partner) (index : Nat)
    (indexBelow : index < bottomCount) :
    natListGetAt (capArcFeet bottomCount partner ++ throughStrandBottoms bottomCount partner) index < bottomCount := by
  have indexInRange : index
      < (capArcFeet bottomCount partner ++ throughStrandBottoms bottomCount partner).length := by
    rw [bottomReadOffOrderLength bottomCount total partner bottomLe wf]; exact indexBelow
  exact memberBoundedBottomReadOff bottomCount partner _
    (getAtMemCount (capArcFeet bottomCount partner ++ throughStrandBottoms bottomCount partner) index indexInRange)

/-! ## Section 11 — the bottom read-off distinctness (`isDistinct`): interleaved cap feet, distinct throughs, disjoint -/

private theorem memBoolAppendCount (value : Nat) : (left right : List Nat) →
    memBool value (left ++ right) = (memBool value left || memBool value right)
  | [], _ => rfl
  | head :: rest, right => by
      show (Nat.beq head value || memBool value (rest ++ right))
        = ((Nat.beq head value || memBool value rest) || memBool value right)
      cases Nat.beq head value with
      | true => rfl
      | false =>
          show memBool value (rest ++ right) = (memBool value rest || memBool value right)
          exact memBoolAppendCount value rest right

private theorem appendDistinctCount : (left right : List Nat) →
    isDistinctList left = true → isDistinctList right = true →
    (∀ value, memBool value left = true → memBool value right = false) →
    isDistinctList (left ++ right) = true
  | [], _, _, distRight, _ => distRight
  | head :: rest, right, distLeft, distRight, disjoint => by
      have splitDist : isDistinctList (head :: rest) = (not (memBool head rest) && isDistinctList rest) := rfl
      rw [splitDist] at distLeft
      have headNotRest : memBool head rest = false :=
        eqFalseOfNotTrueCount _ (boolAndLeftCount _ _ distLeft)
      have distRest : isDistinctList rest = true := boolAndRightCount _ _ distLeft
      have headMemLeft : memBool head (head :: rest) = true := by
        show (Nat.beq head head || memBool head rest) = true
        rw [natBeqSelfCount]; rfl
      have headNotRight : memBool head right = false := disjoint head headMemLeft
      have disjointRest : ∀ value, memBool value rest = true → memBool value right = false := by
        intro value valueMem
        have valueMemLeft : memBool value (head :: rest) = true := by
          show (Nat.beq head value || memBool value rest) = true
          rw [valueMem, Bool.or_true]
        exact disjoint value valueMemLeft
      have distRestAppend : isDistinctList (rest ++ right) = true :=
        appendDistinctCount rest right distRest distRight disjointRest
      show (not (memBool head (rest ++ right)) && isDistinctList (rest ++ right)) = true
      have headNotRestAppend : memBool head (rest ++ right) = false := by
        rw [memBoolAppendCount head rest right, headNotRest, Bool.false_or, headNotRight]
      rw [headNotRestAppend]
      show isDistinctList (rest ++ right) = true
      exact distRestAppend

private theorem capFootPartnerLtBc (bottomCount total : Nat) (partner : List Nat) (bottomLe : bottomCount ≤ total)
    (wf : IsBoundaryInvolution total partner) (value : Nat) (mem : value ∈ capArcFeet bottomCount partner) :
    natListGetAt partner value < bottomCount := by
  obtain ⟨foot, footMem, footEq⟩ :=
    mem_expandBottomFeetPairsCount partner (capArcFeetIndices bottomCount partner) value mem
  have footSound := capArcFeetIndices_mem_sound bottomCount partner foot footMem
  cases footEq with
  | inl valueEqFoot => rw [valueEqFoot]; exact footSound.2.1
  | inr valueEqPartnerFoot =>
      rw [valueEqPartnerFoot, wf.isSelfInverse foot (Nat.lt_of_lt_of_le footSound.1 bottomLe)]
      exact footSound.1

private theorem bottomReadOffDisjoint (bottomCount total : Nat) (partner : List Nat) (bottomLe : bottomCount ≤ total)
    (wf : IsBoundaryInvolution total partner) (value : Nat)
    (memCap : memBool value (capArcFeet bottomCount partner) = true) :
    memBool value (throughStrandBottoms bottomCount partner) = false := by
  cases hmem : memBool value (throughStrandBottoms bottomCount partner) with
  | false => rfl
  | true =>
      have throughSound := throughStrandBottoms_mem_sound bottomCount partner value (memBoolMemCount _ value hmem)
      have partnerLt : natListGetAt partner value < bottomCount :=
        capFootPartnerLtBc bottomCount total partner bottomLe wf value (memBoolMemCount _ value memCap)
      exact absurd (Nat.lt_of_lt_of_le partnerLt throughSound.2) (Nat.lt_irrefl _)

/-- ★★ **The cap-feet interleave is distinct.**  `expandBottomFeetPairs partner feet = [f0, partner f0, f1, …]` is
distinct when `feet` is a distinct list of smaller cap feet: the foot indices are distinct (input distinct), their
partners are distinct (involution injective), and no foot equals a partner (a smaller foot cannot be a larger foot).
The interleaved-pair distinctness the recon flagged as the hidden second chunk. -/
private theorem expandBottomFeetPairsDistinctCount (bottomCount total : Nat) (partner : List Nat)
    (bottomLe : bottomCount ≤ total) (wf : IsBoundaryInvolution total partner) : (feet : List Nat) →
    isDistinctList feet = true →
    (∀ foot, foot ∈ feet → foot < bottomCount ∧ natListGetAt partner foot < bottomCount
      ∧ foot < natListGetAt partner foot) →
    isDistinctList (expandBottomFeetPairs partner feet) = true
  | [], _, _ => rfl
  | index :: rest, feetDistinct, feetSmaller => by
      have splitDist : isDistinctList (index :: rest) = (not (memBool index rest) && isDistinctList rest) := rfl
      rw [splitDist] at feetDistinct
      have indexNotRest : memBool index rest = false :=
        eqFalseOfNotTrueCount _ (boolAndLeftCount _ _ feetDistinct)
      have distRest : isDistinctList rest = true := boolAndRightCount _ _ feetDistinct
      have indexSmaller := feetSmaller index (List.Mem.head rest)
      have restSmaller : ∀ foot, foot ∈ rest → foot < bottomCount ∧ natListGetAt partner foot < bottomCount
          ∧ foot < natListGetAt partner foot :=
        fun foot footMem => feetSmaller foot (List.Mem.tail index footMem)
      have distTail : isDistinctList (expandBottomFeetPairs partner rest) = true :=
        expandBottomFeetPairsDistinctCount bottomCount total partner bottomLe wf rest distRest restSmaller
      have indexLtTotal : index < total := Nat.lt_of_lt_of_le indexSmaller.1 bottomLe
      have selfInvIndex : natListGetAt partner (natListGetAt partner index) = index := wf.isSelfInverse index indexLtTotal
      have partnerIndexNotTail :
          memBool (natListGetAt partner index) (expandBottomFeetPairs partner rest) = false := by
        cases hmem : memBool (natListGetAt partner index) (expandBottomFeetPairs partner rest) with
        | false => rfl
        | true =>
            obtain ⟨collision, collisionMem, collisionEq⟩ := mem_expandBottomFeetPairsCount partner rest
              (natListGetAt partner index) (memBoolMemCount _ _ hmem)
            have collisionSmaller := restSmaller collision collisionMem
            have collisionLtTotal : collision < total := Nat.lt_of_lt_of_le collisionSmaller.1 bottomLe
            cases collisionEq with
            | inl partnerIndexEqCollision =>
                have partnerCollisionEqIndex : natListGetAt partner collision = index := by
                  rw [← partnerIndexEqCollision, selfInvIndex]
                have collisionLtIndex : collision < index := by rw [← partnerCollisionEqIndex]; exact collisionSmaller.2.2
                have indexLtCollision : index < collision := by rw [← partnerIndexEqCollision]; exact indexSmaller.2.2
                exact absurd (Nat.lt_trans collisionLtIndex indexLtCollision) (Nat.lt_irrefl collision)
            | inr partnerIndexEqPartnerCollision =>
                have indexEqCollision : index = collision :=
                  involutionInjectiveCount total partner wf index collision indexLtTotal collisionLtTotal
                    partnerIndexEqPartnerCollision
                have indexMemRest : memBool index rest = true := by
                  rw [indexEqCollision]; exact memBoolOfMemCount rest collision collisionMem
                rw [indexNotRest] at indexMemRest; exact Bool.noConfusion indexMemRest
      have indexNotConsTail :
          memBool index (natListGetAt partner index :: expandBottomFeetPairs partner rest) = false := by
        show (Nat.beq (natListGetAt partner index) index
          || memBool index (expandBottomFeetPairs partner rest)) = false
        have partnerIndexNeIndex : Nat.beq (natListGetAt partner index) index = false :=
          natBeqFalseOfNeCount (natListGetAt partner index) index (by
            intro equal
            have contra : index < index := by
              have step := indexSmaller.2.2
              rw [equal] at step
              exact step
            exact Nat.lt_irrefl index contra)
        rw [partnerIndexNeIndex, Bool.false_or]
        cases hmem : memBool index (expandBottomFeetPairs partner rest) with
        | false => rfl
        | true =>
            obtain ⟨collision, collisionMem, collisionEq⟩ := mem_expandBottomFeetPairsCount partner rest index
              (memBoolMemCount _ _ hmem)
            have collisionSmaller := restSmaller collision collisionMem
            have collisionLtTotal : collision < total := Nat.lt_of_lt_of_le collisionSmaller.1 bottomLe
            cases collisionEq with
            | inl indexEqCollision =>
                have indexMemRest : memBool index rest = true := by
                  rw [indexEqCollision]; exact memBoolOfMemCount rest collision collisionMem
                rw [indexNotRest] at indexMemRest; exact Bool.noConfusion indexMemRest
            | inr indexEqPartnerCollision =>
                have collisionLtIndex : collision < index := by rw [indexEqPartnerCollision]; exact collisionSmaller.2.2
                have partnerIndexEqCollision : natListGetAt partner index = collision := by
                  rw [indexEqPartnerCollision, wf.isSelfInverse collision collisionLtTotal]
                have indexLtCollision : index < collision := by
                  rw [← partnerIndexEqCollision]; exact indexSmaller.2.2
                exact absurd (Nat.lt_trans collisionLtIndex indexLtCollision) (Nat.lt_irrefl collision)
      have distConsTail :
          isDistinctList (natListGetAt partner index :: expandBottomFeetPairs partner rest) = true := by
        show (not (memBool (natListGetAt partner index) (expandBottomFeetPairs partner rest))
          && isDistinctList (expandBottomFeetPairs partner rest)) = true
        rw [partnerIndexNotTail]
        show isDistinctList (expandBottomFeetPairs partner rest) = true
        exact distTail
      show (not (memBool index (natListGetAt partner index :: expandBottomFeetPairs partner rest))
        && isDistinctList (natListGetAt partner index :: expandBottomFeetPairs partner rest)) = true
      rw [indexNotConsTail]
      show isDistinctList (natListGetAt partner index :: expandBottomFeetPairs partner rest) = true
      exact distConsTail

/-- ★★ **The cap-feet order is distinct.** -/
theorem capArcFeet_distinct (bottomCount total : Nat) (partner : List Nat) (bottomLe : bottomCount ≤ total)
    (wf : IsBoundaryInvolution total partner) : isDistinctList (capArcFeet bottomCount partner) = true :=
  expandBottomFeetPairsDistinctCount bottomCount total partner bottomLe wf (capArcFeetIndices bottomCount partner)
    (filterMapGuardIdentityDistinctCount (capSmallerGuard bottomCount partner) (List.range bottomCount)
      (isDistinctListRangeCount bottomCount))
    (fun foot footMem => capArcFeetIndices_mem_sound bottomCount partner foot footMem)

/-- The through-bottom order is distinct (filterMap-identity of the distinct range). -/
theorem throughStrandBottoms_distinct (bottomCount : Nat) (partner : List Nat) :
    isDistinctList (throughStrandBottoms bottomCount partner) = true :=
  filterMapGuardIdentityDistinctCount (throughBottomGuard bottomCount partner) (List.range bottomCount)
    (isDistinctListRangeCount bottomCount)

/-- ★★★ **The bottom read-off distinctness (`isDistinct`).**  `capArcFeet ++ throughStrandBottoms` is distinct: the cap
feet interleave is distinct, the through bottoms are distinct, and the two are disjoint (a cap foot's partner is a
bottom port, so it is never a through bottom). -/
theorem bottomReadOffOrder_distinct (bottomCount total : Nat) (partner : List Nat) (bottomLe : bottomCount ≤ total)
    (wf : IsBoundaryInvolution total partner) :
    isDistinctList (capArcFeet bottomCount partner ++ throughStrandBottoms bottomCount partner) = true :=
  appendDistinctCount (capArcFeet bottomCount partner) (throughStrandBottoms bottomCount partner)
    (capArcFeet_distinct bottomCount total partner bottomLe wf)
    (throughStrandBottoms_distinct bottomCount partner)
    (bottomReadOffDisjoint bottomCount total partner bottomLe wf)

/-! ## Section 12 — the general bottom read-off `IsPermutationOfRange` (T-CLOSE bottom side) -/

/-- ★★★ **The general bottom read-off order is a range-permutation.**  For every well-formed boundary involution over
`bottomCount + topCount` ports, `capArcFeet ++ throughStrandBottoms` satisfies `IsPermutationOfRange bottomCount` —
distinct, length `bottomCount`, `[0, bottomCount)`-bounded.  Promotes the r15 `by decide` truth-probes
(`readOffBottomOrder_isPermutationOfRange_adversarialB` / `_freshMixed`) to the general theorem: the counting residual
the r15 honesty walls named is CLOSED on the bottom side. -/
theorem readOffBottomOrder_isPermutationOfRange (bottomCount topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (bottomCount + topCount) partner) :
    IsPermutationOfRange bottomCount
      (capArcFeet bottomCount partner ++ throughStrandBottoms bottomCount partner) where
  hasWidthLength := bottomReadOffOrderLength bottomCount (bottomCount + topCount) partner
    (Nat.le_add_right bottomCount topCount) wf
  isDistinct := bottomReadOffOrder_distinct bottomCount (bottomCount + topCount) partner
    (Nat.le_add_right bottomCount topCount) wf
  isBounded := bottomReadOffOrderBounded bottomCount (bottomCount + topCount) partner
    (Nat.le_add_right bottomCount topCount) wf

/-! ## Section 13 — the T-CLOSE bottom assembly: the E2 roundtrip fed the general bottom read-off order

The r15 E2 wiring was probe-granular (`permuteOfCrossingWord_permutationToCrossingWord` applied to the `by decide`
witnesses on the adversarial-B / fresh-mixed diagrams).  With the general `readOffBottomOrder_isPermutationOfRange`
in hand, the same conjugator roundtrip fires for EVERY well-formed involution partner — the r15 probe pattern
promoted to a general theorem on the bottom side. -/

/-- ★★★ **The general bottom read-off E2 roundtrip.**  The `permutationToCrossingWord` staircase realizes the bottom
read-off order `capArcFeet ++ throughStrandBottoms` for EVERY well-formed boundary involution — the shipped conjugator
roundtrip `permuteOfCrossingWord_permutationToCrossingWord` fed the general bottom range-permutation witness.  E2
end-to-end on the specific `d`, universally on the bottom side. -/
theorem readOffBottomOrder_realizesRoundtrip (bottomCount topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (bottomCount + topCount) partner) :
    permuteOfCrossingWord bottomCount
        (permutationToCrossingWord bottomCount
          (capArcFeet bottomCount partner ++ throughStrandBottoms bottomCount partner))
      = capArcFeet bottomCount partner ++ throughStrandBottoms bottomCount partner :=
  permuteOfCrossingWord_permutationToCrossingWord bottomCount _
    (readOffBottomOrder_isPermutationOfRange bottomCount topCount partner wf)

/-! ## Section 14 — the TOP-side arithmetic helpers (the offset-port `Nat.sub` / cancel kit, propext-free)

The top read-offs read the partner at the OFFSET port `bottomCount + topIndex` and subtract `bottomCount`, so the
top dual needs the additive cancel lemmas the bottom side never touched.  Re-derived structurally here (never
`Nat.sub_add_cancel` / `Nat.add_left_cancel`, both of which leak `propext`). -/

/-- Left-cancel of `Nat` addition — structural on the left summand, `propext`-free. -/
private theorem natAddLeftCancelTop : (base left right : Nat) → base + left = base + right → left = right
  | 0, left, right, equal => by rw [Nat.zero_add, Nat.zero_add] at equal; exact equal
  | base + 1, left, right, equal => by
      rw [Nat.succ_add base left, Nat.succ_add base right] at equal
      exact natAddLeftCancelTop base left right (Nat.succ.inj equal)

/-- Left-cancel of `Nat` addition under `<` — structural on the left summand, `propext`-free. -/
private theorem natLtOfAddLtAddLeftTop : (base left right : Nat) → base + left < base + right → left < right
  | 0, left, right, lt => by rw [Nat.zero_add, Nat.zero_add] at lt; exact lt
  | base + 1, left, right, lt => by
      rw [Nat.succ_add base left, Nat.succ_add base right] at lt
      exact natLtOfAddLtAddLeftTop base left right (Nat.lt_of_succ_lt_succ lt)

/-- `base ≤ value → base + (value - base) = value` — structural, `propext`-free (the `Nat.le.dest`-style discharge,
never `Nat.sub_add_cancel`). -/
private theorem addSubCancelTop : (base value : Nat) → base ≤ value → base + (value - base) = value
  | 0, value, _ => by rw [Nat.zero_add, Nat.sub_zero]
  | base + 1, 0, le => absurd le (Nat.not_succ_le_zero base)
  | base + 1, value + 1, le => by
      rw [show (value + 1) - (base + 1) = value - base from Nat.succ_sub_succ value base,
        Nat.add_right_comm base 1 (value - base)]
      exact congrArg (· + 1) (addSubCancelTop base value (Nat.le_of_succ_le_succ le))

/-- `(base + value) - base = value` — structural, `propext`-free. -/
private theorem natAddSubCancelLeftTop : (base value : Nat) → (base + value) - base = value
  | 0, value => by rw [Nat.zero_add, Nat.sub_zero]
  | base + 1, value => by
      rw [Nat.succ_add base value, Nat.succ_sub_succ (base + value) base]
      exact natAddSubCancelLeftTop base value

/-! ## Section 15 — the TOP arc-class guard functions (definitionally the offset-port `filterMap` predicates) -/

/-- The SMALLER cup-top guard — a top port `bottomCount + topIndex` whose partner is a top port strictly larger (the
smaller top foot of a top–top cup arc).  Definitionally the `cupArcTopIndices` `filterMap` predicate. -/
def cupSmallerGuard (bottomCount : Nat) (partner : List Nat) (topIndex : Nat) : Bool :=
  Nat.ble bottomCount (natListGetAt partner (bottomCount + topIndex))
    && Nat.blt (bottomCount + topIndex) (natListGetAt partner (bottomCount + topIndex))

/-- The LARGER cup-top guard — a top port whose partner is a top port strictly smaller (the larger top foot of a
top–top cup arc).  The ∗-mirror of `cupSmallerGuard` under swapping the two top feet. -/
def cupLargerGuard (bottomCount : Nat) (partner : List Nat) (topIndex : Nat) : Bool :=
  Nat.ble bottomCount (natListGetAt partner (bottomCount + topIndex))
    && Nat.blt (natListGetAt partner (bottomCount + topIndex)) (bottomCount + topIndex)

/-- The THROUGH-top guard — a top port whose partner is a bottom port.  Definitionally the `throughStrandTops`
`filterMap` predicate. -/
def throughTopGuard (bottomCount : Nat) (partner : List Nat) (topIndex : Nat) : Bool :=
  Nat.blt (natListGetAt partner (bottomCount + topIndex)) bottomCount

/-! ## Section 16 — the ∗-dual per-index classification under the involution gate -/

/-- ★ **The per-index TOP classification under the involution gate.**  Each top port `topIndex < topCount` is exactly
one of a SMALLER cup top, a LARGER cup top, or a THROUGH top — `cupSmallerGuard` / `cupLargerGuard` /
`throughTopGuard` are mutually-exclusive and exhaustive on it.  The cup threshold is `bottomCount ≤ partner` (opposite
side from the cap's `partner < bottomCount`); the fixed-point-freeness at the offset port splits the two cup cases.
The ∗-dual of `partitionThree_of_involution`. -/
theorem partitionThree_of_involution_top (bottomCount topCount total : Nat) (partner : List Nat)
    (topLe : bottomCount + topCount ≤ total) (wf : IsBoundaryInvolution total partner)
    (topIndex : Nat) (below : topIndex < topCount) :
    onlyOneTrueThree (cupSmallerGuard bottomCount partner topIndex)
      (cupLargerGuard bottomCount partner topIndex)
      (throughTopGuard bottomCount partner topIndex) := by
  have portLtSum : bottomCount + topIndex < bottomCount + topCount := Nat.add_lt_add_left below bottomCount
  have portLtTotal : bottomCount + topIndex < total := Nat.lt_of_lt_of_le portLtSum topLe
  cases Nat.lt_or_ge (natListGetAt partner (bottomCount + topIndex)) bottomCount with
  | inl ltBottom =>
      exact Or.inr (Or.inr
        ⟨andEqFalseLeftCount _ _
           (natBleFalseOfGtCount bottomCount (natListGetAt partner (bottomCount + topIndex)) ltBottom),
         andEqFalseLeftCount _ _
           (natBleFalseOfGtCount bottomCount (natListGetAt partner (bottomCount + topIndex)) ltBottom),
         natBltOfLtCount (natListGetAt partner (bottomCount + topIndex)) bottomCount ltBottom⟩)
  | inr geBottom =>
      have throughFalse : throughTopGuard bottomCount partner topIndex = false :=
        natBltFalseOfLeCount (natListGetAt partner (bottomCount + topIndex)) bottomCount geBottom
      have partnerNePort : natListGetAt partner (bottomCount + topIndex) ≠ bottomCount + topIndex :=
        wf.isFixedPointFree (bottomCount + topIndex) portLtTotal
      cases Nat.lt_or_ge (bottomCount + topIndex) (natListGetAt partner (bottomCount + topIndex)) with
      | inl portLtPartner =>
          exact Or.inl
            ⟨andEqTrueCount _ _
               (natBleOfLeCount bottomCount (natListGetAt partner (bottomCount + topIndex)) geBottom)
               (natBltOfLtCount (bottomCount + topIndex) (natListGetAt partner (bottomCount + topIndex)) portLtPartner),
             andEqFalseRightCount _ _
               (natBltFalseOfLeCount (natListGetAt partner (bottomCount + topIndex)) (bottomCount + topIndex)
                 (Nat.le_of_lt portLtPartner)),
             throughFalse⟩
      | inr partnerLePort =>
          have partnerLtPort : natListGetAt partner (bottomCount + topIndex) < bottomCount + topIndex :=
            natLtOfLeOfNeCount (natListGetAt partner (bottomCount + topIndex)) (bottomCount + topIndex)
              partnerLePort partnerNePort
          exact Or.inr (Or.inl
            ⟨andEqFalseRightCount _ _
               (natBltFalseOfLeCount (bottomCount + topIndex) (natListGetAt partner (bottomCount + topIndex))
                 (Nat.le_of_lt partnerLtPort)),
             andEqTrueCount _ _
               (natBleOfLeCount bottomCount (natListGetAt partner (bottomCount + topIndex)) geBottom)
               (natBltOfLtCount (natListGetAt partner (bottomCount + topIndex)) (bottomCount + topIndex) partnerLtPort),
             throughFalse⟩)

/-! ## Section 17 — truth-probes: the ∗-dual crux `2·|cupArcTopIndices| + |throughStrandTops| = topCount`

Confirm the top counting CONCLUSION on the recon's hand-worked top-side cases before proving the general identity. -/

/-- ★ **Truth-probe (adversarial-B, top).**  Partner `[2, 4, 0, 5, 1, 3]`, `topCount = 3`: one cup arc, one through —
`1 + 1 + 1 = 3`. -/
theorem cupCruxCount_probe_adversarialB :
    (cupArcTopIndices 3 3 [2, 4, 0, 5, 1, 3]).length + (cupArcTopIndices 3 3 [2, 4, 0, 5, 1, 3]).length
      + (throughStrandTops 3 3 [2, 4, 0, 5, 1, 3]).length = 3 := by decide

/-- ★ **Truth-probe (fresh mixed, top).**  Partner `[3, 4, 5, 0, 1, 2, 7, 6]`, `topCount = 4`: one cup arc, two
throughs — `1 + 1 + 2 = 4`. -/
theorem cupCruxCount_probe_freshMixed :
    (cupArcTopIndices 4 4 [3, 4, 5, 0, 1, 2, 7, 6]).length + (cupArcTopIndices 4 4 [3, 4, 5, 0, 1, 2, 7, 6]).length
      + (throughStrandTops 4 4 [3, 4, 5, 0, 1, 2, 7, 6]).length = 4 := by decide

/-- ★ **Truth-probe (wild-A, nested bottom caps).**  Partner `[3, 2, 1, 0, 6, 7, 4, 5]`, `bottomCount = 6`,
`topCount = 2`: the top side is all-through — `0 + 0 + 2 = 2`. -/
theorem cupCruxCount_probe_nestedCaps :
    (cupArcTopIndices 6 2 [3, 2, 1, 0, 6, 7, 4, 5]).length + (cupArcTopIndices 6 2 [3, 2, 1, 0, 6, 7, 4, 5]).length
      + (throughStrandTops 6 2 [3, 2, 1, 0, 6, 7, 4, 5]).length = 2 := by decide

/-- ★ **Truth-probe (three crossing cups).**  Partner `[3, 4, 5, 0, 1, 2]`, `bottomCount = 0`, `topCount = 6`: three
cup arcs, no through — `3 + 3 + 0 = 6` — the full cup machinery on a maximally-crossed top. -/
theorem cupCruxCount_probe_threeCups :
    (cupArcTopIndices 0 6 [3, 4, 5, 0, 1, 2]).length + (cupArcTopIndices 0 6 [3, 4, 5, 0, 1, 2]).length
      + (throughStrandTops 0 6 [3, 4, 5, 0, 1, 2]).length = 6 := by decide

/-! ## Section 18 — the three TOP read-off lengths as partition counts -/

/-- The smaller cup-top count equals the `cupSmallerGuard` `countTrue` over `List.range topCount`. -/
theorem cupArcTopIndices_length_eq_count (bottomCount topCount : Nat) (partner : List Nat) :
    (cupArcTopIndices bottomCount topCount partner).length
      = countTrue (cupSmallerGuard bottomCount partner) (List.range topCount) :=
  filterMapLength_eq_countTrue
    (fun topIndex => match cupSmallerGuard bottomCount partner topIndex with | true => some topIndex | false => none)
    (cupSmallerGuard bottomCount partner)
    (fun value => (guardIsSomeAgreeCount (cupSmallerGuard bottomCount partner value) value).symm)
    (List.range topCount)

/-- The through-top count equals the `throughTopGuard` `countTrue` over `List.range topCount`. -/
theorem throughStrandTops_length_eq_count (bottomCount topCount : Nat) (partner : List Nat) :
    (throughStrandTops bottomCount topCount partner).length
      = countTrue (throughTopGuard bottomCount partner) (List.range topCount) :=
  filterMapLength_eq_countTrue
    (fun topIndex => match throughTopGuard bottomCount partner topIndex with | true => some topIndex | false => none)
    (throughTopGuard bottomCount partner)
    (fun value => (guardIsSomeAgreeCount (throughTopGuard bottomCount partner value) value).symm)
    (List.range topCount)

/-- ★ **The larger cup-top indices** — top ports whose partner is a top port strictly smaller (the ∗-mirror of
`cupArcTopIndices`, listing the LARGER top foot of each cup arc). -/
def cupLargerTopIndices (bottomCount topCount : Nat) (partner : List Nat) : List Nat :=
  (List.range topCount).filterMap (fun topIndex =>
    match cupLargerGuard bottomCount partner topIndex with | true => some topIndex | false => none)

/-- The larger cup-top count equals the `cupLargerGuard` `countTrue` over `List.range topCount`. -/
theorem cupLargerTopIndices_length_eq_count (bottomCount topCount : Nat) (partner : List Nat) :
    (cupLargerTopIndices bottomCount topCount partner).length
      = countTrue (cupLargerGuard bottomCount partner) (List.range topCount) :=
  filterMapLength_eq_countTrue
    (fun topIndex => match cupLargerGuard bottomCount partner topIndex with | true => some topIndex | false => none)
    (cupLargerGuard bottomCount partner)
    (fun value => (guardIsSomeAgreeCount (cupLargerGuard bottomCount partner value) value).symm)
    (List.range topCount)

/-! ## Section 19 — the ∗-dual pairing bijection: `|larger cup tops| = |smaller cup tops|` (the crux-of-crux)

The involution maps the smaller top foot of each cup arc to its larger top foot bijectively, via the shift map
`partnerTopShift` (`partner (bottomCount + topIndex) − bottomCount`).  Realized over the erase-kit length equality
(`distinctSameMembersLengthEq`) by exhibiting `cupLargerTopIndices` and `cupArcTopIndices.map partnerTopShift` as two
distinct lists with the same members. -/

/-- The shift map: the top-index of the partner top of a cup top foot (`partner (bottomCount + topIndex) −
bottomCount`).  Definitionally the second entry `expandCupTopPairs` emits per arc. -/
def partnerTopShift (bottomCount : Nat) (partner : List Nat) (topIndex : Nat) : Nat :=
  natListGetAt partner (bottomCount + topIndex) - bottomCount

/-- ★★ **The ∗-dual pairing bijection (crux-of-crux).**  Under the involution gate over `bottomCount + topCount`
ports, the number of LARGER cup tops equals the number of SMALLER cup tops: `partnerTopShift` bijects
`cupArcTopIndices` onto `cupLargerTopIndices`.  Realized via the erase-kit length equality on `cupLargerTopIndices`
and `cupArcTopIndices.map partnerTopShift` (two distinct lists with the same members).  The heart of the ∗-dual
width-length identity — `|larger| = |smaller|`. -/
theorem cupLargerTopIndices_length_eq (bottomCount topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (bottomCount + topCount) partner) :
    (cupLargerTopIndices bottomCount topCount partner).length
      = (cupArcTopIndices bottomCount topCount partner).length := by
  have sameMembers : ∀ value, memBool value (cupLargerTopIndices bottomCount topCount partner)
      = memBool value ((cupArcTopIndices bottomCount topCount partner).map (partnerTopShift bottomCount partner)) := by
    intro value
    apply boolEqOfImpCount
    · intro valueMemLarger
      have valueMem : value ∈ cupLargerTopIndices bottomCount topCount partner := memBoolMemCount _ value valueMemLarger
      obtain ⟨valueRange, valueLargerGuard⟩ :=
        memFilterMapGuardInvertedCount (cupLargerGuard bottomCount partner) (List.range topCount) value valueMem
      have valueLt : value < topCount := memRangeLtCount valueRange
      have portValueLtSum : bottomCount + value < bottomCount + topCount := Nat.add_lt_add_left valueLt bottomCount
      have bottomLeAtValue : bottomCount ≤ natListGetAt partner (bottomCount + value) :=
        natLeOfBleCount bottomCount (natListGetAt partner (bottomCount + value)) (boolAndLeftCount _ _ valueLargerGuard)
      have partnerAtValueLtPort : natListGetAt partner (bottomCount + value) < bottomCount + value :=
        natLtOfBltCount (natListGetAt partner (bottomCount + value)) (bottomCount + value)
          (boolAndRightCount _ _ valueLargerGuard)
      have selfInvValue : natListGetAt partner (natListGetAt partner (bottomCount + value)) = bottomCount + value :=
        wf.isSelfInverse (bottomCount + value) portValueLtSum
      have bottomAddSmall : bottomCount + (natListGetAt partner (bottomCount + value) - bottomCount)
          = natListGetAt partner (bottomCount + value) :=
        addSubCancelTop bottomCount (natListGetAt partner (bottomCount + value)) bottomLeAtValue
      have smallLtTop : natListGetAt partner (bottomCount + value) - bottomCount < topCount := by
        have step : bottomCount + (natListGetAt partner (bottomCount + value) - bottomCount) < bottomCount + topCount := by
          rw [bottomAddSmall]; exact Nat.lt_trans partnerAtValueLtPort portValueLtSum
        exact natLtOfAddLtAddLeftTop bottomCount _ topCount step
      have smallGuard : cupSmallerGuard bottomCount partner (natListGetAt partner (bottomCount + value) - bottomCount)
          = true := by
        show (Nat.ble bottomCount
            (natListGetAt partner (bottomCount + (natListGetAt partner (bottomCount + value) - bottomCount)))
          && Nat.blt (bottomCount + (natListGetAt partner (bottomCount + value) - bottomCount))
            (natListGetAt partner (bottomCount + (natListGetAt partner (bottomCount + value) - bottomCount)))) = true
        rw [bottomAddSmall, selfInvValue]
        exact andEqTrueCount _ _
          (natBleOfLeCount bottomCount (bottomCount + value) (Nat.le_add_right bottomCount value))
          (natBltOfLtCount (natListGetAt partner (bottomCount + value)) (bottomCount + value) partnerAtValueLtPort)
      have smallRange : natListGetAt partner (bottomCount + value) - bottomCount ∈ List.range topCount :=
        memRangeOfLtCount (natListGetAt partner (bottomCount + value) - bottomCount) topCount smallLtTop
      have smallMemCup : natListGetAt partner (bottomCount + value) - bottomCount
          ∈ cupArcTopIndices bottomCount topCount partner :=
        memFilterMapGuardComplete (cupSmallerGuard bottomCount partner) (List.range topCount)
          (natListGetAt partner (bottomCount + value) - bottomCount) smallRange smallGuard
      have shiftEq : partnerTopShift bottomCount partner
          (natListGetAt partner (bottomCount + value) - bottomCount) = value := by
        show natListGetAt partner (bottomCount + (natListGetAt partner (bottomCount + value) - bottomCount)) - bottomCount
          = value
        rw [bottomAddSmall, selfInvValue]
        exact natAddSubCancelLeftTop bottomCount value
      have mapMem : memBool (partnerTopShift bottomCount partner
          (natListGetAt partner (bottomCount + value) - bottomCount))
          ((cupArcTopIndices bottomCount topCount partner).map (partnerTopShift bottomCount partner)) = true :=
        memBoolMapOfMemCount (partnerTopShift bottomCount partner) (cupArcTopIndices bottomCount topCount partner)
          (natListGetAt partner (bottomCount + value) - bottomCount) smallMemCup
      rw [shiftEq] at mapMem
      exact mapMem
    · intro valueMemMap
      obtain ⟨smallerTop, smallerTopMemCup, smallerTopShiftEq⟩ :=
        memBoolMapWitnessCount (partnerTopShift bottomCount partner)
          (cupArcTopIndices bottomCount topCount partner) value valueMemMap
      have smallerSound := cupArcTopIndices_mem_sound bottomCount topCount partner smallerTop smallerTopMemCup
      have subExact : bottomCount + (natListGetAt partner (bottomCount + smallerTop) - bottomCount)
          = natListGetAt partner (bottomCount + smallerTop) :=
        cupArcTop_sub_exact bottomCount topCount partner smallerTop smallerTopMemCup
      have valueEq : natListGetAt partner (bottomCount + smallerTop) - bottomCount = value := smallerTopShiftEq
      have partnerAtEq : natListGetAt partner (bottomCount + smallerTop) = bottomCount + value := by
        rw [← subExact, valueEq]
      have portSmallerLtSum : bottomCount + smallerTop < bottomCount + topCount :=
        Nat.add_lt_add_left smallerSound.1 bottomCount
      have valueLt : value < topCount := by
        have partnerAtLt : natListGetAt partner (bottomCount + smallerTop) < bottomCount + topCount :=
          wf.mapsInRange (bottomCount + smallerTop) portSmallerLtSum
        rw [partnerAtEq] at partnerAtLt
        exact natLtOfAddLtAddLeftTop bottomCount value topCount partnerAtLt
      have valueRange : value ∈ List.range topCount := memRangeOfLtCount value topCount valueLt
      have selfInvSmaller :
          natListGetAt partner (natListGetAt partner (bottomCount + smallerTop)) = bottomCount + smallerTop :=
        wf.isSelfInverse (bottomCount + smallerTop) portSmallerLtSum
      rw [partnerAtEq] at selfInvSmaller
      have largerGuardValue : cupLargerGuard bottomCount partner value = true := by
        show (Nat.ble bottomCount (natListGetAt partner (bottomCount + value))
          && Nat.blt (natListGetAt partner (bottomCount + value)) (bottomCount + value)) = true
        rw [selfInvSmaller]
        exact andEqTrueCount _ _
          (natBleOfLeCount bottomCount (bottomCount + smallerTop) (Nat.le_add_right bottomCount smallerTop))
          (natBltOfLtCount (bottomCount + smallerTop) (bottomCount + value) (partnerAtEq ▸ smallerSound.2.2))
      have valueMemLarger : value ∈ cupLargerTopIndices bottomCount topCount partner :=
        memFilterMapGuardComplete (cupLargerGuard bottomCount partner) (List.range topCount)
          value valueRange largerGuardValue
      exact memBoolOfMemCount _ value valueMemLarger
  have distinctLarger : isDistinctList (cupLargerTopIndices bottomCount topCount partner) = true :=
    filterMapGuardIdentityDistinctCount (cupLargerGuard bottomCount partner) (List.range topCount)
      (isDistinctListRangeCount topCount)
  have distinctMap :
      isDistinctList ((cupArcTopIndices bottomCount topCount partner).map (partnerTopShift bottomCount partner)) = true :=
    mapDistinctOfInjOnCount (partnerTopShift bottomCount partner) (cupArcTopIndices bottomCount topCount partner)
      (filterMapGuardIdentityDistinctCount (cupSmallerGuard bottomCount partner) (List.range topCount)
        (isDistinctListRangeCount topCount))
      (fun left right leftMem rightMem eqShift => by
        have leftSound := cupArcTopIndices_mem_sound bottomCount topCount partner left leftMem
        have rightSound := cupArcTopIndices_mem_sound bottomCount topCount partner right rightMem
        have leftSub : bottomCount + (natListGetAt partner (bottomCount + left) - bottomCount)
            = natListGetAt partner (bottomCount + left) :=
          cupArcTop_sub_exact bottomCount topCount partner left leftMem
        have rightSub : bottomCount + (natListGetAt partner (bottomCount + right) - bottomCount)
            = natListGetAt partner (bottomCount + right) :=
          cupArcTop_sub_exact bottomCount topCount partner right rightMem
        have portsEq : natListGetAt partner (bottomCount + left) = natListGetAt partner (bottomCount + right) := by
          rw [← leftSub, ← rightSub]
          exact congrArg (bottomCount + ·) eqShift
        have portIndexEq : bottomCount + left = bottomCount + right :=
          involutionInjectiveCount (bottomCount + topCount) partner wf (bottomCount + left) (bottomCount + right)
            (Nat.add_lt_add_left leftSound.1 bottomCount) (Nat.add_lt_add_left rightSound.1 bottomCount) portsEq
        exact natAddLeftCancelTop bottomCount left right portIndexEq)
  have lengthEq : (cupLargerTopIndices bottomCount topCount partner).length
      = ((cupArcTopIndices bottomCount topCount partner).map (partnerTopShift bottomCount partner)).length :=
    distinctSameMembersLengthEq (cupLargerTopIndices bottomCount topCount partner)
      ((cupArcTopIndices bottomCount topCount partner).map (partnerTopShift bottomCount partner))
      distinctLarger distinctMap sameMembers
  rw [lengthEq, mapLengthCount]

/-! ## Section 20 — the ∗-dual crux and doubling -/

/-- ★★ **The ∗-dual doubling — `|cupArcTops| = 2·|cupArcTopIndices|`.**  Each cup arc contributes two top feet. -/
theorem expandCupTopPairs_length (bottomCount : Nat) (partner : List Nat) : (feet : List Nat) →
    (expandCupTopPairs bottomCount partner feet).length = feet.length + feet.length
  | [] => rfl
  | topIndex :: rest => by
      show (expandCupTopPairs bottomCount partner rest).length + 1 + 1 = (rest.length + 1) + (rest.length + 1)
      rw [expandCupTopPairs_length bottomCount partner rest]
      exact twoSuccArithCount rest.length

/-- ★★ **The ∗-dual crux — `2·|cupArcTopIndices| + |throughStrandTops| = topCount`.**  Assembles the ∗-dual pairing
bijection (`|larger| = |smaller|`) with the three-way partition count over `List.range topCount`: the smaller cup
tops, the larger cup tops, and the through tops exhaust the top boundary, and the two cup classes have equal
cardinality. -/
theorem cupArcTwiceThroughSumsToTop (bottomCount topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (bottomCount + topCount) partner) :
    (cupArcTopIndices bottomCount topCount partner).length + (cupArcTopIndices bottomCount topCount partner).length
      + (throughStrandTops bottomCount topCount partner).length = topCount := by
  have pairing : countTrue (cupLargerGuard bottomCount partner) (List.range topCount)
      = countTrue (cupSmallerGuard bottomCount partner) (List.range topCount) := by
    rw [← cupLargerTopIndices_length_eq_count, ← cupArcTopIndices_length_eq_count]
    exact cupLargerTopIndices_length_eq bottomCount topCount partner wf
  have partition : countTrue (cupSmallerGuard bottomCount partner) (List.range topCount)
      + countTrue (cupLargerGuard bottomCount partner) (List.range topCount)
      + countTrue (throughTopGuard bottomCount partner) (List.range topCount)
      = topCount :=
    (partitionCountThree (cupSmallerGuard bottomCount partner) (cupLargerGuard bottomCount partner)
      (throughTopGuard bottomCount partner) (List.range topCount)
      (fun value valueMem => partitionThree_of_involution_top bottomCount topCount (bottomCount + topCount) partner
        (Nat.le_refl _) wf value (memRangeLtCount valueMem))).trans (lengthRangeCount topCount)
  rw [cupArcTopIndices_length_eq_count, throughStrandTops_length_eq_count]
  exact pairing ▸ partition

/-! ## Section 21 — the TOP read-off width-length identity (`hasWidthLength`) -/

/-- ★★★ **The top read-off width-length identity (`hasWidthLength`).**  For every well-formed involution partner over
`bottomCount + topCount` ports, `(throughStrandTops ++ cupArcTops).length = topCount` — the ∗-dual counting field the
general `IsPermutationOfRange` was missing on the top side.  From the through count, the ∗-dual doubling
(`expandCupTopPairs_length`), the append length, and the ∗-dual crux. -/
theorem topReadOffOrderLength (bottomCount topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (bottomCount + topCount) partner) :
    (throughStrandTops bottomCount topCount partner ++ cupArcTops bottomCount topCount partner).length = topCount := by
  rw [appendLengthCount]
  show (throughStrandTops bottomCount topCount partner).length
    + (expandCupTopPairs bottomCount partner (cupArcTopIndices bottomCount topCount partner)).length = topCount
  rw [expandCupTopPairs_length bottomCount partner (cupArcTopIndices bottomCount topCount partner),
    Nat.add_comm (throughStrandTops bottomCount topCount partner).length
      ((cupArcTopIndices bottomCount topCount partner).length
        + (cupArcTopIndices bottomCount topCount partner).length)]
  exact cupArcTwiceThroughSumsToTop bottomCount topCount partner wf

/-! ## Section 22 — the TOP read-off boundedness (`isBounded`) -/

private theorem mem_expandCupTopPairsCount (bottomCount : Nat) (partner : List Nat) : (feet : List Nat) → (value : Nat) →
    value ∈ expandCupTopPairs bottomCount partner feet →
    ∃ topIdx, topIdx ∈ feet ∧ (value = topIdx ∨ value = natListGetAt partner (bottomCount + topIdx) - bottomCount)
  | [], _, memNil => nomatch memNil
  | topIndex :: rest, value, mem => by
      have memReduced : value ∈ topIndex :: (natListGetAt partner (bottomCount + topIndex) - bottomCount)
          :: expandCupTopPairs bottomCount partner rest := mem
      cases memReduced with
      | head => exact ⟨topIndex, List.Mem.head rest, Or.inl rfl⟩
      | tail _ memTail =>
          cases memTail with
          | head => exact ⟨topIndex, List.Mem.head rest, Or.inr rfl⟩
          | tail _ memRest =>
              obtain ⟨topIdx, topIdxMem, topIdxEq⟩ := mem_expandCupTopPairsCount bottomCount partner rest value memRest
              exact ⟨topIdx, List.Mem.tail topIndex topIdxMem, topIdxEq⟩

/-- Every member of the top read-off order is a top port (0-based, `< topCount`) — through tops by through soundness,
cup top legs by cup soundness (smaller foot and its partner top).  Uses the involution gate for the larger-leg bound. -/
theorem memberBoundedTopReadOff (bottomCount topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (bottomCount + topCount) partner) (value : Nat)
    (mem : value ∈ throughStrandTops bottomCount topCount partner ++ cupArcTops bottomCount topCount partner) :
    value < topCount := by
  cases memAppendCount value (throughStrandTops bottomCount topCount partner)
      (cupArcTops bottomCount topCount partner) mem with
  | inl memThrough =>
      exact (throughStrandTops_mem_sound bottomCount topCount partner value memThrough).1
  | inr memCup =>
      obtain ⟨topIdx, topIdxMem, topIdxEq⟩ :=
        mem_expandCupTopPairsCount bottomCount partner (cupArcTopIndices bottomCount topCount partner) value memCup
      have topSound := cupArcTopIndices_mem_sound bottomCount topCount partner topIdx topIdxMem
      cases topIdxEq with
      | inl valueEq => rw [valueEq]; exact topSound.1
      | inr valueEqShift =>
          rw [valueEqShift]
          have subExact : bottomCount + (natListGetAt partner (bottomCount + topIdx) - bottomCount)
              = natListGetAt partner (bottomCount + topIdx) :=
            cupArcTop_sub_exact bottomCount topCount partner topIdx topIdxMem
          have portLt : bottomCount + topIdx < bottomCount + topCount := Nat.add_lt_add_left topSound.1 bottomCount
          have partnerLt : natListGetAt partner (bottomCount + topIdx) < bottomCount + topCount :=
            wf.mapsInRange (bottomCount + topIdx) portLt
          have step : bottomCount + (natListGetAt partner (bottomCount + topIdx) - bottomCount)
              < bottomCount + topCount := by rw [subExact]; exact partnerLt
          exact natLtOfAddLtAddLeftTop bottomCount _ topCount step

/-- ★ **The top read-off boundedness (`isBounded`).**  At every in-range position the top read-off order reads a
0-based top port.  From the width-length identity (so the index is in range) and member-boundedness. -/
theorem topReadOffOrderBounded (bottomCount topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (bottomCount + topCount) partner) (index : Nat) (indexBelow : index < topCount) :
    natListGetAt (throughStrandTops bottomCount topCount partner ++ cupArcTops bottomCount topCount partner) index
      < topCount := by
  have indexInRange : index
      < (throughStrandTops bottomCount topCount partner ++ cupArcTops bottomCount topCount partner).length := by
    rw [topReadOffOrderLength bottomCount topCount partner wf]; exact indexBelow
  exact memberBoundedTopReadOff bottomCount topCount partner wf _
    (getAtMemCount (throughStrandTops bottomCount topCount partner ++ cupArcTops bottomCount topCount partner)
      index indexInRange)

/-! ## Section 23 — the TOP read-off distinctness (`isDistinct`): interleaved cup tops, distinct throughs, disjoint -/

/-- ★★ **The cup-top interleave is distinct.**  `expandCupTopPairs partner feet = [t0, partnerTopShift t0, t1, …]` is
distinct when `feet` is a distinct list of smaller cup tops: the top indices are distinct (input distinct), their
partner tops are distinct (involution injective at the offset ports), and no top equals a partner top (a smaller top
cannot be a larger top).  The ∗-dual of `expandBottomFeetPairsDistinctCount`. -/
private theorem expandCupTopPairsDistinctCount (bottomCount topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (bottomCount + topCount) partner) : (feet : List Nat) →
    isDistinctList feet = true →
    (∀ topIdx, topIdx ∈ feet → topIdx < topCount ∧ bottomCount ≤ natListGetAt partner (bottomCount + topIdx)
      ∧ bottomCount + topIdx < natListGetAt partner (bottomCount + topIdx)) →
    isDistinctList (expandCupTopPairs bottomCount partner feet) = true
  | [], _, _ => rfl
  | index :: rest, feetDistinct, feetSmaller => by
      have splitDist : isDistinctList (index :: rest) = (not (memBool index rest) && isDistinctList rest) := rfl
      rw [splitDist] at feetDistinct
      have indexNotRest : memBool index rest = false :=
        eqFalseOfNotTrueCount _ (boolAndLeftCount _ _ feetDistinct)
      have distRest : isDistinctList rest = true := boolAndRightCount _ _ feetDistinct
      have indexSmaller := feetSmaller index (List.Mem.head rest)
      have restSmaller : ∀ topIdx, topIdx ∈ rest → topIdx < topCount
          ∧ bottomCount ≤ natListGetAt partner (bottomCount + topIdx)
          ∧ bottomCount + topIdx < natListGetAt partner (bottomCount + topIdx) :=
        fun topIdx topIdxMem => feetSmaller topIdx (List.Mem.tail index topIdxMem)
      have distTail : isDistinctList (expandCupTopPairs bottomCount partner rest) = true :=
        expandCupTopPairsDistinctCount bottomCount topCount partner wf rest distRest restSmaller
      have portIndexLt : bottomCount + index < bottomCount + topCount := Nat.add_lt_add_left indexSmaller.1 bottomCount
      have bottomAddShiftIndex : bottomCount + (natListGetAt partner (bottomCount + index) - bottomCount)
          = natListGetAt partner (bottomCount + index) :=
        addSubCancelTop bottomCount (natListGetAt partner (bottomCount + index)) indexSmaller.2.1
      have selfInvIndex :
          natListGetAt partner (natListGetAt partner (bottomCount + index)) = bottomCount + index :=
        wf.isSelfInverse (bottomCount + index) portIndexLt
      have shiftIndexNotTail :
          memBool (natListGetAt partner (bottomCount + index) - bottomCount)
            (expandCupTopPairs bottomCount partner rest) = false := by
        cases hmem : memBool (natListGetAt partner (bottomCount + index) - bottomCount)
            (expandCupTopPairs bottomCount partner rest) with
        | false => rfl
        | true =>
            obtain ⟨collision, collisionMem, collisionEq⟩ := mem_expandCupTopPairsCount bottomCount partner rest
              (natListGetAt partner (bottomCount + index) - bottomCount) (memBoolMemCount _ _ hmem)
            have collisionSmaller := restSmaller collision collisionMem
            have portCollisionLt : bottomCount + collision < bottomCount + topCount :=
              Nat.add_lt_add_left collisionSmaller.1 bottomCount
            cases collisionEq with
            | inl shiftEqCollision =>
                have portCollisionEq : bottomCount + collision = natListGetAt partner (bottomCount + index) :=
                  (congrArg (bottomCount + ·) shiftEqCollision.symm).trans bottomAddShiftIndex
                have partnerCollisionEqIndexPort :
                    natListGetAt partner (bottomCount + collision) = bottomCount + index :=
                  (congrArg (natListGetAt partner) portCollisionEq).trans selfInvIndex
                have indexLtCollision : index < collision := by
                  have step : bottomCount + index < bottomCount + collision := by
                    rw [portCollisionEq]; exact indexSmaller.2.2
                  exact natLtOfAddLtAddLeftTop bottomCount index collision step
                have collisionLtIndex : collision < index := by
                  have step : bottomCount + collision < bottomCount + index := by
                    have raw := collisionSmaller.2.2
                    rw [partnerCollisionEqIndexPort] at raw
                    exact raw
                  exact natLtOfAddLtAddLeftTop bottomCount collision index step
                exact absurd (Nat.lt_trans indexLtCollision collisionLtIndex) (Nat.lt_irrefl index)
            | inr shiftEqPartnerCollision =>
                have collisionSub : bottomCount + (natListGetAt partner (bottomCount + collision) - bottomCount)
                    = natListGetAt partner (bottomCount + collision) :=
                  addSubCancelTop bottomCount (natListGetAt partner (bottomCount + collision)) collisionSmaller.2.1
                have portsEq :
                    natListGetAt partner (bottomCount + index) = natListGetAt partner (bottomCount + collision) :=
                  (bottomAddShiftIndex.symm.trans (congrArg (bottomCount + ·) shiftEqPartnerCollision)).trans collisionSub
                have portIndexEqCollision : bottomCount + index = bottomCount + collision :=
                  involutionInjectiveCount (bottomCount + topCount) partner wf (bottomCount + index)
                    (bottomCount + collision) portIndexLt portCollisionLt portsEq
                have indexMemRest : memBool index rest = true := by
                  rw [natAddLeftCancelTop bottomCount index collision portIndexEqCollision]
                  exact memBoolOfMemCount rest collision collisionMem
                rw [indexNotRest] at indexMemRest; exact Bool.noConfusion indexMemRest
      have indexNotConsTail :
          memBool index ((natListGetAt partner (bottomCount + index) - bottomCount)
            :: expandCupTopPairs bottomCount partner rest) = false := by
        show (Nat.beq (natListGetAt partner (bottomCount + index) - bottomCount) index
          || memBool index (expandCupTopPairs bottomCount partner rest)) = false
        have shiftIndexNeIndex : Nat.beq (natListGetAt partner (bottomCount + index) - bottomCount) index = false :=
          natBeqFalseOfNeCount (natListGetAt partner (bottomCount + index) - bottomCount) index (by
            intro equal
            have step : bottomCount + index
                < bottomCount + (natListGetAt partner (bottomCount + index) - bottomCount) := by
              rw [bottomAddShiftIndex]; exact indexSmaller.2.2
            have indexLtShift : index < natListGetAt partner (bottomCount + index) - bottomCount :=
              natLtOfAddLtAddLeftTop bottomCount index _ step
            rw [equal] at indexLtShift
            exact Nat.lt_irrefl index indexLtShift)
        rw [shiftIndexNeIndex, Bool.false_or]
        cases hmem : memBool index (expandCupTopPairs bottomCount partner rest) with
        | false => rfl
        | true =>
            obtain ⟨collision, collisionMem, collisionEq⟩ := mem_expandCupTopPairsCount bottomCount partner rest index
              (memBoolMemCount _ _ hmem)
            have collisionSmaller := restSmaller collision collisionMem
            have portCollisionLt : bottomCount + collision < bottomCount + topCount :=
              Nat.add_lt_add_left collisionSmaller.1 bottomCount
            cases collisionEq with
            | inl indexEqCollision =>
                have indexMemRest : memBool index rest = true := by
                  rw [indexEqCollision]; exact memBoolOfMemCount rest collision collisionMem
                rw [indexNotRest] at indexMemRest; exact Bool.noConfusion indexMemRest
            | inr indexEqPartnerCollision =>
                have collisionSub : bottomCount + (natListGetAt partner (bottomCount + collision) - bottomCount)
                    = natListGetAt partner (bottomCount + collision) :=
                  addSubCancelTop bottomCount (natListGetAt partner (bottomCount + collision)) collisionSmaller.2.1
                have portCollisionPartnerEq : natListGetAt partner (bottomCount + collision) = bottomCount + index :=
                  collisionSub.symm.trans (congrArg (bottomCount + ·) indexEqPartnerCollision.symm)
                have collisionLtIndex : collision < index := by
                  have step : bottomCount + collision < bottomCount + index := by
                    rw [← portCollisionPartnerEq]; exact collisionSmaller.2.2
                  exact natLtOfAddLtAddLeftTop bottomCount collision index step
                have partnerIndexPortEq : natListGetAt partner (bottomCount + index) = bottomCount + collision :=
                  (congrArg (natListGetAt partner) portCollisionPartnerEq).symm.trans
                    (wf.isSelfInverse (bottomCount + collision) portCollisionLt)
                have indexLtCollision : index < collision := by
                  have step : bottomCount + index < bottomCount + collision := by
                    rw [← partnerIndexPortEq]; exact indexSmaller.2.2
                  exact natLtOfAddLtAddLeftTop bottomCount index collision step
                exact absurd (Nat.lt_trans collisionLtIndex indexLtCollision) (Nat.lt_irrefl collision)
      have distConsTail :
          isDistinctList ((natListGetAt partner (bottomCount + index) - bottomCount)
            :: expandCupTopPairs bottomCount partner rest) = true := by
        show (not (memBool (natListGetAt partner (bottomCount + index) - bottomCount)
            (expandCupTopPairs bottomCount partner rest))
          && isDistinctList (expandCupTopPairs bottomCount partner rest)) = true
        rw [shiftIndexNotTail]
        show isDistinctList (expandCupTopPairs bottomCount partner rest) = true
        exact distTail
      show (not (memBool index ((natListGetAt partner (bottomCount + index) - bottomCount)
          :: expandCupTopPairs bottomCount partner rest))
        && isDistinctList ((natListGetAt partner (bottomCount + index) - bottomCount)
          :: expandCupTopPairs bottomCount partner rest)) = true
      rw [indexNotConsTail]
      show isDistinctList ((natListGetAt partner (bottomCount + index) - bottomCount)
        :: expandCupTopPairs bottomCount partner rest) = true
      exact distConsTail

/-- ★★ **The cup-top order is distinct.** -/
theorem cupArcTops_distinct (bottomCount topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (bottomCount + topCount) partner) :
    isDistinctList (cupArcTops bottomCount topCount partner) = true :=
  expandCupTopPairsDistinctCount bottomCount topCount partner wf (cupArcTopIndices bottomCount topCount partner)
    (filterMapGuardIdentityDistinctCount (cupSmallerGuard bottomCount partner) (List.range topCount)
      (isDistinctListRangeCount topCount))
    (fun topIdx topIdxMem => cupArcTopIndices_mem_sound bottomCount topCount partner topIdx topIdxMem)

/-- The through-top order is distinct (filterMap-identity of the distinct range). -/
theorem throughStrandTops_distinct (bottomCount topCount : Nat) (partner : List Nat) :
    isDistinctList (throughStrandTops bottomCount topCount partner) = true :=
  filterMapGuardIdentityDistinctCount (throughTopGuard bottomCount partner) (List.range topCount)
    (isDistinctListRangeCount topCount)

/-- A cup top leg's partner is a TOP port (`bottomCount ≤ partner`).  The smaller foot by cup soundness; the larger
foot's partner is the smaller foot's port (involution), which is a top port. -/
private theorem cupTopLegPartnerGe (bottomCount topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (bottomCount + topCount) partner) (value : Nat)
    (mem : value ∈ cupArcTops bottomCount topCount partner) :
    bottomCount ≤ natListGetAt partner (bottomCount + value) := by
  obtain ⟨topIdx, topIdxMem, topIdxEq⟩ :=
    mem_expandCupTopPairsCount bottomCount partner (cupArcTopIndices bottomCount topCount partner) value mem
  have topSound := cupArcTopIndices_mem_sound bottomCount topCount partner topIdx topIdxMem
  cases topIdxEq with
  | inl valueEqTopIdx => rw [valueEqTopIdx]; exact topSound.2.1
  | inr valueEqShift =>
      have subExact : bottomCount + (natListGetAt partner (bottomCount + topIdx) - bottomCount)
          = natListGetAt partner (bottomCount + topIdx) :=
        cupArcTop_sub_exact bottomCount topCount partner topIdx topIdxMem
      have portTopIdxLt : bottomCount + topIdx < bottomCount + topCount := Nat.add_lt_add_left topSound.1 bottomCount
      have selfInv : natListGetAt partner (natListGetAt partner (bottomCount + topIdx)) = bottomCount + topIdx :=
        wf.isSelfInverse (bottomCount + topIdx) portTopIdxLt
      rw [valueEqShift, subExact, selfInv]
      exact Nat.le_add_right bottomCount topIdx

private theorem topReadOffDisjoint (bottomCount topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (bottomCount + topCount) partner) (value : Nat)
    (memThrough : memBool value (throughStrandTops bottomCount topCount partner) = true) :
    memBool value (cupArcTops bottomCount topCount partner) = false := by
  cases hmem : memBool value (cupArcTops bottomCount topCount partner) with
  | false => rfl
  | true =>
      have throughSound :=
        throughStrandTops_mem_sound bottomCount topCount partner value (memBoolMemCount _ value memThrough)
      have partnerGe : bottomCount ≤ natListGetAt partner (bottomCount + value) :=
        cupTopLegPartnerGe bottomCount topCount partner wf value (memBoolMemCount _ value hmem)
      exact absurd (Nat.lt_of_lt_of_le throughSound.2 partnerGe) (Nat.lt_irrefl _)

/-- ★★★ **The top read-off distinctness (`isDistinct`).**  `throughStrandTops ++ cupArcTops` is distinct: the through
tops are distinct, the cup-top interleave is distinct, and the two are disjoint (a cup top leg's partner is a top
port, so it is never a through top). -/
theorem topReadOffOrder_distinct (bottomCount topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (bottomCount + topCount) partner) :
    isDistinctList (throughStrandTops bottomCount topCount partner ++ cupArcTops bottomCount topCount partner) = true :=
  appendDistinctCount (throughStrandTops bottomCount topCount partner) (cupArcTops bottomCount topCount partner)
    (throughStrandTops_distinct bottomCount topCount partner)
    (cupArcTops_distinct bottomCount topCount partner wf)
    (topReadOffDisjoint bottomCount topCount partner wf)

/-! ## Section 24 — the general TOP read-off `IsPermutationOfRange` (T-CLOSE top side) + the `permInverse` lift -/

/-- ★★★ **The general top read-off order is a range-permutation.**  For every well-formed boundary involution over
`bottomCount + topCount` ports, `throughStrandTops ++ cupArcTops` satisfies `IsPermutationOfRange topCount` — distinct,
length `topCount`, `[0, topCount)`-bounded.  Promotes the r15 `by decide` top truth-probes
(`readOffTopOrder_isPermutationOfRange_adversarialB` / `_freshMixed`) to the general theorem: the ∗-dual counting
residual the r15/r16 honesty walls named is CLOSED on the top side. -/
theorem readOffTopOrder_isPermutationOfRange (bottomCount topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (bottomCount + topCount) partner) :
    IsPermutationOfRange topCount
      (throughStrandTops bottomCount topCount partner ++ cupArcTops bottomCount topCount partner) where
  hasWidthLength := topReadOffOrderLength bottomCount topCount partner wf
  isDistinct := topReadOffOrder_distinct bottomCount topCount partner wf
  isBounded := topReadOffOrderBounded bottomCount topCount partner wf

/-- ★★★ **The inverted top read-off order is a range-permutation.**  The corrected extractor feeds
`permInverse (throughStrandTops ++ cupArcTops)` into the top staircase (the r3 cup-side inversion pin); by r15's
`isPermutationOfRange_permInverse` the inverse is also a range-permutation. -/
theorem readOffTopOrderInverse_isPermutationOfRange (bottomCount topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (bottomCount + topCount) partner) :
    IsPermutationOfRange topCount
      (permInverse (throughStrandTops bottomCount topCount partner ++ cupArcTops bottomCount topCount partner)) :=
  isPermutationOfRange_permInverse topCount _ (readOffTopOrder_isPermutationOfRange bottomCount topCount partner wf)

/-- ★★★ **The general top read-off E2 roundtrip.**  The `permutationToCrossingWord` staircase realizes the top read-off
order `throughStrandTops ++ cupArcTops` for EVERY well-formed boundary involution — the shipped conjugator roundtrip
`permuteOfCrossingWord_permutationToCrossingWord` fed the general top range-permutation witness. -/
theorem readOffTopOrder_realizesRoundtrip (bottomCount topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (bottomCount + topCount) partner) :
    permuteOfCrossingWord topCount
        (permutationToCrossingWord topCount
          (throughStrandTops bottomCount topCount partner ++ cupArcTops bottomCount topCount partner))
      = throughStrandTops bottomCount topCount partner ++ cupArcTops bottomCount topCount partner :=
  permuteOfCrossingWord_permutationToCrossingWord topCount _
    (readOffTopOrder_isPermutationOfRange bottomCount topCount partner wf)

/-! ## Honesty markers + the r16 ledger -/

/-- ★★★ **Honesty marker — the BOTTOM read-off order is a range-permutation for EVERY well-formed involution (r16).**
`readOffBottomOrder_isPermutationOfRange` proves `capArcFeet ++ throughStrandBottoms` satisfies
`IsPermutationOfRange bottomCount` (distinct, length `bottomCount`, `[0, bottomCount)`-bounded) for every
`IsBoundaryInvolution (bottomCount + topCount)` partner — zero-axiom, structural.  The counting core: the three-way
partition count (`partitionCountThree` + `partitionThree_of_involution`), the pairing bijection
`|larger cap feet| = |smaller cap feet|` (`capLargerFeetIndices_length_eq`, via `distinctSameMembersLengthEq`), the
doubling (`expandBottomFeetPairs_length`), and the interleaved-pair distinctness (`capArcFeet_distinct`).  Promotes the
r15 `by decide` bottom probes (`readOffBottomOrder_isPermutationOfRange_adversarialB` / `_freshMixed`) to the general
theorem — the r15 bottom counting residual is CLOSED.  `= true`. -/
def fxBrauer_hasReadOffBottomOrderPermutation : Bool := true

/-- ★★★ **Honesty marker — the BOTTOM E2 roundtrip is wired UNIVERSALLY (r16).**  `readOffBottomOrder_realizesRoundtrip`
feeds the general bottom range-permutation witness into the shipped conjugator roundtrip
`permuteOfCrossingWord_permutationToCrossingWord`, so the `permutationToCrossingWord` staircase realizes the bottom
read-off order for EVERY well-formed involution — the r15 probe-granular E2 wiring
(`readOffBottomOrder_realizesRoundtrip_adversarialB` / `_freshMixed`) promoted to a general theorem.  `= true`. -/
def fxBrauer_hasReadOffBottomOrderRoundtrip : Bool := true

/-- **Honesty WALL marker — the TOP read-off order range-permutation is the named r16 residual (T-CLOSE top side).**
The bottom read-off is now a general range-permutation, but `fxBrauer_hasReadOffOrderPermutation` demands BOTH sides:
the top read-off `throughStrandTops ++ cupArcTops` still needs its ∗-dual counting identity
(`2·|cupArcTopIndices| + |throughStrandTops| = topCount`) — the dual partition count over `List.range topCount`, the
dual pairing bijection, and the interleaved-top distinctness, with the `cupArcTops` `− bottomCount` subtraction handled
additively (`cupArcTop_sub_exact`).  Every generic engine here (`partitionCountThree`, `filterMapLength_eq_countTrue`,
`distinctSameMembersLengthEq`, `filterMapGuardIdentityDistinctCount`, `appendDistinctCount`) is guard-generic and
reused verbatim; the top round instantiates them over the `bottomCount + topIndex` ports.  Then the inverted top
read-off closes by r15's `isPermutationOfRange_permInverse`.  So `fxBrauer_hasReadOffOrderPermutation` stays honestly
`false`, and — since E3 (fold-alignment / T-CONNECT, the union-find `stepWiring` long-pole) and the T-CLOSE(b) field
reassembly are untouched — both tag-correspondence masters stay `false`; #2013 does NOT close.  `= false`. -/
def fxBrauer_hasReadOffTopOrderPermutation : Bool := false

/-- ★★★ **The BRAUER-MIDDLE r16 LEDGER — MACHINE-CHECKED (T-CLOSE bottom side landed).**  Extends the r15 ledger with
the two bottom flips `fxBrauer_hasReadOffBottomOrderPermutation = true` (the general bottom read-off
`IsPermutationOfRange`) and `fxBrauer_hasReadOffBottomOrderRoundtrip = true` (the universal bottom E2 wiring), each
zero-axiom.  Every r11→r15 marker stays `true`; and EVERY remaining wall stays `false` — the JOINT read-off order
permutation (`fxBrauer_hasReadOffOrderPermutation`, blocked on the TOP-side dual counting identity), the CONJUGATED
enumeration node (E3 fold-alignment), both tag-correspondence masters, the extractor-totality roundtrip nodes, and the
completeness flags.  A `rfl`-conjunction over the shipped markers.  The remaining chain to the masters: **the TOP-side
read-off counting identity** (`throughStrandTops ++ cupArcTops` `IsPermutationOfRange`, then `permInverse` lift) **→ E3**
(union-find `stepWiring` long-pole) **→ T-CLOSE(b)** (the `extractDiagram` field reassembly) **→ the master flips**.  So
#2013 does NOT close this round. -/
theorem fxBrauer_r16Ledger :
    (fxBrauer_hasBoundedBoundaryFoldLift = true
      ∧ fxBrauer_hasPartnerReadOff = true
      ∧ fxBrauer_hasBoundaryPartneredFold = true
      ∧ fxBrauer_hasReadOffWiredFiring = true
      ∧ fxBrauer_hasArcEnumeration = true
      ∧ fxBrauer_hasArcConjugatorLeg = true
      ∧ fxBrauer_hasPermInverseRangePreservation = true
      ∧ fxBrauer_hasReadOffOrderPermutationProbe = true
      ∧ fxBrauer_hasReadOffRoundtripWiredProbe = true
      ∧ fxBrauer_hasReadOffBottomOrderPermutation = true
      ∧ fxBrauer_hasReadOffBottomOrderRoundtrip = true)
    ∧ (fxBrauer_hasReadOffTopOrderPermutation = false
      ∧ fxBrauer_hasReadOffOrderPermutation = false
      ∧ fxBrauer_hasArcEnumerationConjugated = false)
    ∧ (fxBrauer_hasTagCorrDisjoint = false
      ∧ fxBrauer_hasTagCorrExtraction = false)
    ∧ (fxBrauer_hasExt5CorrectedRoundtripProof = false
      ∧ fxBrauer_hasExt5TotalExtractorRoundtrip = false)
    ∧ (fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
    ⟨rfl, rfl, rfl⟩⟩

/-- ★★ **Honesty marker — BRAUER-MIDDLE r16 did NOT close #2013.**  The round CLOSED the T-CLOSE bottom side: the
general bottom read-off order `capArcFeet ++ throughStrandBottoms` is a range-permutation for every well-formed
involution (`readOffBottomOrder_isPermutationOfRange`), and the E2 roundtrip is wired universally on the bottom side —
each zero-axiom and structural, promoting the r15 `by decide` probes to general theorems.  But the TOP-side dual
counting identity (`throughStrandTops ++ cupArcTops` `IsPermutationOfRange` + the `permInverse` lift), E3
(fold-alignment / T-CONNECT), and the T-CLOSE(b) field reassembly remain named, not built, so the JOINT read-off
permutation, both tag-correspondence masters, and the completeness flags stay `false`, and #2013 does not close — every
residual a ROUTE / counting gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).  `= false`. -/
def fxBrauer_hasBrauerMiddleR16Complete : Bool := false

end FX1Poly.Polygraph
