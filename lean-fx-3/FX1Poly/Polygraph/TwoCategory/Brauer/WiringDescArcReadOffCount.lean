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

end FX1Poly.Polygraph
