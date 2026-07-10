import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBoundedBoundaryFold

/-! # BRAUER-MIDDLE r11 B1 — the EXISTENCE leg: partner-TOTALITY of the boundary matching, SEED shipped

The r11 read-off (`Brauer/WiringDescPartnerReadOff.lean`) pins the partner of an in-range boundary index once a
same-component partner is EXHIBITED — it is the UNIQUENESS half.  The complementary EXISTENCE half is that the
partner map is TOTAL: every in-range boundary index actually has a genuine same-component partner
(`partnerIndex ≠ probeIndex`), equivalently `partnerIndexOf … i ≠ i` (the `notFixed` premise the involution and
the `d`-matching consumers need).  This file states that invariant (`boundaryPartnered`) and ships its SEED base
case, following the r6→r10 arc precedent (`boundedBoundaryComponents_seed` shipped first, the fold lift trailing).

The invariant is the perfect-matching content of a Brauer boundary: it pairs with the shipped
`boundedBoundaryComponents` (≤ 2 boundary indices per component) to give exactly-2 (each component a chord).  At
the fresh seed each strand `k` is read at the two boundary indices `k` (its bottom port) and `bottomCount + k`
(its top slot); those two indices are the genuine partner pair, and they are distinct precisely when
`0 < bottomCount`.

  * ★ `boundaryPartnered` — the partner-totality invariant, stated through the `propext`-free `matchingSameComponent`
    Bool exactly as `extractDiagram` reads it (so the read-off `partnerShares` premise is discharged verbatim).

  * ★ `boundaryPartnered_seed` — the SEED base case: `brauerSeed bottomCount` (all identity through-strands) is
    partner-total for `0 < bottomCount`, the bottom port `k` and top slot `bottomCount + k` reading the shared
    strand value.

This flips the NEW sub-marker `fxBrauer_hasBoundaryPartneredSeed`.  It does NOT flip the fold marker
`fxBrauer_hasBoundaryPartneredFold` (named `false`): the three per-atom preservations — cup (splice a fresh
same-component pair), crossing (transpose two reads, root multiset fixed), and cap (THE sub-long-pole: the two
capped ports must have partnered EACH OTHER, the genuine perfect-matching content not implied by `≤ 2` at the
point-set level) — plus the whole-`processBrauer` fold lift are the standing rungs, mirroring the r10 template.

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range + append + BEq plumbing (per-file copies, following the codebase pattern) -/

private theorem rangeLoopLengthBP : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLengthBP count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLengthBP (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLengthBP count []]
  exact Nat.add_zero count

private theorem rangeLoopGetAt_pastBP : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAt_pastBP count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAt_belowBP : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count → natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAt_belowBP count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAt_pastBP count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAt_belowBP (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAt_belowBP count [] index indexBelow

private theorem natListGetAt_appendLeftBP :
    (leftList rightList : List Nat) → (index : Nat) → index < leftList.length →
    natListGetAt (leftList ++ rightList) index = natListGetAt leftList index
  | [], _, _, indexBelow => absurd indexBelow (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: rest, rightList, index + 1, indexBelow =>
      natListGetAt_appendLeftBP rest rightList index (Nat.lt_of_succ_lt_succ indexBelow)

private theorem natListGetAt_appendAddBP :
    (leftList rightList : List Nat) → (offset : Nat) →
    natListGetAt (leftList ++ rightList) (leftList.length + offset) = natListGetAt rightList offset
  | [], rightList, offset => by
      show natListGetAt rightList (0 + offset) = natListGetAt rightList offset
      rw [Nat.zero_add]
  | head :: rest, rightList, offset => by
      show natListGetAt (head :: (rest ++ rightList)) ((rest.length + 1) + offset) = natListGetAt rightList offset
      rw [Nat.add_right_comm rest.length 1 offset]
      show natListGetAt (rest ++ rightList) (rest.length + offset) = natListGetAt rightList offset
      exact natListGetAt_appendAddBP rest rightList offset

/-- Reflexivity of `Nat` `BEq` — `Nat`'s `==` is `decide`-based, so `decide_eq_true rfl` closes it
(`propext`-free; the `Nat.beq_refl` / `beq_self_eq_true` route leaks `propext`). -/
private theorem natBeqSelf_BP (value : Nat) : (value == value) = true := decide_eq_true rfl

private theorem unionFindRootOf_nilBP (node : Nat) : unionFindRootOf [] node = node := rfl

/-! ## The seed boundary reads -/

/-- The seed boundary same-component relation reduces to a raw `Nat` `BEq` of the append read-offs (the seed has no
links, so every root is the node itself). -/
private theorem seedSameComponent_BP (bottomCount firstIndex secondIndex : Nat) :
    matchingSameComponent bottomCount (brauerSeed bottomCount) firstIndex secondIndex
      = (natListGetAt (List.range bottomCount ++ List.range bottomCount) firstIndex
          == natListGetAt (List.range bottomCount ++ List.range bottomCount) secondIndex) := by
  show (unionFindRootOf [] (natListGetAt (List.range bottomCount ++ List.range bottomCount) firstIndex)
        == unionFindRootOf [] (natListGetAt (List.range bottomCount ++ List.range bottomCount) secondIndex))
      = (natListGetAt (List.range bottomCount ++ List.range bottomCount) firstIndex
          == natListGetAt (List.range bottomCount ++ List.range bottomCount) secondIndex)
  rw [unionFindRootOf_nilBP, unionFindRootOf_nilBP]

/-- The bottom port `index < bottomCount` reads its own strand value in the seed boundary node list. -/
private theorem seedBottomRead_BP (bottomCount index : Nat) (indexBelow : index < bottomCount) :
    natListGetAt (List.range bottomCount ++ List.range bottomCount) index = index := by
  rw [natListGetAt_appendLeftBP (List.range bottomCount) (List.range bottomCount) index
        (by rw [rangeLengthBP]; exact indexBelow),
    rangeGetAt_belowBP bottomCount index indexBelow]

/-- The top slot `bottomCount + offset` (with `offset < bottomCount`) reads the same strand value `offset`. -/
private theorem seedTopRead_BP (bottomCount offset : Nat) (offsetBelow : offset < bottomCount) :
    natListGetAt (List.range bottomCount ++ List.range bottomCount) (bottomCount + offset) = offset := by
  rw [show bottomCount + offset = (List.range bottomCount).length + offset from
        congrArg (· + offset) (rangeLengthBP bottomCount).symm,
    natListGetAt_appendAddBP (List.range bottomCount) (List.range bottomCount) offset,
    rangeGetAt_belowBP bottomCount offset offsetBelow]

/-! ## The partner-totality invariant -/

/-- ★ **The partner-TOTALITY invariant (T-EXISTENCE).**  Every in-range boundary index of `state` (index
`< bottomCount + state.openWires.length`, reading `List.range bottomCount ++ state.openWires` exactly as
`extractDiagram` does) has a DISTINCT in-range boundary index sharing its union-find component.  Stated through the
`propext`-free `matchingSameComponent` Bool, so it plugs straight into the r11 read-off's `partnerShares`
premise.  Paired with `boundedBoundaryComponents` (≤ 2 per component) it forces exactly-2 — each component a
boundary chord, i.e. `partnerIndexOf` is a fixed-point-free involution. -/
def boundaryPartnered (bottomCount : Nat) (state : WireState) : Prop :=
  ∀ probeIndex, probeIndex < bottomCount + state.openWires.length →
    ∃ partnerIndex, partnerIndex < bottomCount + state.openWires.length
      ∧ partnerIndex ≠ probeIndex
      ∧ matchingSameComponent bottomCount state probeIndex partnerIndex = true

/-! ## The seed base case -/

/-- ★ **The SEED base case of partner-TOTALITY.**  The fresh seed `brauerSeed bottomCount` (all identity
through-strands) is partner-total for `0 < bottomCount`: a bottom port `probeIndex < bottomCount` pairs with its
top slot `bottomCount + probeIndex` (both read value `probeIndex`), and a top slot `bottomCount + gap` pairs back
with its bottom port `gap` (both read value `gap`).  The two indices are distinct precisely because
`0 < bottomCount` (the bottom / top split is nonempty), and same-component because the seed has no links so equal
read-off values give equal roots. -/
theorem boundaryPartnered_seed (bottomCount : Nat) (bottomPos : 0 < bottomCount) :
    boundaryPartnered bottomCount (brauerSeed bottomCount) := by
  intro probeIndex probeBelow
  have lengthEq : (brauerSeed bottomCount).openWires.length = bottomCount := rangeLengthBP bottomCount
  rw [lengthEq] at probeBelow ⊢
  cases Nat.lt_or_ge probeIndex bottomCount with
  | inl probeLow =>
      refine ⟨bottomCount + probeIndex, Nat.add_lt_add_left probeLow bottomCount, ?_, ?_⟩
      · exact Nat.ne_of_gt (Nat.lt_add_of_pos_left bottomPos)
      · rw [seedSameComponent_BP, seedBottomRead_BP bottomCount probeIndex probeLow,
          seedTopRead_BP bottomCount probeIndex probeLow]
        exact natBeqSelf_BP probeIndex
  | inr probeHigh =>
      obtain ⟨gap, gapEq⟩ := Nat.le.dest probeHigh
      have gapBelow : gap < bottomCount := by
        have widened : bottomCount + gap < bottomCount + bottomCount := by rw [gapEq]; exact probeBelow
        exact Nat.lt_of_add_lt_add_left widened
      refine ⟨gap, Nat.lt_of_lt_of_le gapBelow (Nat.le_add_left bottomCount bottomCount), ?_, ?_⟩
      · rw [← gapEq]
        exact Nat.ne_of_lt (Nat.lt_add_of_pos_left bottomPos)
      · rw [seedSameComponent_BP, ← gapEq, seedTopRead_BP bottomCount gap gapBelow,
          seedBottomRead_BP bottomCount gap gapBelow]
        exact natBeqSelf_BP gap

/-! ## Non-vacuity -/

/-- ★ **Non-vacuity — the seed partner-totality applies at a genuine `0 < bottomCount`.**  `brauerSeed 2` is
partner-total (a two-strand identity: index `0` pairs with `2`, index `1` with `3`), so `boundaryPartnered_seed`
is not vacuous. -/
theorem boundaryPartnered_seed_two : boundaryPartnered 2 (brauerSeed 2) :=
  boundaryPartnered_seed 2 (by decide)

/-- ★ **Cross-check firing — a concrete seed partner pair.**  Boundary index `0` (bottom port of strand `0`) and
index `2` (its top slot) are same-component in `brauerSeed 2`. -/
theorem boundaryPartnered_seedPair_firing :
    matchingSameComponent 2 (brauerSeed 2) 0 2 = true := by decide

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the partner-TOTALITY SEED is SHIPPED (r11 B1).**  `boundaryPartnered` states the
existence half of the tag correspondence — every in-range boundary index has a genuine same-component partner,
the `notFixed` / `partnerShares` premise the read-off and involution consumers need — and `boundaryPartnered_seed`
discharges it at the fresh seed (for `0 < bottomCount`), the bottom port and top slot of each strand being the
partner pair.  Non-vacuous (`boundaryPartnered_seed_two`, `boundaryPartnered_seedPair_firing`).  `= true`. -/
def fxBrauer_hasBoundaryPartneredSeed : Bool := true

/-- **Honesty marker — the partner-TOTALITY FOLD LIFT does NOT close this round.**  Beyond the seed, the r10
template needs the three per-atom preservations of `boundaryPartnered` and the whole-`processBrauer` fold lift:
the CUP splices a fresh same-component pair (two new partnered reads); the CROSSING transposes two boundary reads
with the root multiset fixed; and the CAP — THE sub-long-pole — is where the perfect-matching content lives: the
two capped ports must have partnered EACH OTHER, so a surviving index that partnered a capped port would lose its
boundary partner unless the cap consumes a matched pair, a fact NOT implied by `boundedBoundaryComponents` (≤ 2)
at the point-set level.  These preservations + the fold lift + the seed payoff (the partner-total analogue of
`boundedBoundaryComponents_reachable`) are the standing rungs; none is fabricated this round.  So
`fxBrauer_hasTagCorrDisjoint` / `fxBrauer_hasTagCorrExtraction`, the roundtrip flags, and the masters stay
`false`; #2013 does NOT close.  `= false`. -/
def fxBrauer_hasBoundaryPartneredFold : Bool := false

end FX1Poly.Polygraph
