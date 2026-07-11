import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBoundaryPartneredFold
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcReadOffCount

/-! # BRAUER r29 — the two dispatch EXPOSURES: boundary-matching symmetry + the value→rank roundtrip

The r29 unconditional `partnerShares_general` (the 6-way `partitionThree_of_involution` / `…_top` dispatch) needs
two ingredients that the lane has proven only PRIVATELY, three times over.  This file re-exposes each ONCE, publicly,
so every flip arm (arms 2 / 5 / 6, the `matchingSameComponent`-symmetric reorientations) and every rank-recovery arm
(the value→rank inversion on the arc enumeration lists) has a single public keystone to reach for.

## The two exposures

  * ★ `matchingSameComponent_symm` — the boundary same-component matching is symmetric.  A `dsimp`-thin wrapper of the
    public `isSameComponent_symm` (a `Nat` `BEq` of the two union-find roots), lifted through the definitional unfold
    `matchingSameComponent bc state a b = isSameComponent state.links (getAt (matchingBoundaryNodes bc state) a) (…b)`.
    The lane's three private copies (`matchingSameComponent_symmBBC` in `WiringDescBoundedBoundaryComponents`,
    `matchingSameComponent_symmBP` in `WiringDescBoundaryPartneredFold`) both go the same one-line route — this is their
    public promotion, the additive-flip precedent (r28's `fxBrauer_hasThroughArcGeneral` over the frozen r27 marker).

  * ★ `natIndexOfValueRoundtrip` — the value→rank roundtrip: for a value `∈ order`, `natListGetAt order
    (natIndexOfValue order value) = value` and `natIndexOfValue order value < order.length`.  Structural induction on
    `order`, casing the first-occurrence `Bool` `head == value` via `of_decide_eq_true` (propext-free, per the lane's
    `natBeqSelfDuality` discipline — NEVER `eq_of_beq`).  The private copies
    (`natIndexOfValueRoundtripPerm` in `WiringDescArcReadOffPermutation`, and duplicates in `WiringDescArcConjugator` /
    `WiringDescBrauerReadbackProof`) take `memBool value order = true`; this public copy takes the `List.Mem` the
    dispatch's `memFilterMapGuardComplete` produces directly, so no `memBool` bridge is needed at each arm.

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.  `==` handled via
`of_decide_eq_true`, never `eq_of_beq` (leaks `propext`).  Per-declaration `#assert_no_axioms` in the audit twin;
independent `#print axioms` clean. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Exposure 1 — boundary-matching symmetry -/

/-- ★★ **The boundary same-component matching is SYMMETRIC (public).**  `matchingSameComponent bottomCount state
indexA indexB` is definitionally `isSameComponent state.links (getAt boundaryNodes indexA) (getAt boundaryNodes
indexB)`, and `isSameComponent` is a `Nat` `BEq` of the two roots, hence symmetric.  The public promotion of the
lane's private `matchingSameComponent_symmBBC` / `matchingSameComponent_symmBP` — the flip keystone the dispatch's
cap-larger / cup-larger / through-top arms (arms 2 / 5 / 6) reorient the general matching lemma through. -/
theorem matchingSameComponent_symm (bottomCount : Nat) (state : WireState) (indexA indexB : Nat) :
    matchingSameComponent bottomCount state indexA indexB
      = matchingSameComponent bottomCount state indexB indexA := by
  show isSameComponent state.links (natListGetAt (matchingBoundaryNodes bottomCount state) indexA)
        (natListGetAt (matchingBoundaryNodes bottomCount state) indexB)
      = isSameComponent state.links (natListGetAt (matchingBoundaryNodes bottomCount state) indexB)
        (natListGetAt (matchingBoundaryNodes bottomCount state) indexA)
  exact isSameComponent_symm state.links _ _

/-- The `matchingSameComponent`-symmetric reorientation to `= true` — the direct form the flip arms consume: from a
same-component fact on `(indexB, indexA)` produce the one on `(indexA, indexB)`. -/
theorem matchingSameComponent_flipTrue (bottomCount : Nat) (state : WireState) (indexA indexB : Nat)
    (shares : matchingSameComponent bottomCount state indexB indexA = true) :
    matchingSameComponent bottomCount state indexA indexB = true := by
  rw [matchingSameComponent_symm bottomCount state indexA indexB]; exact shares

/-! ## Exposure 2 — the value→rank roundtrip -/

/-- The membership-consed value that is not the head lives in the tail. -/
private theorem memConsOfNeSymm (value head : Nat) (rest : List Nat) (mem : value ∈ head :: rest)
    (ne : value ≠ head) : value ∈ rest := by
  cases mem with
  | head => exact absurd rfl ne
  | tail _ memRest => exact memRest

/-- ★★ **The value→rank roundtrip (public).**  For every `value` that occurs in `order`, the first-occurrence index
`natIndexOfValue order value` reads back to `value` under `natListGetAt` and lies below `order.length`.  Structural
induction on `order`, casing the head `Bool` equality `head == value` via `of_decide_eq_true` (propext-free).  The
public promotion of the lane's private `natIndexOfValueRoundtripPerm` — the rank-recovery keystone every dispatch arm
feeds its arc-enumeration list membership through to name the rank. -/
theorem natIndexOfValueRoundtrip : (order : List Nat) → (value : Nat) → value ∈ order →
    natListGetAt order (natIndexOfValue order value) = value ∧ natIndexOfValue order value < order.length
  | [], _, memNil => nomatch memNil
  | head :: rest, value, mem => by
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
          have headNe : head ≠ value := of_decide_eq_false hbeq
          have valueNeHead : value ≠ head := fun equal => headNe equal.symm
          have memRest : value ∈ rest := memConsOfNeSymm value head rest mem valueNeHead
          have ih := natIndexOfValueRoundtrip rest value memRest
          have indexSucc : natIndexOfValue (head :: rest) value = natIndexOfValue rest value + 1 := by
            show (match head == value with | true => 0 | false => natIndexOfValue rest value + 1)
              = natIndexOfValue rest value + 1
            rw [hbeq]
          refine ⟨?_, ?_⟩
          · rw [indexSucc]; exact ih.1
          · rw [indexSucc]; exact Nat.succ_lt_succ ih.2

/-! ## B1 — the classification truth-probes (eval FIRST): the 3-way partition is exhaustive+exclusive per port

Before the six-arm `partnerShares_general` consumes `partitionThree_of_involution` / `…_top`, probe the classification
CONCRETELY on three shapes: a MIXED involution (one cap, one through, one cup — the monster in miniature), an
ALL-THROUGH permutation (every boundary port a through), and the ALL-LOOP diagram (no boundary ports, the partition
vacuous, the loops dominate).  Each bottom port lands in exactly one of `capSmallerGuard` / `capLargerGuard` /
`throughBottomGuard`; each top port in exactly one of `cupSmallerGuard` / `cupLargerGuard` / `throughTopGuard`. -/

/-- The MIXED probe involution `[2, 4, 0, 5, 1, 3]` (bottomCount 3, total 6) is a boundary involution — one cap
`0 ↔ 2`, one through `1 ↔ top1`, one cup `top0 ↔ top2`, the monster in miniature. -/
theorem isBoundaryInvolution_mixedProbe :
    IsBoundaryInvolution 6 [2, 4, 0, 5, 1, 3] where
  hasBoundaryLength := rfl
  mapsInRange := by decide
  isSelfInverse := by decide
  isFixedPointFree := by decide

/-- ★ **Classification probe (MIXED, bottom side) — via the SHIPPED lemma.**  Firing `partitionThree_of_involution`
on the mixed involution at each bottom port PRODUCES the exhaustive+exclusive `onlyOneTrueThree` (not a re-`decide`):
bottom `0` is a cap-smaller foot (`0 ↔ 2`), bottom `1` a through-bottom (`1 ↔ top1`), bottom `2` a cap-larger foot
(`2 ↔ 0`) — the exact classification the dispatch's bottom-port split consumes. -/
theorem classificationProbe_bottom_mixed :
    onlyOneTrueThree (capSmallerGuard 3 [2, 4, 0, 5, 1, 3] 0) (capLargerGuard 3 [2, 4, 0, 5, 1, 3] 0)
        (throughBottomGuard 3 [2, 4, 0, 5, 1, 3] 0)
    ∧ onlyOneTrueThree (capSmallerGuard 3 [2, 4, 0, 5, 1, 3] 2) (capLargerGuard 3 [2, 4, 0, 5, 1, 3] 2)
        (throughBottomGuard 3 [2, 4, 0, 5, 1, 3] 2) :=
  ⟨partitionThree_of_involution 3 6 [2, 4, 0, 5, 1, 3] (by decide) isBoundaryInvolution_mixedProbe 0 (by decide),
   partitionThree_of_involution 3 6 [2, 4, 0, 5, 1, 3] (by decide) isBoundaryInvolution_mixedProbe 2 (by decide)⟩

/-- ★ **Classification probe (MIXED, top side) — via the SHIPPED `…_top` lemma.**  Top `0` is a cup-smaller foot
(`top0 ↔ top2`), top `2` a cup-larger foot (`top2 ↔ top0`) — the top-port split the dispatch consumes. -/
theorem classificationProbe_top_mixed :
    onlyOneTrueThree (cupSmallerGuard 3 [2, 4, 0, 5, 1, 3] 0) (cupLargerGuard 3 [2, 4, 0, 5, 1, 3] 0)
        (throughTopGuard 3 [2, 4, 0, 5, 1, 3] 0)
    ∧ onlyOneTrueThree (cupSmallerGuard 3 [2, 4, 0, 5, 1, 3] 2) (cupLargerGuard 3 [2, 4, 0, 5, 1, 3] 2)
        (throughTopGuard 3 [2, 4, 0, 5, 1, 3] 2) :=
  ⟨partitionThree_of_involution_top 3 3 6 [2, 4, 0, 5, 1, 3] (by decide) isBoundaryInvolution_mixedProbe 0 (by decide),
   partitionThree_of_involution_top 3 3 6 [2, 4, 0, 5, 1, 3] (by decide) isBoundaryInvolution_mixedProbe 2 (by decide)⟩

/-- ★ **Classification probe (ALL-THROUGH `[2, 3, 0, 1]`, bottomCount 2).**  Every bottom port is a through-bottom
(both partners are top ports) and every top port a through-top — the pure-through corner of the six-arm split, no cap
or cup arm ever fires.  Each guard `decide`s to its expected Bool. -/
theorem classificationProbe_allThrough :
    (throughBottomGuard 2 [2, 3, 0, 1] 0 = true ∧ throughBottomGuard 2 [2, 3, 0, 1] 1 = true
      ∧ throughTopGuard 2 [2, 3, 0, 1] 0 = true ∧ throughTopGuard 2 [2, 3, 0, 1] 1 = true)
    ∧ (capSmallerGuard 2 [2, 3, 0, 1] 0 = false ∧ capLargerGuard 2 [2, 3, 0, 1] 0 = false
      ∧ cupSmallerGuard 2 [2, 3, 0, 1] 0 = false ∧ cupLargerGuard 2 [2, 3, 0, 1] 0 = false) :=
  ⟨⟨by decide, by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide⟩

/-- ★ **Classification probe (ALL-LOOP `{0, 0, [], 3}`).**  No boundary ports: the classification is vacuous, every
arc-enumeration list is empty, and the three partition counts are `0` — the loops carry all the content (T-CLOSE(b)
`loops` field territory, B3).  The `partitionCountThree` sum degenerates to `0 = 0`. -/
theorem classificationProbe_allLoop :
    (capArcFeetIndices 0 [] = [] ∧ throughStrandBottoms 0 [] = []
      ∧ cupArcTopIndices 0 0 [] = [] ∧ throughStrandTops 0 0 [] = []) :=
  ⟨rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph
