import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescUntwist

/-! # WP-BRAUER-4 r4 — the constructive STRAIGHTENING blocks (untwist absorption + free Coxeter moves)

The r3 seven-relation extension (`Brauer/WiringDescUntwist.lean`) dissolved the r2 crossing-parity wall: the two
Lehrer–Zhang untwist rows (`σ ∘ cup = cup`, `cap ∘ σ = cap`, arXiv:1207.5889 Thm 2.6) close the last independent
character, so the residual `fxBrauer_hasBrauerCompleteness` is now purely CONSTRUCTIVE — an explicit rewrite
realization (every diagram-equal pair straightens to a common normal form), not an obstruction.

This file lands the two straightening blocks that close CLEANLY this round, both over the seven-relation
over-approximation `BrauerConvFree7` (whose whiskerings are UNCONDITIONAL — this is the round-4 key: the
suffix-congruence leg named as the r2 residual of `fxBrauer_hasCrossingOnlyStraightening` is now FREE, supplied by
`BrauerConvFree7.whiskerRight`, and needs no `MatchingConnectivityViewSim`-preservation lemma through
`processBrauer`).

## Block (a) — UNTWIST ABSORPTION (the crossing-count measure leg)

`crossingCount` counts crossing generators; each untwist application (a crossing adjacent to a cup / cap arc) is
`BrauerConvFree7` in ARBITRARY horizontal context (`cupUntwistAbsorb` / `capUntwistAbsorb`, via free
whiskerLeft + whiskerRight of the `cupUntwist` / `capUntwist` rows) and STRICTLY reduces `crossingCount` by exactly
one (`cupUntwistAbsorb_crossingCount` / `capUntwistAbsorb_crossingCount`, through the fold homomorphism
`crossingCount_append`).  This is measure-leg-1 of the lexicographic straightening fuel, made concrete.

## Block (b) — the FREE COXETER moves (R2 cancel / R3 braid / distant commute), UNCONDITIONAL, in any context

The three Matsumoto generators for `S_n` — `s² = 1` (R2), the braid `s_p s_{p+1} s_p = s_{p+1} s_p s_{p+1}` (R3),
and the distant commutation `s_p s_q = s_q s_p` for `q ≥ p + 2` — each fire as `BrauerConvFree7` with NO width /
in-range side-condition (unlike the shipped `brauerConv_crossing_*` over the diagram-gated `BrauerConv`), because
`BrauerConvFree7` embeds `BrauerConvFree`'s offset-relations + interchange (`ofFree`) and closes freely under
whiskering.  So they compose in arbitrary prefix AND suffix context (`crossingCancelFree_inContext`, …) — the exact
generators a bubble-sort insertion induction consumes, with the suffix congruence FREE.

## Honest scope — what is NOT closed, and the exact jam

The MASTER `fxBrauer_hasBrauerCompleteness` STAYS `false` (`fxBrauer_hasCrossingOnlyStraightening` is now `true` via
the comb-fold BREACH r2, `crossingWords_equalPerm_conv`; this file's INSERTION route remains the historical jam) (honestly, not
walled — Lehrer–Zhang Thm 2.6 guarantees NO relation 8; any jam is a route/measure gap).  The remaining leg after
this round is the CANONICAL reduced word `canonicalReducedWord` + its braid-move INSERTION induction (insert one
adjacent transposition into the canonical word of a permutation, driven by these free Coxeter moves) — the standard
Matsumoto/Tits word problem for `S_n`, whose faithful zero-axiom structural-fuel formalization is the sibling
`ArcCupSortComplete` (`pureCupSpine_sort`, 1300+ lines).  For the master additionally the crossing block must
connect to the DIAGRAM invariant via the general readback
`brauerDiagramOf n (crossingWord w) = permutationDiagram n (permuteOfCrossingWord n w)` (SMOKES-only, the union-find
state invariant), and the whole diagram must factor into the Lehrer–Zhang regular form (caps ∘ permutation ∘ cups,
Lemma 2.13) — no shipped pattern.  Those three — canonical-word insertion, general readback, regular-form
factorization — are the named residual.  Soundness (`brauerConv_sound`, `brauerConv_crossing_not_identity`,
`Brauer/WiringDescConv.lean`) is UNTOUCHED: the sound relation `BrauerConv` still keeps the crossing distinct from
the identity (these blocks live in the completeness-only over-approximation and never weaken it).

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local subtraction-free arithmetic (Init's cancels leak `propext`) -/

/-- `value + 2 - 2 = value` — a single `rfl` (the two `Nat.pred`s cancel the two `Nat.succ`s). -/
private theorem addTwoSubTwoStr (value : Nat) : value + 2 - 2 = value := rfl

/-- `value - 2 + 2 = value` when `2 ≤ value` — the crossing-arity round-trip.  Structural on the `value + 2` shape
(`2 ≤ value` rules out `0` / `1`). -/
private theorem subTwoAddTwoStr : (value : Nat) → 2 ≤ value → value - 2 + 2 = value
  | 0, twoLe => absurd twoLe (by decide)
  | 1, twoLe => absurd twoLe (by decide)
  | value + 2, _ => by rw [addTwoSubTwoStr value]

/-! ## Block (a) — the crossing-count measure

`crossingCount` tallies the crossing generators of a word; it is a monoid homomorphism to `(Nat, +)` over word
concatenation.  Under an untwist absorption it drops by exactly one — the untwist eliminates a crossing adjacent to
a cup / cap arc, which is measure-leg-1 of the lexicographic straightening fuel. -/

/-- Is this atom a crossing, as a `Nat` bit (`1` / `0`)?  Full-enum match on the `Bool`, propext-free. -/
def crossingBit (atom : BrauerAtom) : Nat :=
  match isCrossingAtom atom with
  | true => 1
  | false => 0

/-- ★ **The crossing count of a word** — the `Nat` fold of the crossing bit over the word. -/
def crossingCount : List BrauerAtom → Nat
  | [] => 0
  | atom :: rest => crossingBit atom + crossingCount rest

/-- ★ **`crossingCount` is additive over concatenation** — the fold is a monoid homomorphism to `(Nat, +)`.
Structural on the left word. -/
theorem crossingCount_append :
    (leftWord rightWord : List BrauerAtom) →
    crossingCount (leftWord ++ rightWord) = crossingCount leftWord + crossingCount rightWord
  | [], rightWord => (Nat.zero_add (crossingCount rightWord)).symm
  | atom :: rest, rightWord => by
      show crossingBit atom + crossingCount (rest ++ rightWord)
        = crossingBit atom + crossingCount rest + crossingCount rightWord
      rw [crossingCount_append rest rightWord]
      exact (Nat.add_assoc (crossingBit atom) (crossingCount rest) (crossingCount rightWord)).symm

/-! ## Block (a) — the two untwist rows at an ARBITRARY horizontal position

The `BrauerConvFree7.cupUntwist` / `capUntwist` constructors fire at any horizontal offset `shift`; re-based to an
explicit boundary position `position` via `Nat.zero_add` on the `0 + position` the shift produces. -/

/-- ★ **The cup untwist `σ ∘ cup = cup` at any position** — `[cupAt position, crossingAt position]` is
`BrauerConvFree7` to the bare `[cupAt position]`. -/
theorem cupUntwistAt (position : Nat) :
    BrauerConvFree7 [cupAt position, crossingAt position] [cupAt position] := by
  have base := BrauerConvFree7.cupUntwist position
  have lhsEq : shiftWord position cupUntwistRelation.lhs = [cupAt position, crossingAt position] := by
    show [({ position := 0 + position, wiring := cupWiring } : BrauerAtom),
          { position := 0 + position, wiring := crossingWiring }]
        = [cupAt position, crossingAt position]
    rw [Nat.zero_add]; rfl
  have rhsEq : shiftWord position cupUntwistRelation.rhs = [cupAt position] := by
    show [({ position := 0 + position, wiring := cupWiring } : BrauerAtom)] = [cupAt position]
    rw [Nat.zero_add]; rfl
  rw [lhsEq, rhsEq] at base
  exact base

/-- ★ **The cap untwist `cap ∘ σ = cap` at any position** — `[crossingAt position, capAt position]` is
`BrauerConvFree7` to the bare `[capAt position]`. -/
theorem capUntwistAt (position : Nat) :
    BrauerConvFree7 [crossingAt position, capAt position] [capAt position] := by
  have base := BrauerConvFree7.capUntwist position
  have lhsEq : shiftWord position capUntwistRelation.lhs = [crossingAt position, capAt position] := by
    show [({ position := 0 + position, wiring := crossingWiring } : BrauerAtom),
          { position := 0 + position, wiring := capWiring }]
        = [crossingAt position, capAt position]
    rw [Nat.zero_add]; rfl
  have rhsEq : shiftWord position capUntwistRelation.rhs = [capAt position] := by
    show [({ position := 0 + position, wiring := capWiring } : BrauerAtom)] = [capAt position]
    rw [Nat.zero_add]; rfl
  rw [lhsEq, rhsEq] at base
  exact base

/-! ## Block (a) — untwist ABSORPTION in arbitrary context + the strict crossing-count drop -/

/-- ★ **Cup untwist absorption in arbitrary horizontal context.**  A cup-then-crossing on the cup's own legs,
sitting between ANY prefix and suffix words, is `BrauerConvFree7` to the bare cup in that context — the free
whiskerLeft + whiskerRight of `cupUntwistAt`.  The suffix congruence is FREE (`BrauerConvFree7.whiskerRight`). -/
theorem cupUntwistAbsorb (prefixWord suffixWord : List BrauerAtom) (position : Nat) :
    BrauerConvFree7 (prefixWord ++ ([cupAt position, crossingAt position] ++ suffixWord))
      (prefixWord ++ ([cupAt position] ++ suffixWord)) :=
  BrauerConvFree7.whiskerLeft prefixWord
    (BrauerConvFree7.whiskerRight suffixWord (cupUntwistAt position))

/-- ★ **Cap untwist absorption in arbitrary horizontal context.** -/
theorem capUntwistAbsorb (prefixWord suffixWord : List BrauerAtom) (position : Nat) :
    BrauerConvFree7 (prefixWord ++ ([crossingAt position, capAt position] ++ suffixWord))
      (prefixWord ++ ([capAt position] ++ suffixWord)) :=
  BrauerConvFree7.whiskerLeft prefixWord
    (BrauerConvFree7.whiskerRight suffixWord (capUntwistAt position))

/-- The cup untwist strictly drops the crossing count by one at the redex (`1 = 0 + 1`). -/
theorem cupUntwist_crossingCount (position : Nat) :
    crossingCount [cupAt position, crossingAt position] = crossingCount [cupAt position] + 1 := rfl

/-- The cap untwist strictly drops the crossing count by one at the redex. -/
theorem capUntwist_crossingCount (position : Nat) :
    crossingCount [crossingAt position, capAt position] = crossingCount [capAt position] + 1 := rfl

/-- ★ **The cup untwist strictly drops the crossing count by one IN CONTEXT.**  The measure decreases by exactly
one across any prefix / suffix — the fold homomorphism `crossingCount_append` cancels the common prefix / suffix
and the redex contributes `1` vs `0`. -/
theorem cupUntwistAbsorb_crossingCount (prefixWord suffixWord : List BrauerAtom) (position : Nat) :
    crossingCount (prefixWord ++ ([cupAt position, crossingAt position] ++ suffixWord))
      = crossingCount (prefixWord ++ ([cupAt position] ++ suffixWord)) + 1 := by
  rw [crossingCount_append prefixWord ([cupAt position, crossingAt position] ++ suffixWord),
    crossingCount_append [cupAt position, crossingAt position] suffixWord,
    crossingCount_append prefixWord ([cupAt position] ++ suffixWord),
    crossingCount_append [cupAt position] suffixWord]
  show crossingCount prefixWord + (1 + crossingCount suffixWord)
    = crossingCount prefixWord + (0 + crossingCount suffixWord) + 1
  rw [Nat.zero_add, Nat.add_comm 1 (crossingCount suffixWord),
    ← Nat.add_assoc (crossingCount prefixWord) (crossingCount suffixWord) 1]

/-- ★ **The cap untwist strictly drops the crossing count by one IN CONTEXT.**  The exact mirror of
`cupUntwistAbsorb_crossingCount`: the redex `[crossingAt position, capAt position]` contributes `1` to the crossing
count while its reduced form `[capAt position]` contributes `0`, so the measure decreases by exactly one across any
prefix / suffix — the fold homomorphism `crossingCount_append` cancels the common context. -/
theorem capUntwistAbsorb_crossingCount (prefixWord suffixWord : List BrauerAtom) (position : Nat) :
    crossingCount (prefixWord ++ ([crossingAt position, capAt position] ++ suffixWord))
      = crossingCount (prefixWord ++ ([capAt position] ++ suffixWord)) + 1 := by
  rw [crossingCount_append prefixWord ([crossingAt position, capAt position] ++ suffixWord),
    crossingCount_append [crossingAt position, capAt position] suffixWord,
    crossingCount_append prefixWord ([capAt position] ++ suffixWord),
    crossingCount_append [capAt position] suffixWord]
  show crossingCount prefixWord + (1 + crossingCount suffixWord)
    = crossingCount prefixWord + (0 + crossingCount suffixWord) + 1
  rw [Nat.zero_add, Nat.add_comm 1 (crossingCount suffixWord),
    ← Nat.add_assoc (crossingCount prefixWord) (crossingCount suffixWord) 1]

/-! ## Block (b) — the FREE Coxeter moves (unconditional, in any context) -/

/-- ★ **Coxeter CANCEL (R2, `s² = 1`), FREE.**  A double crossing at any position is `BrauerConvFree7` to the empty
word — the crossing involution embedded via `ofFree`, with NO width side-condition (unlike the diagram-gated
`brauerConv_crossing_cancel`). -/
theorem crossingCancelFree (position : Nat) :
    BrauerConvFree7 [crossingAt position, crossingAt position] [] := by
  have base := BrauerConvFree7.ofFree (BrauerConvFree.crossingInvolution position)
  have lhsEq : shiftWord position crossingInvolutionRelation.lhs
      = [crossingAt position, crossingAt position] := by
    show [({ position := 0 + position, wiring := crossingWiring } : BrauerAtom),
          { position := 0 + position, wiring := crossingWiring }]
        = [crossingAt position, crossingAt position]
    rw [Nat.zero_add]; rfl
  rw [lhsEq] at base
  exact base

/-- ★ **Coxeter BRAID (R3, `s_p s_{p+1} s_p = s_{p+1} s_p s_{p+1}`), FREE.**  Yang–Baxter embedded via `ofFree`,
unconditional. -/
theorem crossingBraidFree (position : Nat) :
    BrauerConvFree7 [crossingAt position, crossingAt (position + 1), crossingAt position]
      [crossingAt (position + 1), crossingAt position, crossingAt (position + 1)] := by
  have base := BrauerConvFree7.ofFree (BrauerConvFree.yangBaxter position)
  have lhsEq : shiftWord position yangBaxterRelation.lhs
      = [crossingAt position, crossingAt (position + 1), crossingAt position] := by
    show [({ position := 0 + position, wiring := crossingWiring } : BrauerAtom),
          { position := 1 + position, wiring := crossingWiring },
          { position := 0 + position, wiring := crossingWiring }]
        = [crossingAt position, crossingAt (position + 1), crossingAt position]
    rw [Nat.zero_add, Nat.add_comm 1 position]; rfl
  have rhsEq : shiftWord position yangBaxterRelation.rhs
      = [crossingAt (position + 1), crossingAt position, crossingAt (position + 1)] := by
    show [({ position := 1 + position, wiring := crossingWiring } : BrauerAtom),
          { position := 0 + position, wiring := crossingWiring },
          { position := 1 + position, wiring := crossingWiring }]
        = [crossingAt (position + 1), crossingAt position, crossingAt (position + 1)]
    rw [Nat.zero_add, Nat.add_comm 1 position]; rfl
  rw [lhsEq, rhsEq] at base
  exact base

/-- ★ **Coxeter COMMUTE (distant `s_p s_q = s_q s_p`, `p + 2 ≤ q`), FREE.**  The interchange (Godement) move
embedded via `ofFree`; the moved-position round-trip `q - 2 + 2 = q` is discharged by `subTwoAddTwoStr` from
`2 ≤ q`. -/
theorem crossingCommuteFree (positionLeft positionRight : Nat)
    (disjoint : positionLeft + 2 ≤ positionRight) :
    BrauerConvFree7 [crossingAt positionLeft, crossingAt positionRight]
      [crossingAt positionRight, crossingAt positionLeft] := by
  have twoLe : 2 ≤ positionRight := Nat.le_trans (Nat.le_add_left 2 positionLeft) disjoint
  have base : BrauerConvFree
      [crossingAt positionLeft, (⟨positionRight - 2 + 2, crossingWiring⟩ : BrauerAtom)]
      [crossingAt positionRight, crossingAt positionLeft] :=
    BrauerConvFree.interchange positionLeft positionRight crossingWiring crossingWiring disjoint
  rw [subTwoAddTwoStr positionRight twoLe] at base
  exact BrauerConvFree7.ofFree base

/-! ## Block (b) — the Coxeter moves in arbitrary prefix / suffix context (suffix congruence FREE) -/

/-- ★ **R2 cancel in arbitrary context.**  A trailing / interior double crossing straightens away between ANY
prefix and suffix — free whiskerLeft + whiskerRight.  This is the "suffix congruence is free" realization: the
`BrauerConvFree7.whiskerRight` supplies the trailing-context move that the diagram-gated `BrauerConv` cannot without
a `MatchingConnectivityViewSim`-preservation lemma. -/
theorem crossingCancelFree_inContext (prefixWord suffixWord : List BrauerAtom) (position : Nat) :
    BrauerConvFree7 (prefixWord ++ ([crossingAt position, crossingAt position] ++ suffixWord))
      (prefixWord ++ suffixWord) :=
  BrauerConvFree7.whiskerLeft prefixWord
    (BrauerConvFree7.whiskerRight suffixWord (crossingCancelFree position))

/-- ★ **R3 braid in arbitrary context.** -/
theorem crossingBraidFree_inContext (prefixWord suffixWord : List BrauerAtom) (position : Nat) :
    BrauerConvFree7
      (prefixWord ++ ([crossingAt position, crossingAt (position + 1), crossingAt position] ++ suffixWord))
      (prefixWord ++ ([crossingAt (position + 1), crossingAt position, crossingAt (position + 1)] ++ suffixWord)) :=
  BrauerConvFree7.whiskerLeft prefixWord
    (BrauerConvFree7.whiskerRight suffixWord (crossingBraidFree position))

/-- ★ **Distant commute in arbitrary context.** -/
theorem crossingCommuteFree_inContext (prefixWord suffixWord : List BrauerAtom)
    (positionLeft positionRight : Nat) (disjoint : positionLeft + 2 ≤ positionRight) :
    BrauerConvFree7 (prefixWord ++ ([crossingAt positionLeft, crossingAt positionRight] ++ suffixWord))
      (prefixWord ++ ([crossingAt positionRight, crossingAt positionLeft] ++ suffixWord)) :=
  BrauerConvFree7.whiskerLeft prefixWord
    (BrauerConvFree7.whiskerRight suffixWord (crossingCommuteFree positionLeft positionRight disjoint))

/-! ## Non-vacuity — the r2 pair straightens; an R3 pair; soundness intact -/

/-- ★ **The r2 wall pair is derivable THROUGH the straightening, and its crossing count strictly drops.**  The
exact pair the r2 wall proved unreachable by the five relations (`[cupAt 0, crossingAt 0]` vs `[cupAt 0]`) is the
untwist absorption at the empty context, and its `crossingCount` measure falls `1 → 0`.  So the untwist block both
derives the pair and fires its measure leg. -/
theorem r2Pair_straightens :
    BrauerConvFree7 [cupAt 0, crossingAt 0] [cupAt 0]
      ∧ crossingCount [cupAt 0, crossingAt 0] = crossingCount [cupAt 0] + 1 :=
  ⟨cupUntwistAbsorb [] [] 0, rfl⟩

/-- ★ **An R3 pair is derivable** — the two Yang–Baxter words on three strands, via the free braid move. -/
theorem r3Pair_straightens :
    BrauerConvFree7 [crossingAt 0, crossingAt 1, crossingAt 0] [crossingAt 1, crossingAt 0, crossingAt 1] :=
  crossingBraidFree 0

/-- ★ **Soundness intact — the crossing stays NOT convertible to the identity in the SOUND relation.**  These
straightening blocks live in the completeness-only over-approximation `BrauerConvFree7`; the sound convertibility
`BrauerConv` (`Brauer/WiringDescConv.lean`) is untouched, and still keeps the crossing distinct from the identity
pair (else `brauerConv_sound` would equate their distinct diagrams).  So the round does not weaken soundness. -/
theorem soundness_crossing_not_identity_preserved :
    ¬ BrauerConv 2 [crossingAt 0] [identityStrandAt 0, identityStrandAt 1] :=
  brauerConv_crossing_not_identity

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the UNTWIST ABSORPTION block is SHIPPED (measure-leg-1).**  Each untwist (a crossing
adjacent to a cup / cap arc) is `BrauerConvFree7` in ARBITRARY horizontal context (`cupUntwistAbsorb` /
`capUntwistAbsorb`, free whiskerLeft + whiskerRight of `cupUntwistAt` / `capUntwistAt`) and STRICTLY drops the
crossing-count measure by exactly one (`cupUntwistAbsorb_crossingCount` / `capUntwistAbsorb_crossingCount`, via the
fold homomorphism `crossingCount_append`).  Non-vacuous: `r2Pair_straightens` derives the exact r2 wall pair through
the absorption and fires its measure leg `1 → 0`.  This is measure-leg-1 of the lexicographic straightening fuel,
made concrete; it does NOT assemble the full straightening.  `= true`. -/
def fxBrauer_hasUntwistAbsorption : Bool := true

/-- ★ **Honesty marker — the FREE COXETER moves are SHIPPED (suffix congruence FREE).**  The three Matsumoto
generators for `S_n` — R2 cancel (`crossingCancelFree`), R3 braid (`crossingBraidFree`), distant commute
(`crossingCommuteFree`) — fire as `BrauerConvFree7` with NO width / in-range side-condition (embedding
`BrauerConvFree`'s offset-relations + interchange via `ofFree`), and compose in arbitrary prefix AND suffix context
(`crossingCancelFree_inContext` / `crossingBraidFree_inContext` / `crossingCommuteFree_inContext`).  This DISCHARGES
the suffix-congruence leg named as the r2 residual of `fxBrauer_hasCrossingOnlyStraightening`: `BrauerConvFree7`'s
unconditional whiskerRight supplies the trailing-context move without any `MatchingConnectivityViewSim`-preservation
lemma through `processBrauer`.  Non-vacuous: `r3Pair_straightens`.  It does NOT assemble the full crossing-only
straightening — the standing jam is the canonical reduced word + its braid-move INSERTION induction (Matsumoto/Tits
for `S_n`), whose faithful zero-axiom mirror is the 1300-line sibling `pureCupSpine_sort`.  `= true`. -/
def fxBrauer_hasCrossingWordFreeCoxeterMoves : Bool := true

/-- **Honesty marker — the crossing-only straightening ASSEMBLY via the INSERTION route stays jammed (the comb fold in
`Brauer/WiringDescStaircaseCanonical.lean` is the route that flipped `fxBrauer_hasCrossingOnlyStraightening` to `true`).**  With the
suffix congruence now FREE (`fxBrauer_hasCrossingWordFreeCoxeterMoves`) and untwist absorption shipped
(`fxBrauer_hasUntwistAbsorption`), the SOLE remaining leg of `fxBrauer_hasCrossingOnlyStraightening`
(`Brauer/WiringDescStandardForm.lean`) is the CANONICAL reduced word `canonicalReducedWord` plus its braid-move
INSERTION induction: inserting one adjacent transposition `s_p` into the canonical word of a permutation, driven by
the free Coxeter moves above, reduces to the canonical word of the swapped permutation.  This is the standard
Matsumoto/Tits word problem for `S_n`; its faithful zero-axiom structural-fuel formalization is the sibling
`ArcCupSortComplete` (`pureCupSpine_sort`).  For the MASTER `fxBrauer_hasBrauerCompleteness` the crossing block must
additionally connect to the diagram invariant via the general readback
`brauerDiagramOf n (crossingWord w) = permutationDiagram n (permuteOfCrossingWord n w)` (SMOKES-only) and the whole
diagram factor into the Lehrer–Zhang regular form (caps ∘ permutation ∘ cups, Lemma 2.13, no shipped pattern).
Lehrer–Zhang Thm 2.6 guarantees NO relation 8 — this is a route/measure gap, not an obstruction.  `= false`. -/
def fxBrauer_hasCrossingStraighteningInsertionResidual : Bool := false

end FX1Poly.Polygraph
