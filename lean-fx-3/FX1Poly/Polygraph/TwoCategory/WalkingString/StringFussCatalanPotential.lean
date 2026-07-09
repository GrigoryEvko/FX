import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanStaircase

/-! # WalkingString — the COMMUTE potential `p2` + the lex-priority check (FC-3b, piece B)

FC-3 (`StringFussCatalanStaircase`) read off the termination measure `lex(generatorCount, size, commutePotential)` and
machine-checked every mode's effect on the two SHIPPED structural weights: CANCEL drops `generatorCount` by 2, EXTEND
holds `generatorCount` and drops `size` by 2, and COMMUTE / INTERLEAVE hold BOTH weights.  It left `commutePotential`
UNDEFINED, walling it as "a positional distance to innermost-fireable position … needing a redex LOCATOR".  The FC-3b
recon (grounded in Delpeuch–Vicary arXiv:1804.07832 Lemma 2.8 / Theorem 2.14, Thiebaut arXiv:2508.19360 Lemma 2.17,
and the classical bubble-sort inversion count) settled the choice: **`commutePotential = p2`, the number of adjacent
out-of-order pairs (bubble-sort inversions) of the colour-position word against the canonical peel order.**  This file
ships that definition, its core combinatorial descent, and the lex-priority check.

## The choice (recon verdict) — why `p2` over `p1` (positional distance) / `p3` (interleave depth)

`p3` is REFUTED: it is invariant under same-colour COMMUTE, so a pure-COMMUTE chain has no descent.  `p1` and `p2`
both strictly drop, but `p2` wins: it drops by EXACTLY 1 per adjacent transposition (matching the one-step-move
granularity, clean `+1` lex bookkeeping), needs only the pairwise canonical-ORDER comparator (computable from the
spine, no materialized canonical position), and with NO braid ascent (design lock #4) inversions = symmetric-group
length = min adjacent swaps to canonical (the tight Squier/Newman measure).  Delpeuch–Vicary's monotone-trajectory
bound (each ordered pair of non-final vertices exchanges AT MOST ONCE, Lemma 2.8 ⟹ the O(n²) Theorem 2.14) IS this
inversion count; Thiebaut's Temperley–Lieb convergence orients the relations so every rule strictly decreases a
lexicographic order on the generator word — length-reducing rules (CANCEL / EXTEND) dominate, commutation rules
(COMMUTE / INTERLEAVE) order the descending blocks — exactly `lex(generatorCount, size, p2)`.

## What this ships

  * `countLess` / `countInversions` — the bubble-sort inversion count of a `Nat` colour-key word.
  * ★ `countInversions_swapAdjacent_dropsOne` — the CORE: swapping two ADJACENT out-of-order keys drops the inversion
    count by EXACTLY 1 (the per-step descent of COMMUTE / INTERLEAVE, item-2/item-3 combinatorial content).
  * `stringLexLt3` + the three descent lemmas (`_of_fst` / `_of_snd` / `_of_thd`) — the LEX-PRIORITY CHECK: coord-1
    drop dominates (CANCEL), coord-1-tie + coord-2 drop (EXTEND), coords-tie + coord-3 drop (COMMUTE / INTERLEAVE).
  * the term-level wiring: CANCEL (`stringLexDescent_cancelF`) and EXTEND (`stringLexDescent_extend`) descend the lex
    tuple via the SHIPPED weight lemmas; COMMUTE / INTERLEAVE (`stringLexDescent_commute`) descend the third
    coordinate via the swap-drops-one fact.

## The honest wall (FC-3c)

The term-level COMMUTE / INTERLEAVE descent is stated over the colour-word SWAP (`b :: a :: rest ↝ a :: b :: rest`),
NOT bound to the actual `whiskerExchange` move — because binding "each `whiskerExchange` = a specific adjacent spine
transposition" is the redex-locating DRIVER (`fireSnakeAt` / `commuteAt`), the FC-3c assembly the Staircase marker
walls.  So this file delivers the measure + its descent + the lex check; the full multi-mode straightening FOLD and
the moves-as-transpositions binding are NOT claimed (`fxString_hasStaircaseDriver` stays `false`).

Raw Lean 4 + Init; `countInversions` is structural list recursion, the swap-drop is a boolean-`if` split + `Nat`
add-commutativity, the lex check is `Or`/`And` plumbing.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/
`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The bubble-sort inversion count -/

/-- Count the elements of `keys` strictly BELOW `bound` — the per-head inversion contribution.  Structural list
recursion; the `if head < bound` uses `Nat.decLt`, propext-clean. -/
def countLess (bound : Nat) : List Nat → Nat
  | [] => 0
  | head :: rest => (if head < bound then 1 else 0) + countLess bound rest

/-- ★ The **bubble-sort inversion count** of a colour-key word: the number of pairs `(i, j)` with `i < j` (position)
but `keys[i] > keys[j]` (out of canonical order).  Structural: each head contributes the count of strictly-smaller
keys AFTER it.  With NO braid ascent this equals the symmetric-group length = the minimum number of adjacent swaps to
sort to canonical order — the FC-3b `commutePotential`. -/
def countInversions : List Nat → Nat
  | [] => 0
  | head :: rest => countLess head rest + countInversions rest

/-- ★ The **COMMUTE potential** `p2` of a colour-key word — its bubble-sort inversion count against the canonical peel
order.  The third lexicographic component of the FC-3 staircase measure `lex(generatorCount, size, commutePotential)`;
the redex-locating binding of a spine to its colour-key word is the FC-3c driver. -/
def commutePotential (colourWord : List Nat) : Nat := countInversions colourWord

/-- The inversion count of the empty word is `0`. -/
theorem countInversions_nil : countInversions [] = 0 := rfl

/-- ★★ **An adjacent out-of-order swap drops the inversion count by EXACTLY 1.**  For `b < a`, swapping the adjacent
pair `a :: b` to `b :: a` (sorting it into canonical order) removes precisely the single inversion `(a, b)` and
touches no other pair: `countInversions (a :: b :: rest) = countInversions (b :: a :: rest) + 1`.  This is the
per-step descent COMMUTE / INTERLEAVE fire — the classical bubble-sort fact and Delpeuch–Vicary's "at most once per
pair" bound in one equation. -/
theorem countInversions_swapAdjacent_dropsOne (a b : Nat) (rest : List Nat) (outOfOrder : b < a) :
    countInversions (a :: b :: rest) = countInversions (b :: a :: rest) + 1 := by
  show countLess a (b :: rest) + countInversions (b :: rest)
    = countLess b (a :: rest) + countInversions (a :: rest) + 1
  show (if b < a then 1 else 0) + countLess a rest + (countLess b rest + countInversions rest)
    = (if a < b then 1 else 0) + countLess b rest + (countLess a rest + countInversions rest) + 1
  rw [if_pos outOfOrder, if_neg (fun aLtB => Nat.lt_irrefl a (Nat.lt_trans aLtB outOfOrder)), Nat.zero_add]
  -- 1 + countLess a rest + (countLess b rest + countInversions rest)
  --   = countLess b rest + (countLess a rest + countInversions rest) + 1
  generalize countLess a rest = weightA
  generalize countLess b rest = weightB
  generalize countInversions rest = weightC
  rw [Nat.add_comm (1 + weightA) (weightB + weightC),
    Nat.add_assoc weightB weightC (1 + weightA),
    Nat.add_comm weightC (1 + weightA),
    Nat.add_assoc 1 weightA weightC,
    Nat.add_comm 1 (weightA + weightC),
    ← Nat.add_assoc weightB (weightA + weightC) 1]

/-! ## The lexicographic priority order on the three-weight tuple -/

/-- ★ The **lexicographic order on the three-weight tuple** `(generatorCount, size, commutePotential)`: strictly less
when the first coordinate drops, or ties and the second drops, or both tie and the third drops.  The termination order
the FC-3 staircase measure lives in (the lex product of `ℕ` three times is well-founded — the standard fact; the
per-mode descent below IS the priority check). -/
def stringLexLt3 (fstReduct sndReduct thdReduct fstRedex sndRedex thdRedex : Nat) : Prop :=
  fstReduct < fstRedex
    ∨ (fstReduct = fstRedex
        ∧ (sndReduct < sndRedex ∨ (sndReduct = sndRedex ∧ thdReduct < thdRedex)))

/-- ★ **CANCEL priority.**  A first-coordinate drop (`generatorCount` descends) dominates the lex order regardless of
the other two coordinates. -/
theorem stringLexLt3_of_fst (fstReduct sndReduct thdReduct fstRedex sndRedex thdRedex : Nat)
    (fstDrop : fstReduct < fstRedex) :
    stringLexLt3 fstReduct sndReduct thdReduct fstRedex sndRedex thdRedex :=
  Or.inl fstDrop

/-- ★ **EXTEND priority.**  A first-coordinate TIE (`generatorCount` neutral) plus a second-coordinate drop (`size`
descends) descends the lex order regardless of the third coordinate. -/
theorem stringLexLt3_of_snd (fstReduct sndReduct thdReduct fstRedex sndRedex thdRedex : Nat)
    (fstTie : fstReduct = fstRedex) (sndDrop : sndReduct < sndRedex) :
    stringLexLt3 fstReduct sndReduct thdReduct fstRedex sndRedex thdRedex :=
  Or.inr ⟨fstTie, Or.inl sndDrop⟩

/-- ★ **COMMUTE / INTERLEAVE priority.**  Both first (`generatorCount`) and second (`size`) coordinates TIE and the
third (`commutePotential`) drops — the free-interchange moves' strict descent lives entirely in `p2`. -/
theorem stringLexLt3_of_thd (fstReduct sndReduct thdReduct fstRedex sndRedex thdRedex : Nat)
    (fstTie : fstReduct = fstRedex) (sndTie : sndReduct = sndRedex) (thdDrop : thdReduct < thdRedex) :
    stringLexLt3 fstReduct sndReduct thdReduct fstRedex sndRedex thdRedex :=
  Or.inr ⟨fstTie, Or.inr ⟨sndTie, thdDrop⟩⟩

/-! ## Term-level wiring — the SHIPPED weight lemmas feed the lex check (CANCEL / EXTEND) -/

/-- A private `n < n + 2` (used for the CANCEL / EXTEND coordinate drops). -/
private theorem natLtAddTwo (value : Nat) : value < value + 2 :=
  Nat.lt_succ_of_lt (Nat.lt_succ_self value)

/-- ★ **CANCEL descends the lex tuple** (colour-1 `F`).  The CANCEL reduct `w` sits strictly below the redex
`vcomp w stringSnakeF` in `lex(generatorCount, size, commutePotential)`: the first coordinate drops by 2
(`stringCancelSnakeF_dropsTwo`), dominating — the other two coordinates (`thdReduct`, `thdRedex`) are free. -/
theorem stringLexDescent_cancelF
    {sourcePath : ModalityPath adjointTripleGraph AdjointTripleMode.base AdjointTripleMode.tip}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath
      (singletonModalityPath AdjointTripleModality.left)) (thdReduct thdRedex : Nat) :
    stringLexLt3 w.generatorCount w.size thdReduct
      (RawTwoCellExpr.vcomp w stringSnakeF).generatorCount (RawTwoCellExpr.vcomp w stringSnakeF).size thdRedex :=
  stringLexLt3_of_fst _ _ _ _ _ _
    (by rw [stringCancelSnakeF_dropsTwo]; exact natLtAddTwo w.generatorCount)

/-- ★ **EXTEND descends the lex tuple.**  The EXTEND reduct `w` sits strictly below the redex `vcomp w (id path)`: the
first coordinate TIES (`stringExtendByIdentity_generatorCount_neutral`) and the second drops by 2
(`stringExtendByIdentity_size_dropsTwo`) — caught by the second lex component, the third free. -/
theorem stringLexDescent_extend
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) (thdReduct thdRedex : Nat) :
    stringLexLt3 w.generatorCount w.size thdReduct
      (RawTwoCellExpr.vcomp w (RawTwoCellExpr.id (signature := adjointTripleModeSignature) targetPath)).generatorCount
      (RawTwoCellExpr.vcomp w (RawTwoCellExpr.id (signature := adjointTripleModeSignature) targetPath)).size
      thdRedex :=
  stringLexLt3_of_snd _ _ _ _ _ _
    (stringExtendByIdentity_generatorCount_neutral w).symm
    (by rw [stringExtendByIdentity_size_dropsTwo]; exact natLtAddTwo w.size)

/-- ★★ **COMMUTE / INTERLEAVE descend the lex tuple.**  When the two structural weights TIE (the SHIPPED neutrality of
`generatorCount` / `size` under whisker-interchange, `stringWhiskerLeft/Right_*` + `stringCastBoundary_*`, here
represented by equal first/second coordinates `fstWeight` / `sndWeight`), the colour-word SWAP `b :: a :: rest ↝
a :: b :: rest` (an adjacent out-of-order transposition toward canonical order) drops the third coordinate by exactly
1 (`countInversions_swapAdjacent_dropsOne`), descending the lex order.  The binding of the actual `whiskerExchange`
move to this colour-word swap is the FC-3c redex-locating driver. -/
theorem stringLexDescent_commute (fstWeight sndWeight a b : Nat) (rest : List Nat) (outOfOrder : b < a) :
    stringLexLt3 fstWeight sndWeight (commutePotential (b :: a :: rest))
      fstWeight sndWeight (commutePotential (a :: b :: rest)) :=
  stringLexLt3_of_thd _ _ _ _ _ _ rfl rfl
    (by
      show countInversions (b :: a :: rest) < countInversions (a :: b :: rest)
      rw [countInversions_swapAdjacent_dropsOne a b rest outOfOrder]
      exact Nat.lt_succ_self _)

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the COMMUTE potential `p2` is DEFINED and its lex descent is machine-checked.**  `commutePotential
= countInversions`, the bubble-sort inversion count of the colour-key word (the recon's choice: `p3` refuted as
COMMUTE-invariant, `p1` dominated by `p2`'s exact-`+1` granularity and comparator-only computability, grounded in
Delpeuch–Vicary's monotone-trajectory bound and Thiebaut's Temperley–Lieb lex convergence).  The CORE descent
`countInversions_swapAdjacent_dropsOne` proves an adjacent out-of-order swap drops the count by EXACTLY 1, and the
lex-priority check `stringLexLt3` + `_of_fst` / `_of_snd` / `_of_thd` exhibits the four modes strictly descending
`lex(generatorCount, size, commutePotential)`: CANCEL via the first coordinate (`stringLexDescent_cancelF`, feeding the
shipped `stringCancelSnakeF_dropsTwo`), EXTEND via the second (`stringLexDescent_extend`, feeding the shipped
`stringExtendByIdentity_*`), COMMUTE / INTERLEAVE via the third (`stringLexDescent_commute`, feeding the swap-drop).
All UNCONDITIONAL, zero-axiom.  `= true`. -/
def fxString_hasCommutePotential : Bool := true

/-- **OPEN (honest) — the moves-as-spine-transpositions BINDING + the multi-mode FOLD stay FC-3c.**  The term-level
COMMUTE / INTERLEAVE descent (`stringLexDescent_commute`) is stated over the colour-word SWAP, NOT bound to the actual
`whiskerExchange` move: proving "each `whiskerExchange` = a specific adjacent spine transposition of the colour-key
word" is the redex-locating DRIVER (`fireSnakeAt` / `commuteAt`) — the same driver the Staircase marker
`fxString_hasStaircaseDriver` walls.  So this file ships the MEASURE (`commutePotential`), its per-step DESCENT
(`countInversions_swapAdjacent_dropsOne`), and the LEX-PRIORITY CHECK (`stringLexLt3` + the three descent lemmas), but
NOT the full multi-mode straightening fold nor the driver binding.  `fxString_hasStaircaseDriver` STAYS `false`,
honestly, with the measure now DEFINED and its combinatorics proven — the frontier moved from "no `commutePotential`
definition exists" to "the definition + descent are shipped; the driver binding + fold are FC-3c".  `= false`. -/
def fxString_hasStaircaseFoldFromPotential : Bool := false

end FX1Poly.Polygraph
