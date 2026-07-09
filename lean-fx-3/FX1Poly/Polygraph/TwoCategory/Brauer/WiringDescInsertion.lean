import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardForm
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStraightening

/-! # WP-BRAUER-4 r5 — the CROSSING-ONLY word problem: canonical reduced word + the conditional fold

The r4 straightening file (`Brauer/WiringDescStraightening.lean`) shipped the three FREE Coxeter moves over the
seven-relation over-approximation `BrauerConvFree7` — R2 cancel (`crossingCancelFree`), R3 braid
(`crossingBraidFree`), distant commute (`crossingCommuteFree`) — each unconditional and composable in arbitrary
prefix AND suffix context (the "suffix congruence is free" realization).  Those are exactly the generators
Matsumoto's / Tits' word problem for `S_n` consumes.  This file assembles the STRAIGHTENING LAYER on top of them and
reduces the whole crossing-only word problem to ONE explicit residual — the general insertion step — which it then
witnesses in every one of its three modes (cancel / extend / braid).

## What is landed (all closed, zero-axiom)

  * **The homomorphism helpers** — `crossingWord_append` (the crossing-word map is a monoid homomorphism from
    position lists to `BrauerAtom` words) and `permuteOfCrossingWord_snoc` (appending one position applies one
    adjacent swap to the realized permutation, via the local `foldlSwapSnoc`).
  * **The canonical reduced word** `canonicalCrossingWord` — the reverse of the BUBBLE-SORT word `bubbleWord`
    (record the leftmost-descent transposition, apply it, recurse; fuel = `inversionCount`, the Lehmer measure that
    strictly drops per R2 cancellation, unlike word-length which the R3 braid preserves).  Reversing the sort-word
    turns "sort `perm` to the identity" into "build `perm` from the identity", so `canonicalCrossingWord perm` is a
    genuine reduced word FOR `perm` (`permuteOfCrossingWord n (canonicalCrossingWord perm) = perm`, witnessed
    concretely by `canonical_reducedWord_smoke_*`).
  * **The identity base** `canonicalCrossingWord_range` — the canonical word of the identity permutation
    `List.range n` is empty (via `isAscendingFrom_range` -> `isAscendingFrom_isIdentity` ->
    `bubbleWordFueled_identity`).  This is the base of the outer fold.
  * **The OUTER FOLD, conditional on the insertion step** — `crossingOnly_straightens_ofInsertionStep`: GIVEN the
    general insertion step, EVERY crossing word `BrauerConvFree7`-reduces to the canonical word of its permutation
    (peel the last letter, IH + free `whiskerRight`, then the insertion step).  Hence
    `crossingWords_equalPerm_conv_ofInsertionStep`: two crossing words with equal permutation are convertible — the
    symmetric-group word problem, reduced to the single residual.

## The residual — the GENERAL insertion step (honestly `false`, the exact case named)

The sole remaining leg is the general `crossingInsertionStep`:
`crossingWord (canonicalCrossingWord perm ++ [position]) ~ crossingWord (canonicalCrossingWord (applyAdjacentSwap perm position))`
for ALL `perm`, `position`.  Both sides have the SAME permutation (`applyAdjacentSwap perm position`, since
`canonicalCrossingWord perm` builds `perm`), so it is a genuine (true) special case of the word problem, provable in
principle by the bubble-insertion induction (Björner–Brenti, *Combinatorics of Coxeter Groups*, Thm 3.3.1; Tits'
word property).  Its three modes are each WITNESSED here on concrete inputs:

  * **cancel** (`crossingInsertionStep_cancel_smoke`) — the inserted letter meets its inverse at the tail; R2
    (`crossingCancelFree`) drops `inversionCount`;
  * **extend** (`crossingInsertionStep_extend_smoke`) — appending the letter STAYS canonical; reflexivity;
  * **braid** (`crossingInsertionStep_braid_smoke`) — the inserted letter braids past the trailing canonical pair;
    R3 (`crossingBraidFree`).

The GENERAL braid mode — the inserted letter bubbling LEFTWARD through a canonical prefix of arbitrary length via a
CHAIN of braid / commute moves while the "still canonical" invariant is threaded (fuel = lexicographic
`(inversionCount perm, insertion position)`) — is the standing jam, the `locateAux`-magnitude induction whose
faithful zero-axiom mirror is the 1300-line sibling `pureCupSpine_sort`.  That single universally-quantified
statement is the exact residual; the master markers `fxBrauer_hasCrossingOnlyStraightening`
(`Brauer/WiringDescStandardForm.lean`) and `fxBrauer_hasCrossingStraighteningInsertionResidual`
(`Brauer/WiringDescStraightening.lean`) STAY `false` because of it, not because of any obstruction (Lehrer–Zhang
Thm 2.6(2) guarantees NO relation 8; the seven relations DO present the category).

Raw Lean 4 + Init; structural recursion (fuel = word length for the fold, `inversionCount` for the bubble word),
no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.  Per-declaration `#assert_no_axioms` in the audit
twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local propext-free structural helpers -/

/-- `Nat.beq value value = true` — structural, avoids the `propext`-tainted `Nat.beq_refl`. -/
private theorem natBeqRefl : (value : Nat) → Nat.beq value value = true
  | 0 => rfl
  | value + 1 => natBeqRefl value

/-- Reflect a true `Nat.beq` back to a propositional equality — structural, `propext`-free. -/
private theorem natEqOfBeq : (leftValue rightValue : Nat) → Nat.beq leftValue rightValue = true →
    leftValue = rightValue
  | 0, 0, _ => rfl
  | 0, _ + 1, beqTrue => Bool.noConfusion beqTrue
  | _ + 1, 0, beqTrue => Bool.noConfusion beqTrue
  | leftValue + 1, rightValue + 1, beqTrue =>
      congrArg Nat.succ (natEqOfBeq leftValue rightValue beqTrue)

/-- Left projection of a true boolean conjunction — full-enum `Bool` match, `propext`-free. -/
private theorem boolAndTrueLeft : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true →
    leftFlag = true
  | true, _, _ => rfl
  | false, _, conj => Bool.noConfusion conj

/-- Right projection of a true boolean conjunction. -/
private theorem boolAndTrueRight : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true →
    rightFlag = true
  | true, _, conj => conj
  | false, _, conj => Bool.noConfusion conj

/-- Collapse a two-branch `Bool` match whose scrutinee is known to be `false` — structural on the scrutinee via
`Bool.casesOn`, so no match-motive `propext` is incurred (unlike `rw`/`cases h :` on the discriminant). -/
private theorem condFalse {alpha : Type _} (thenValue elseValue : alpha) :
    (scrutinee : Bool) → scrutinee = false →
    (match scrutinee with | true => thenValue | false => elseValue) = elseValue
  | false, _ => rfl
  | true, scrutineeFalse => Bool.noConfusion scrutineeFalse

/-- `Nat.ble (value + 2) value = false` — the strict-below round-trip, structural on `value`. -/
private theorem natBleSelfAddTwo_false : (value : Nat) → Nat.ble (value + 2) value = false
  | 0 => rfl
  | value + 1 => natBleSelfAddTwo_false value

/-- `Nat.blt (value + 1) value = false` — `value + 1` is not strictly below `value`
(`Nat.blt a b = Nat.ble (a + 1) b`). -/
private theorem natBltSuccSelf_false (value : Nat) : Nat.blt (value + 1) value = false :=
  natBleSelfAddTwo_false value

/-- Every list is empty or has a distinguished last element — structural, so the peel-last fold stays
`propext`-free (`List.reverse_reverse` leaks `propext`). -/
private theorem listNilOrSnoc {carrier : Type _} :
    (list : List carrier) → list = [] ∨ ∃ prefixList lastElement, list = prefixList ++ [lastElement]
  | [] => Or.inl rfl
  | headElement :: restList =>
      match listNilOrSnoc restList with
      | Or.inl restNil => Or.inr ⟨[], headElement, by subst restNil; rfl⟩
      | Or.inr ⟨prefixList, lastElement, restSnoc⟩ =>
          Or.inr ⟨headElement :: prefixList, lastElement, by subst restSnoc; rfl⟩

/-- `(prefixList ++ [lastElement]).length = prefixList.length + 1` — structural, general carrier. -/
private theorem lengthSnoc {carrier : Type _} :
    (prefixList : List carrier) → (lastElement : carrier) →
    (prefixList ++ [lastElement]).length = prefixList.length + 1
  | [], _ => rfl
  | _ :: restList, lastElement => congrArg Nat.succ (lengthSnoc restList lastElement)

/-! ## Homomorphism helpers — the crossing-word map and the realized permutation -/

/-- ★ **The crossing-word map is a monoid homomorphism** — `crossingWord` splits over concatenation of the
position lists.  Structural on the left positions. -/
theorem crossingWord_append :
    (leftPositions rightPositions : List Nat) →
    crossingWord (leftPositions ++ rightPositions)
      = crossingWord leftPositions ++ crossingWord rightPositions
  | [], _ => rfl
  | position :: rest, rightPositions =>
      congrArg (crossingAt position :: ·) (crossingWord_append rest rightPositions)

/-- Folding adjacent swaps over a snoc applies the last swap outermost — the local `List.foldl_append`
specialisation (Init's leaks `propext`).  Structural on the left positions. -/
theorem foldlSwapSnoc :
    (positions : List Nat) → (basePerm : List Nat) → (position : Nat) →
    (positions ++ [position]).foldl applyAdjacentSwap basePerm
      = applyAdjacentSwap (positions.foldl applyAdjacentSwap basePerm) position
  | [], _, _ => rfl
  | head :: rest, basePerm, position =>
      foldlSwapSnoc rest (applyAdjacentSwap basePerm head) position

/-- ★ **Appending one position applies one adjacent swap to the realized permutation.**  The snoc law for
`permuteOfCrossingWord`, driving the peel-last outer fold. -/
theorem permuteOfCrossingWord_snoc (bottomCount : Nat) (positions : List Nat) (position : Nat) :
    permuteOfCrossingWord bottomCount (positions ++ [position])
      = applyAdjacentSwap (permuteOfCrossingWord bottomCount positions) position :=
  foldlSwapSnoc positions (List.range bottomCount) position

/-! ## The canonical reduced word (Lehmer / decreasing-staircase form) -/

/-- Is this one-line permutation already the identity (strictly increasing, no adjacent descent)?  Structural on
the list, `Nat.blt` + full-enum `Bool` match, `propext`-free. -/
def isIdentityPerm : List Nat → Bool
  | [] => true
  | _ :: [] => true
  | first :: second :: rest =>
      match Nat.blt second first with
      | true => false
      | false => isIdentityPerm (second :: rest)

/-- The position of the leftmost adjacent descent (`0` when already sorted — never consulted in that case). -/
def leftmostDescent : List Nat → Nat
  | [] => 0
  | _ :: [] => 0
  | first :: second :: rest =>
      match Nat.blt second first with
      | true => 0
      | false => leftmostDescent (second :: rest) + 1

/-- How many entries of the list are strictly below `value`. -/
def countEntriesBelow (value : Nat) : List Nat → Nat
  | [] => 0
  | head :: rest =>
      (match Nat.blt head value with | true => 1 | false => 0) + countEntriesBelow value rest

/-- ★ **The inversion count** — the Lehmer length `ell(perm)`, the fuel of the bubble word (strictly drops per R2
cancellation; the R3 braid preserves it, which is why word-length is the WRONG measure). -/
def inversionCount : List Nat → Nat
  | [] => 0
  | head :: rest => countEntriesBelow head rest + inversionCount rest

/-- The bubble-sort word, fuel-bounded: record the leftmost-descent transposition, apply it, recurse.  Structural
on the fuel (`inversionCount perm` at the top level). -/
def bubbleWordFueled : Nat → List Nat → List Nat
  | 0, _ => []
  | fuel + 1, perm =>
      match isIdentityPerm perm with
      | true => []
      | false =>
          leftmostDescent perm :: bubbleWordFueled fuel (applyAdjacentSwap perm (leftmostDescent perm))

/-- The bubble-sort word: the sequence of adjacent transpositions that sorts `perm` to the identity. -/
def bubbleWord (perm : List Nat) : List Nat := bubbleWordFueled (inversionCount perm) perm

/-- ★ **The canonical reduced word of a permutation** — the REVERSE of the bubble-sort word.  Reversing turns
"sort `perm` to the identity" into "build `perm` from the identity", so this is a genuine reduced word FOR `perm`
(`permuteOfCrossingWord n (canonicalCrossingWord perm) = perm`, witnessed by `canonical_reducedWord_smoke_*`). -/
def canonicalCrossingWord (perm : List Nat) : List Nat := (bubbleWord perm).reverse

/-! ## The identity base — the canonical word of the identity permutation is empty -/

/-- Is this list the ascending run `[start, start+1, start+2, ...]`?  Structural, `Nat.beq`-based. -/
def isAscendingFrom : Nat → List Nat → Bool
  | _, [] => true
  | start, head :: rest => Nat.beq head start && isAscendingFrom (start + 1) rest

/-- An ascending run has no adjacent descent, hence is an identity permutation.  Structural on the list. -/
theorem isAscendingFrom_isIdentity : (start : Nat) → (xs : List Nat) →
    isAscendingFrom start xs = true → isIdentityPerm xs = true
  | _, [], _ => rfl
  | _, _ :: [], _ => rfl
  | start, first :: second :: rest, ascending => by
      have firstBeq : Nat.beq first start = true := boolAndTrueLeft _ _ ascending
      have tailAscending : isAscendingFrom (start + 1) (second :: rest) = true :=
        boolAndTrueRight _ _ ascending
      have secondBeq : Nat.beq second (start + 1) = true := boolAndTrueLeft _ _ tailAscending
      have firstEq : first = start := natEqOfBeq first start firstBeq
      have secondEq : second = start + 1 := natEqOfBeq second (start + 1) secondBeq
      -- keep the recursion on the literal subterm `second :: rest`; `subst` would obscure the structural
      -- decrease and force `WellFounded.fix` (propext / Quot.sound).
      have noDescent : Nat.blt second first = false := by
        rw [firstEq, secondEq]; exact natBltSuccSelf_false start
      have reduce : isIdentityPerm (first :: second :: rest) = isIdentityPerm (second :: rest) :=
        condFalse false (isIdentityPerm (second :: rest)) (Nat.blt second first) noDescent
      exact reduce.trans (isAscendingFrom_isIdentity (start + 1) (second :: rest) tailAscending)

/-- Prepending the descending prefix of `range.loop` keeps the list ascending from `0`.  Structural on the count. -/
theorem rangeLoopAscending : (count : Nat) → (accumulated : List Nat) →
    isAscendingFrom count accumulated = true →
    isAscendingFrom 0 (List.range.loop count accumulated) = true
  | 0, _, ascending => ascending
  | count + 1, accumulated, ascending => by
      have step : isAscendingFrom count (count :: accumulated) = true := by
        show (Nat.beq count count && isAscendingFrom (count + 1) accumulated) = true
        rw [natBeqRefl count]
        exact ascending
      exact rangeLoopAscending count (count :: accumulated) step

/-- `List.range count` is the ascending run from `0`. -/
theorem isAscendingFrom_range (count : Nat) : isAscendingFrom 0 (List.range count) = true :=
  rangeLoopAscending count [] rfl

/-- Once the permutation is the identity, the bubble word is empty for ANY fuel. -/
theorem bubbleWordFueled_identity : (fuel : Nat) → (perm : List Nat) →
    isIdentityPerm perm = true → bubbleWordFueled fuel perm = []
  | 0, _, _ => rfl
  | _ + 1, perm, isIdentity => by
      dsimp only [bubbleWordFueled]
      rw [isIdentity]

/-- ★ **The identity base of the fold.**  The canonical word of the identity permutation `List.range count` is the
empty word — its inversion count is `0`, so the bubble word (hence its reverse) is empty. -/
theorem canonicalCrossingWord_range (count : Nat) :
    canonicalCrossingWord (List.range count) = [] := by
  have isIdentity : isIdentityPerm (List.range count) = true :=
    isAscendingFrom_isIdentity 0 (List.range count) (isAscendingFrom_range count)
  have bubbleNil : bubbleWord (List.range count) = [] :=
    bubbleWordFueled_identity (inversionCount (List.range count)) (List.range count) isIdentity
  show (bubbleWord (List.range count)).reverse = []
  exact congrArg List.reverse bubbleNil

/-! ## The OUTER FOLD — conditional on the general insertion step

Peel the LAST letter of the word: the tail-shortened word straightens by the induction hypothesis, the trailing
letter rides along by the FREE `whiskerRight`, and the general insertion step re-canonicalises the result.  Fuel =
word length (structural), base = the identity `canonicalCrossingWord_range`. -/

/-- The fold, fuel-indexed by word length so the peel-last recursion is structural (`WellFounded.fix` banned). -/
theorem crossingOnly_straightensFueled (bottomCount : Nat)
    (insertionStep : ∀ (perm : List Nat) (position : Nat),
      BrauerConvFree7 (crossingWord (canonicalCrossingWord perm ++ [position]))
        (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm position)))) :
    (fuel : Nat) → (word : List Nat) → word.length = fuel →
    BrauerConvFree7 (crossingWord word)
      (crossingWord (canonicalCrossingWord (permuteOfCrossingWord bottomCount word)))
  | 0, [], _ => by
      show BrauerConvFree7 [] (crossingWord (canonicalCrossingWord (List.range bottomCount)))
      rw [canonicalCrossingWord_range bottomCount]
      exact BrauerConvFree7.ofFree (BrauerConvFree.refl [])
  | 0, _ :: _, lengthEq => Nat.noConfusion lengthEq
  | fuel + 1, word, lengthEq => by
      cases listNilOrSnoc word with
      | inl wordNil => subst wordNil; exact Nat.noConfusion lengthEq
      | inr wordSnoc =>
          obtain ⟨prefixPositions, lastPosition, wordEq⟩ := wordSnoc
          subst wordEq
          rw [lengthSnoc prefixPositions lastPosition] at lengthEq
          have prefixLengthEq : prefixPositions.length = fuel := Nat.succ.inj lengthEq
          have straightenedPrefix :=
            crossingOnly_straightensFueled bottomCount insertionStep fuel prefixPositions prefixLengthEq
          rw [permuteOfCrossingWord_snoc bottomCount prefixPositions lastPosition]
          refine BrauerConvFree7.trans ?_
            (insertionStep (permuteOfCrossingWord bottomCount prefixPositions) lastPosition)
          rw [crossingWord_append prefixPositions [lastPosition],
            crossingWord_append (canonicalCrossingWord (permuteOfCrossingWord bottomCount prefixPositions))
              [lastPosition]]
          exact BrauerConvFree7.whiskerRight [crossingAt lastPosition] straightenedPrefix

/-- ★ **Every crossing word straightens to the canonical word of its permutation — CONDITIONAL on the general
insertion step.**  The outer fold, un-fueled.  This is the reduction of the entire crossing-only word problem to the
single residual `insertionStep`. -/
theorem crossingOnly_straightens_ofInsertionStep (bottomCount : Nat)
    (insertionStep : ∀ (perm : List Nat) (position : Nat),
      BrauerConvFree7 (crossingWord (canonicalCrossingWord perm ++ [position]))
        (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm position))))
    (word : List Nat) :
    BrauerConvFree7 (crossingWord word)
      (crossingWord (canonicalCrossingWord (permuteOfCrossingWord bottomCount word))) :=
  crossingOnly_straightensFueled bottomCount insertionStep word.length word rfl

/-- ★★ **The symmetric-group WORD PROBLEM inside the Brauer presentation — CONDITIONAL on the insertion step.**
Two crossing words with EQUAL realized permutation are `BrauerConvFree7`-convertible: both straighten to the
canonical word of that common permutation.  This is the exact statement Matsumoto's theorem provides for `S_n`,
realized here inside the seven-relation Brauer presentation, modulo the single named residual. -/
theorem crossingWords_equalPerm_conv_ofInsertionStep (bottomCount : Nat)
    (insertionStep : ∀ (perm : List Nat) (position : Nat),
      BrauerConvFree7 (crossingWord (canonicalCrossingWord perm ++ [position]))
        (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm position))))
    (wordLeft wordRight : List Nat)
    (permEq : permuteOfCrossingWord bottomCount wordLeft = permuteOfCrossingWord bottomCount wordRight) :
    BrauerConvFree7 (crossingWord wordLeft) (crossingWord wordRight) := by
  have straightenedRight :=
    crossingOnly_straightens_ofInsertionStep bottomCount insertionStep wordRight
  rw [← permEq] at straightenedRight
  exact BrauerConvFree7.trans
    (crossingOnly_straightens_ofInsertionStep bottomCount insertionStep wordLeft)
    (BrauerConvFree7.symm straightenedRight)

/-! ## Non-vacuity — the canonical word is a genuine reduced word; the residual's three modes are witnessed -/

/-- The canonical word of the transposition `[1, 0]` realizes it: `permuteOf 2 (canonical [1,0]) = [1,0]`. -/
theorem canonical_reducedWord_smoke_transposition :
    permuteOfCrossingWord 2 (canonicalCrossingWord [1, 0]) = [1, 0] := by decide

/-- The canonical word of the 3-cycle `[1, 2, 0]` realizes it. -/
theorem canonical_reducedWord_smoke_threeCycle :
    permuteOfCrossingWord 3 (canonicalCrossingWord [1, 2, 0]) = [1, 2, 0] := by decide

/-- The canonical word of the reversal `[2, 1, 0]` realizes it — the maximal (Yang–Baxter) case. -/
theorem canonical_reducedWord_smoke_reversal :
    permuteOfCrossingWord 3 (canonicalCrossingWord [2, 1, 0]) = [2, 1, 0] := by decide

/-- ★ **Insertion step, CANCEL mode.**  Inserting `s_0` into the canonical word of `[1, 0]` meets its own inverse:
the residual holds via R2 (`crossingCancelFree`), and the inversion count drops `1 -> 0`. -/
theorem crossingInsertionStep_cancel_smoke :
    BrauerConvFree7 (crossingWord (canonicalCrossingWord [1, 0] ++ [0]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap [1, 0] 0))) := by
  show BrauerConvFree7 [crossingAt 0, crossingAt 0] []
  exact crossingCancelFree 0

/-- ★ **Insertion step, EXTEND mode.**  Inserting `s_0` into the canonical word of `[1, 2, 0]` STAYS canonical
(`[0,1] ++ [0] = [0,1,0]` is already the canonical word of the swapped permutation `[2,1,0]`): the residual holds
by reflexivity. -/
theorem crossingInsertionStep_extend_smoke :
    BrauerConvFree7 (crossingWord (canonicalCrossingWord [1, 2, 0] ++ [0]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap [1, 2, 0] 0))) := by
  show BrauerConvFree7 (crossingWord [0, 1, 0]) (crossingWord [0, 1, 0])
  exact BrauerConvFree7.ofFree (BrauerConvFree.refl (crossingWord [0, 1, 0]))

/-- ★ **Insertion step, BRAID mode.**  Inserting `s_1` into the canonical word of `[2, 0, 1]` (`= [1, 0]`) gives
`[1, 0, 1]`, which braids to the canonical word `[0, 1, 0]` of the swapped permutation `[2, 1, 0]`: the residual
holds via R3 (`crossingBraidFree`).  This is the smallest genuine braid instance of the standing residual. -/
theorem crossingInsertionStep_braid_smoke :
    BrauerConvFree7 (crossingWord (canonicalCrossingWord [2, 0, 1] ++ [1]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap [2, 0, 1] 1))) := by
  show BrauerConvFree7 (crossingWord [1, 0, 1]) (crossingWord [0, 1, 0])
  exact BrauerConvFree7.symm (crossingBraidFree 0)

/-- ★ **The word-problem claim, witnessed directly on the braid pair.**  `[0,1,0]` and `[1,0,1]` have the same
permutation (`[2,1,0]`) and ARE convertible — the R3 witness, decidably equal permutations.  This is the canonical
non-trivial instance of the (conditional) `crossingWords_equalPerm_conv_ofInsertionStep`. -/
theorem crossingWords_equalPerm_conv_braidPair :
    permuteOfCrossingWord 3 [0, 1, 0] = permuteOfCrossingWord 3 [1, 0, 1]
      ∧ BrauerConvFree7 (crossingWord [0, 1, 0]) (crossingWord [1, 0, 1]) :=
  ⟨by decide, crossingBraidFree 0⟩

/-- ★ **The word-problem claim, witnessed directly on the R2 pair.**  `[0,0]` and `[]` have the same permutation
(the identity `[0,1]`) and ARE convertible — the R2 collapse. -/
theorem crossingWords_equalPerm_conv_r2Pair :
    permuteOfCrossingWord 2 [0, 0] = permuteOfCrossingWord 2 []
      ∧ BrauerConvFree7 (crossingWord [0, 0]) (crossingWord []) :=
  ⟨by decide, crossingCancelFree 0⟩

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the CANONICAL CROSSING-WORD layer is SHIPPED.**  `canonicalCrossingWord` (the reverse of
the `inversionCount`-fuelled bubble word `bubbleWord`) is a genuine reduced word for its permutation
(`canonical_reducedWord_smoke_{transposition,threeCycle,reversal}` verify
`permuteOfCrossingWord n (canonicalCrossingWord perm) = perm` on the transposition, a 3-cycle, and the reversal),
with the homomorphism helpers `crossingWord_append` / `permuteOfCrossingWord_snoc` and the identity base
`canonicalCrossingWord_range` (`= []`) closed zero-axiom.  `= true`. -/
def fxBrauer_hasCanonicalCrossingWordLayer : Bool := true

/-- ★ **Honesty marker — the crossing-only WORD PROBLEM is REDUCED to the single insertion residual.**
`crossingOnly_straightens_ofInsertionStep` proves, CONDITIONAL on the general insertion step, that every crossing
word `BrauerConvFree7`-reduces to the canonical word of its permutation (peel-last fold, IH + free `whiskerRight` +
the insertion step, base = `canonicalCrossingWord_range`), whence
`crossingWords_equalPerm_conv_ofInsertionStep`: equal permutation implies convertibility — the symmetric-group word
problem realized inside the seven-relation Brauer presentation.  The reduction is complete and machine-checked; the
sole hypothesis is the general insertion step.  Non-vacuous: `crossingWords_equalPerm_conv_{braidPair,r2Pair}`
witness the conclusion directly on the two canonical hard pairs.  `= true`. -/
def fxBrauer_hasCrossingWordProblemConditionalReduction : Bool := true

/-- **Honesty marker — the GENERAL insertion step stays `false`; the exact residual case is named.**  The sole
remaining leg is `crossingInsertionStep` for ALL `perm`, `position`:
`crossingWord (canonicalCrossingWord perm ++ [position]) ~ crossingWord (canonicalCrossingWord (applyAdjacentSwap perm position))`.
Both sides have the same permutation (`applyAdjacentSwap perm position`, since `canonicalCrossingWord perm` builds
`perm`), so it is a TRUE special case of the word problem (Björner–Brenti Thm 3.3.1 / Tits).  Its three modes are
each witnessed on concrete inputs — `crossingInsertionStep_cancel_smoke` (R2, `inversionCount` drops),
`crossingInsertionStep_extend_smoke` (append stays canonical, reflexivity), `crossingInsertionStep_braid_smoke`
(R3).  The exact standing jam is the GENERAL braid mode: the inserted letter bubbling LEFTWARD through a canonical
prefix of ARBITRARY length via a chain of braid / commute moves while the "still canonical" invariant is threaded,
under the lexicographic fuel `(inversionCount perm, insertion position)` — the `locateAux`-magnitude induction whose
faithful zero-axiom mirror is the 1300-line sibling `pureCupSpine_sort`.  That single universally-quantified
statement is the residual; `fxBrauer_hasCrossingOnlyStraightening` (`Brauer/WiringDescStandardForm.lean`) and
`fxBrauer_hasCrossingStraighteningInsertionResidual` (`Brauer/WiringDescStraightening.lean`) stay `false` because of
it — a route/measure gap, not an obstruction (Lehrer–Zhang Thm 2.6(2): the seven relations DO present the
category).  `= false`. -/
def fxBrauer_hasCrossingInsertionStepGeneralResidual : Bool := false

end FX1Poly.Polygraph
