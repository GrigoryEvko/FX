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

/-! ## The insertion step — CANCEL mode (general), the staircase-snoc identity, and the Lehmer measure drop

This section closes ONE of the three insertion modes — the CANCEL mode — as a GENERAL theorem (all non-identity
`perm`, insert at the leftmost descent), for ARBITRARY `perm : List Nat`, with the reusable structural kit it stands
on: the staircase-snoc identity (`canonicalCrossingWord perm = canonicalCrossingWord (perm · s_d) ++ [d]` for
`d = leftmostDescent perm`) and the Lehmer measure drop (`inversionCount (perm · s_d) + 1 = inversionCount perm`).

WHY only CANCEL closes at this generality: the CANCEL mode inserts at `d = leftmostDescent perm`, which is a genuine
adjacent descent for ANY non-identity list — so the trailing `[d, d]` cancels via R2 with NO permutation-structure
hypothesis.  The other two modes are `perm`-structure sensitive: EXTEND (`position < d`, append stays canonical) and
COMMUTE (`position ≥ d + 2`) both need `perm` to be a genuine permutation (DISTINCT entries) — e.g. the EXTEND
stability `position < leftmostDescent perm → leftmostDescent (applyAdjacentSwap perm position) = position` is FALSE
for lists with repeats (`[1, 1, 0]`).  BRAID (`position = d + 1`) is the Matsumoto inner induction on top of that.
See the honesty marker below for the full residual diagnosis. -/

/-- Collapse a two-branch `Bool` match whose scrutinee is known to be `true` — mirror of `condFalse`, structural on
the scrutinee via `Bool.casesOn`, so no match-motive `propext` is incurred. -/
private theorem condTrue {alpha : Type _} (thenValue elseValue : alpha) :
    (scrutinee : Bool) → scrutinee = true →
    (match scrutinee with | true => thenValue | false => elseValue) = thenValue
  | true, _ => rfl
  | false, scrutineeTrue => Bool.noConfusion scrutineeTrue

/-- `Nat.blt` antisymmetry — `smaller < larger` rules out `larger < smaller`.  Structural on both `Nat`s, full-enum
`Bool` matches, `propext`-free. -/
private theorem natBltAsymm : (leftValue rightValue : Nat) →
    Nat.blt rightValue leftValue = true → Nat.blt leftValue rightValue = false
  | 0, 0, bltTrue => Bool.noConfusion bltTrue
  | 0, _ + 1, bltTrue => Bool.noConfusion bltTrue
  | _ + 1, 0, _ => rfl
  | leftValue + 1, rightValue + 1, bltTrue => natBltAsymm leftValue rightValue bltTrue

/-- Reduce `countEntriesBelow` on a cons whose head IS below the value — the head contributes `1`. -/
private theorem countEntriesBelow_cons_true {value head : Nat} {rest : List Nat}
    (headBelow : Nat.blt head value = true) :
    countEntriesBelow value (head :: rest) = 1 + countEntriesBelow value rest := by
  dsimp only [countEntriesBelow]; rw [headBelow]

/-- Reduce `countEntriesBelow` on a cons whose head is NOT below the value — the head contributes `0`. -/
private theorem countEntriesBelow_cons_false {value head : Nat} {rest : List Nat}
    (headNotBelow : Nat.blt head value = false) :
    countEntriesBelow value (head :: rest) = countEntriesBelow value rest := by
  dsimp only [countEntriesBelow]; rw [headNotBelow]; exact Nat.zero_add _

/-- ★ **`countEntriesBelow` is invariant under an adjacent swap** — an adjacent transposition only reorders two
entries, and `countEntriesBelow value` counts a set, so it is unchanged.  The multiset-invariance leg of the
inversion-count drop.  Structural on the swap's own matcher. -/
theorem countEntriesBelow_applyAdjacentSwap :
    (value : Nat) → (perm : List Nat) → (position : Nat) →
    countEntriesBelow value (applyAdjacentSwap perm position) = countEntriesBelow value perm
  | _, [], _ => rfl
  | _, _ :: [], _ => rfl
  | value, first :: second :: rest, 0 => by
      show (match Nat.blt second value with | true => 1 | false => 0)
            + ((match Nat.blt first value with | true => 1 | false => 0) + countEntriesBelow value rest)
          = (match Nat.blt first value with | true => 1 | false => 0)
            + ((match Nat.blt second value with | true => 1 | false => 0) + countEntriesBelow value rest)
      rw [Nat.add_left_comm]
  | value, first :: second :: rest, position + 1 => by
      show (match Nat.blt first value with | true => 1 | false => 0)
            + countEntriesBelow value (applyAdjacentSwap (second :: rest) position)
          = (match Nat.blt first value with | true => 1 | false => 0)
            + countEntriesBelow value (second :: rest)
      rw [countEntriesBelow_applyAdjacentSwap value (second :: rest) position]

/-- The commutative-monoid identity behind the descent case of the inversion drop:
`(bB + (aA + cC)) + 1 = (1 + aA) + (bB + cC)` — both sides are `1 + aA + bB + cC`. -/
private theorem addReassocDescent (leftCount rightCount tailCount : Nat) :
    (rightCount + (leftCount + tailCount)) + 1 = (1 + leftCount) + (rightCount + tailCount) := by
  rw [Nat.add_comm (rightCount + (leftCount + tailCount)) 1,
    Nat.add_left_comm rightCount leftCount tailCount, Nat.add_assoc]

/-- ★ **The Lehmer inversion count strictly drops by one at the leftmost-descent swap.**  Swapping the leftmost
adjacent descent removes exactly one inversion (the descent pair itself; every other pair is unchanged because the
swap only reorders two adjacent entries, and `countEntriesBelow` is multiset-invariant —
`countEntriesBelow_applyAdjacentSwap`).  This is the strict decrease of the OUTER fuel for the insertion induction:
`inversionCount (perm · s_d) + 1 = inversionCount perm` with `d = leftmostDescent perm`.  Structural on `perm`. -/
theorem inversionCount_ofLeftmostDescentSwap_succ :
    (perm : List Nat) → isIdentityPerm perm = false →
    inversionCount (applyAdjacentSwap perm (leftmostDescent perm)) + 1 = inversionCount perm
  | [], nonIdentity => Bool.noConfusion nonIdentity
  | _ :: [], nonIdentity => Bool.noConfusion nonIdentity
  | first :: second :: rest, nonIdentity =>
      match hDescent : Nat.blt second first with
      | true => by
          have leftmostIsZero : leftmostDescent (first :: second :: rest) = 0 :=
            condTrue 0 (leftmostDescent (second :: rest) + 1) (Nat.blt second first) hDescent
          rw [leftmostIsZero]
          show (countEntriesBelow second (first :: rest) + inversionCount (first :: rest)) + 1
              = countEntriesBelow first (second :: rest) + inversionCount (second :: rest)
          rw [countEntriesBelow_cons_false (natBltAsymm first second hDescent),
            countEntriesBelow_cons_true hDescent]
          show (countEntriesBelow second rest + (countEntriesBelow first rest + inversionCount rest)) + 1
              = (1 + countEntriesBelow first rest) + (countEntriesBelow second rest + inversionCount rest)
          exact addReassocDescent (countEntriesBelow first rest) (countEntriesBelow second rest)
            (inversionCount rest)
      | false => by
          have leftmostIsSucc :
              leftmostDescent (first :: second :: rest) = leftmostDescent (second :: rest) + 1 :=
            condFalse 0 (leftmostDescent (second :: rest) + 1) (Nat.blt second first) hDescent
          rw [leftmostIsSucc]
          have identityReduces : isIdentityPerm (first :: second :: rest) = isIdentityPerm (second :: rest) :=
            condFalse false (isIdentityPerm (second :: rest)) (Nat.blt second first) hDescent
          have tailNonIdentity : isIdentityPerm (second :: rest) = false := identityReduces ▸ nonIdentity
          have tailDrop := inversionCount_ofLeftmostDescentSwap_succ (second :: rest) tailNonIdentity
          show (countEntriesBelow first (applyAdjacentSwap (second :: rest) (leftmostDescent (second :: rest)))
                + inversionCount (applyAdjacentSwap (second :: rest) (leftmostDescent (second :: rest)))) + 1
              = countEntriesBelow first (second :: rest) + inversionCount (second :: rest)
          rw [countEntriesBelow_applyAdjacentSwap first (second :: rest) (leftmostDescent (second :: rest)),
            ← tailDrop, Nat.add_assoc]

/-! ### propext-free `reverse` cons law (Init's `List.reverse_cons` leaks `propext`) -/

/-- Right-associate a snoc through a following append — `(xs ++ [mid]) ++ tail = xs ++ (mid :: tail)`.  Structural
on `xs`, so it avoids the general `List.append_assoc` (which leaks `propext`). -/
private theorem appendSnocAssoc {alpha : Type _} :
    (xs : List alpha) → (mid : alpha) → (tail : List alpha) →
    (xs ++ [mid]) ++ tail = xs ++ (mid :: tail)
  | [], _, _ => rfl
  | headElement :: restList, mid, tail => congrArg (headElement :: ·) (appendSnocAssoc restList mid tail)

/-- `List.reverseAux list acc = List.reverse list ++ acc` — the accumulator floats out as a trailing append.
Structural on `list`, `propext`-free (built on `appendSnocAssoc`, not `List.append_assoc`). -/
private theorem reverseAuxAppend {alpha : Type _} :
    (list : List alpha) → (acc : List alpha) →
    List.reverseAux list acc = List.reverse list ++ acc
  | [], _ => rfl
  | headElement :: tailList, acc => by
      show List.reverseAux tailList (headElement :: acc) = List.reverseAux tailList [headElement] ++ acc
      rw [reverseAuxAppend tailList (headElement :: acc), reverseAuxAppend tailList [headElement]]
      exact (appendSnocAssoc (List.reverse tailList) headElement acc).symm

/-- ★ **`List.reverse (head :: tail) = List.reverse tail ++ [head]`** — the propext-free `reverse_cons` (Init's leaks
`propext`, as does `List.reverse_reverse`), the load-bearing step of the staircase-snoc identity. -/
private theorem reverseConsLocal {alpha : Type _} (headElement : alpha) (tailList : List alpha) :
    List.reverse (headElement :: tailList) = List.reverse tailList ++ [headElement] := by
  show List.reverseAux tailList [headElement] = List.reverse tailList ++ [headElement]
  exact reverseAuxAppend tailList [headElement]

/-- `list ++ [] = list` — cons-only structural copy (Init's `List.append_nil` leaks `propext`). -/
private theorem appendNilLocal {alpha : Type _} : (list : List alpha) → list ++ [] = list
  | [] => rfl
  | headElement :: restList => congrArg (headElement :: ·) (appendNilLocal restList)

/-- ★★ **The staircase-snoc identity.**  For a NON-IDENTITY permutation the canonical crossing word ENDS in the
leftmost descent `d`, and its prefix is the canonical word of the once-bubbled permutation `perm · s_d`:
`canonicalCrossingWord perm = canonicalCrossingWord (applyAdjacentSwap perm d) ++ [d]`.  This is the reverse of the
bubble-word recursion (`bubbleWord perm = d :: bubbleWord (perm · s_d)`), which is legitimate exactly because the
inversion count drops by one (`inversionCount_ofLeftmostDescentSwap_succ`), so the fuel matches.  This is what turns
the peel-last outer fold into an induction on `inversionCount` and is the structural core of the CANCEL mode. -/
theorem canonicalCrossingWord_snoc_leftmostDescent (perm : List Nat)
    (nonIdentity : isIdentityPerm perm = false) :
    canonicalCrossingWord perm
      = canonicalCrossingWord (applyAdjacentSwap perm (leftmostDescent perm)) ++ [leftmostDescent perm] := by
  have inversionSucc : inversionCount perm
      = inversionCount (applyAdjacentSwap perm (leftmostDescent perm)) + 1 :=
    (inversionCount_ofLeftmostDescentSwap_succ perm nonIdentity).symm
  have fueledStep : bubbleWordFueled
        (inversionCount (applyAdjacentSwap perm (leftmostDescent perm)) + 1) perm
      = leftmostDescent perm
        :: bubbleWordFueled (inversionCount (applyAdjacentSwap perm (leftmostDescent perm)))
            (applyAdjacentSwap perm (leftmostDescent perm)) :=
    condFalse [] (leftmostDescent perm
        :: bubbleWordFueled (inversionCount (applyAdjacentSwap perm (leftmostDescent perm)))
            (applyAdjacentSwap perm (leftmostDescent perm)))
      (isIdentityPerm perm) nonIdentity
  have bubbleSnoc : bubbleWord perm
      = leftmostDescent perm :: bubbleWord (applyAdjacentSwap perm (leftmostDescent perm)) := by
    show bubbleWordFueled (inversionCount perm) perm = _
    rw [inversionSucc]
    exact fueledStep
  show (bubbleWord perm).reverse
      = (bubbleWord (applyAdjacentSwap perm (leftmostDescent perm))).reverse ++ [leftmostDescent perm]
  rw [bubbleSnoc]
  exact reverseConsLocal (leftmostDescent perm)
    (bubbleWord (applyAdjacentSwap perm (leftmostDescent perm)))

/-- ★★ **The insertion step — CANCEL mode, GENERAL.**  For ANY non-identity `perm`, inserting the leftmost-descent
generator `s_d` at the tail of the canonical word (`canonicalCrossingWord perm ++ [d]`, `d = leftmostDescent perm`)
is `BrauerConvFree7`-convertible to the canonical word of the swapped permutation `perm · s_d`.  PROOF: the
staircase-snoc identity rewrites `canonicalCrossingWord perm = canonicalCrossingWord (perm · s_d) ++ [d]`, so the
inserted `[d]` meets the trailing `[d]` as `[d, d]`, and R2 (`crossingCancelFree` whiskered on the left) collapses
it — the inversion count drops `inversionCount perm → inversionCount (perm · s_d)`.  This closes the CANCEL mode of
the general insertion step for ARBITRARY `perm : List Nat` (no genuine-permutation hypothesis needed), no inner
induction.  It is the general form of `crossingInsertionStep_cancel_smoke`. -/
theorem crossingInsertionStep_atLeftmostDescent (perm : List Nat)
    (nonIdentity : isIdentityPerm perm = false) :
    BrauerConvFree7 (crossingWord (canonicalCrossingWord perm ++ [leftmostDescent perm]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm (leftmostDescent perm)))) := by
  rw [canonicalCrossingWord_snoc_leftmostDescent perm nonIdentity,
    appendSnocAssoc (canonicalCrossingWord (applyAdjacentSwap perm (leftmostDescent perm)))
      (leftmostDescent perm) [leftmostDescent perm],
    crossingWord_append (canonicalCrossingWord (applyAdjacentSwap perm (leftmostDescent perm)))
      [leftmostDescent perm, leftmostDescent perm]]
  have base := BrauerConvFree7.whiskerLeft
    (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm (leftmostDescent perm))))
    (crossingCancelFree (leftmostDescent perm))
  rw [appendNilLocal
    (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm (leftmostDescent perm))))] at base
  exact base

/-- Non-vacuity — the GENERAL CANCEL mode on a bigger input than the smoke: inserting the leftmost descent `0` of the
reversal `[2, 1, 0]` into its canonical word `[0, 1, 0]` yields `[0, 1, 0, 0]`, whose trailing `[0, 0]` cancels to the
canonical word `[0, 1]` of `applyAdjacentSwap [2, 1, 0] 0 = [1, 2, 0]`. -/
theorem crossingInsertionStep_atLeftmostDescent_smoke :
    BrauerConvFree7 (crossingWord (canonicalCrossingWord [2, 1, 0] ++ [leftmostDescent [2, 1, 0]]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap [2, 1, 0] (leftmostDescent [2, 1, 0])))) :=
  crossingInsertionStep_atLeftmostDescent [2, 1, 0] rfl

/-! ## WP-BRAUER r7 — the HONEST reformulation: the IN-RANGE insertion step over genuine permutations

The r5 fold `crossingOnly_straightens_ofInsertionStep` consumes the `∀ (perm) (position)` insertion hypothesis, which
the r6 diagnosis proved FALSE for out-of-range positions (`perm = [0, 1]`, `position = 5`: `applyAdjacentSwap` is a
no-op past the end, so the step degenerates to the underivable lone-crossing `~ []`).  This section defines the
GENUINELY provable residual `InRangeInsertionStep` — quantified only over `isDistinctList` permutations (genuine
one-line permutations) at IN-RANGE positions (`position + 1 < perm.length`, where the crossing acts on two real
strands) — and revises the fold to consume it, threading a `wellFormedCrossingWord` predicate that guarantees every
letter of the input word is in range (so the peeled last letter's position is `< bottomCount = perm.length`).

The r5 conditional folds are KEPT (unchanged, additive) — they are correct as conditionals; the reformulated fold
`crossingOnly_straightensFueled_wellFormed` is the one whose hypothesis is TRUE and unconditionally dischargeable once
the modes close.  The permutation invariants (distinctness preserved by `applyAdjacentSwap`, true of `List.range`) are
proven here as the discharge kit. -/

/-! ### Local propext-free boolean / arithmetic helpers for the reformulation -/

/-- `Nat.beq` is symmetric — structural on both `Nat`s, `propext`-free. -/
private theorem natBeqSymm : (leftValue rightValue : Nat) → Nat.beq leftValue rightValue = Nat.beq rightValue leftValue
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | _ + 1, 0 => rfl
  | leftValue + 1, rightValue + 1 => natBeqSymm leftValue rightValue

/-- Left-commutativity of boolean `or` — full-enum on the outer two flags, `propext`-free. -/
private theorem boolOrLeftComm : (firstFlag secondFlag thirdFlag : Bool) →
    (firstFlag || (secondFlag || thirdFlag)) = (secondFlag || (firstFlag || thirdFlag))
  | false, false, _ => rfl
  | false, true, _ => rfl
  | true, false, _ => rfl
  | true, true, _ => rfl

/-- Left projection of a false boolean disjunction. -/
private theorem boolOrFalseLeft : (leftFlag rightFlag : Bool) → (leftFlag || rightFlag) = false →
    leftFlag = false
  | false, _, _ => rfl
  | true, _, disj => Bool.noConfusion disj

/-- Right projection of a false boolean disjunction. -/
private theorem boolOrFalseRight : (leftFlag rightFlag : Bool) → (leftFlag || rightFlag) = false →
    rightFlag = false
  | false, _, disj => disj
  | true, _, disj => Bool.noConfusion disj

/-- Reflect `not flag = true` to `flag = false` — full-enum `Bool`, `propext`-free. -/
private theorem eqFalseOfNotTrue : (flag : Bool) → (not flag) = true → flag = false
  | false, _ => rfl
  | true, notTrue => Bool.noConfusion notTrue

/-- `Nat.blt smaller larger = true → Nat.beq larger smaller = false` — a strict inequality rules out equality.
Structural on both `Nat`s, `propext`-free. -/
private theorem natBeqFalse_ofBlt : (smaller larger : Nat) → Nat.blt smaller larger = true →
    Nat.beq larger smaller = false
  | 0, 0, bltTrue => Bool.noConfusion bltTrue
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, bltTrue => Bool.noConfusion bltTrue
  | smaller + 1, larger + 1, bltTrue => natBeqFalse_ofBlt smaller larger bltTrue

/-- `Nat.ble` reflexivity — structural, `propext`-free. -/
private theorem natBleRefl : (value : Nat) → Nat.ble value value = true
  | 0 => rfl
  | value + 1 => natBleRefl value

/-- Weaken the upper bound of a true `Nat.ble` by one — structural, `propext`-free. -/
private theorem natBleWeakenRight : (lower upper : Nat) → Nat.ble lower upper = true →
    Nat.ble lower (upper + 1) = true
  | 0, _, _ => rfl
  | _ + 1, 0, bleTrue => Bool.noConfusion bleTrue
  | lower + 1, upper + 1, bleTrue => natBleWeakenRight lower upper bleTrue

/-- `value` is strictly below its successor. -/
private theorem natBltSelfSucc (value : Nat) : Nat.blt value (value + 1) = true :=
  natBleRefl (value + 1)

/-! ### The reformulation predicates + the honest in-range insertion step -/

/-- Boolean membership in a `Nat` list — full-enum `Nat.beq` fold, `propext`-free (unlike `List.elem` machinery). -/
def memBool (value : Nat) : List Nat → Bool
  | [] => false
  | head :: rest => Nat.beq head value || memBool value rest

/-- The GENUINE-permutation invariant: pairwise-distinct entries.  True of `List.range`, preserved by
`applyAdjacentSwap`; the exact content EXTEND (strict ascent) and the fold's insertion-step discharge consume. -/
def isDistinctList : List Nat → Bool
  | [] => true
  | head :: rest => (not (memBool head rest)) && isDistinctList rest

/-- A crossing word is WELL-FORMED for `bottomCount` strands when every letter is an in-range adjacent position
(`letter + 1 < bottomCount`), so each crossing acts on two real strands.  Structural, `Nat.blt`-based. -/
def wellFormedCrossingWord (bottomCount : Nat) : List Nat → Bool
  | [] => true
  | position :: rest => Nat.blt (position + 1) bottomCount && wellFormedCrossingWord bottomCount rest

/-- ★★ **The HONEST insertion residual** — in-range (`position + 1 < perm.length`, where the crossing acts) over
GENUINE (distinct-entry) permutations.  Unlike the r5 `∀ (perm) (position)` hypothesis (FALSE out-of-range), this is a
TRUE statement (Björner–Brenti Thm 3.3.1 / Tits): both sides realize `applyAdjacentSwap perm position`.  The fold below
consumes it; proving it is the CANCEL (done) + EXTEND + COMMUTE + BRAID mode assembly. -/
def InRangeInsertionStep : Prop :=
  ∀ (perm : List Nat) (position : Nat),
    isDistinctList perm = true →
    position + 1 < perm.length →
    BrauerConvFree7 (crossingWord (canonicalCrossingWord perm ++ [position]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm position)))

/-! ### The genuine-permutation invariant is preserved by the fold -/

/-- ★ **Membership is invariant under an adjacent swap** — the swap only reorders two entries, so the multiset (hence
`memBool`) is unchanged.  Structural on the swap's own matcher (mirrors `countEntriesBelow_applyAdjacentSwap`). -/
theorem memBool_applyAdjacentSwap : (value : Nat) → (perm : List Nat) → (position : Nat) →
    memBool value (applyAdjacentSwap perm position) = memBool value perm
  | _, [], _ => rfl
  | _, _ :: [], _ => rfl
  | value, first :: second :: rest, 0 =>
      boolOrLeftComm (Nat.beq second value) (Nat.beq first value) (memBool value rest)
  | value, first :: second :: rest, position + 1 =>
      congrArg (Nat.beq first value || ·) (memBool_applyAdjacentSwap value (second :: rest) position)

/-- ★ **An adjacent swap preserves distinctness** — a permutation of distinct entries stays distinct.  The genuine-
permutation invariant threaded through the fold.  Structural on the swap's own matcher. -/
theorem isDistinctList_applyAdjacentSwap : (perm : List Nat) → (position : Nat) →
    isDistinctList perm = true → isDistinctList (applyAdjacentSwap perm position) = true
  | [], _, _ => rfl
  | _ :: [], _, distinct => distinct
  | first :: second :: rest, 0, distinct => by
      have memFirst : memBool first (second :: rest) = false :=
        eqFalseOfNotTrue _ (boolAndTrueLeft _ _ distinct)
      have rightDist : isDistinctList (second :: rest) = true := boolAndTrueRight _ _ distinct
      have beqSecondFirst : Nat.beq second first = false := boolOrFalseLeft _ _ memFirst
      have memFirstRest : memBool first rest = false := boolOrFalseRight _ _ memFirst
      have distRest : isDistinctList rest = true := boolAndTrueRight _ _ rightDist
      have memSecondRest : memBool second rest = false := eqFalseOfNotTrue _ (boolAndTrueLeft _ _ rightDist)
      have beqFirstSecond : Nat.beq first second = false := (natBeqSymm first second).trans beqSecondFirst
      show (not (Nat.beq first second || memBool second rest)
            && (not (memBool first rest) && isDistinctList rest)) = true
      rw [beqFirstSecond, memSecondRest, memFirstRest, distRest]; rfl
  | first :: second :: rest, position + 1, distinct => by
      have memFirst : memBool first (second :: rest) = false :=
        eqFalseOfNotTrue _ (boolAndTrueLeft _ _ distinct)
      have distTail : isDistinctList (second :: rest) = true := boolAndTrueRight _ _ distinct
      have distSwap : isDistinctList (applyAdjacentSwap (second :: rest) position) = true :=
        isDistinctList_applyAdjacentSwap (second :: rest) position distTail
      have memSwap : memBool first (applyAdjacentSwap (second :: rest) position) = false := by
        rw [memBool_applyAdjacentSwap first (second :: rest) position]; exact memFirst
      show (not (memBool first (applyAdjacentSwap (second :: rest) position))
            && isDistinctList (applyAdjacentSwap (second :: rest) position)) = true
      rw [memSwap, distSwap]; rfl

/-- An ascending-from-`start` list has no member strictly below `start`.  Structural on the list. -/
private theorem memBool_ascendingFrom_below : (start : Nat) → (xs : List Nat) → (value : Nat) →
    isAscendingFrom start xs = true → Nat.blt value start = true → memBool value xs = false
  | _, [], _, _, _ => rfl
  | start, head :: rest, value, ascending, valueBelow => by
      have headEq : head = start := natEqOfBeq head start (boolAndTrueLeft _ _ ascending)
      have restAsc : isAscendingFrom (start + 1) rest = true := boolAndTrueRight _ _ ascending
      have valueBelowHead : Nat.blt value head = true := by rw [headEq]; exact valueBelow
      have beqHeadValue : Nat.beq head value = false := natBeqFalse_ofBlt value head valueBelowHead
      have valueBelowSucc : Nat.blt value (start + 1) = true := natBleWeakenRight (value + 1) start valueBelow
      have memRest : memBool value rest = false :=
        memBool_ascendingFrom_below (start + 1) rest value restAsc valueBelowSucc
      show (Nat.beq head value || memBool value rest) = false
      rw [beqHeadValue, memRest]; rfl

/-- An ascending-from-`start` list is distinct (the head is below every later entry).  Structural on the list. -/
private theorem isDistinctList_ofAscendingFrom : (start : Nat) → (xs : List Nat) →
    isAscendingFrom start xs = true → isDistinctList xs = true
  | _, [], _ => rfl
  | start, head :: rest, ascending => by
      have headEq : head = start := natEqOfBeq head start (boolAndTrueLeft _ _ ascending)
      have restAsc : isAscendingFrom (start + 1) rest = true := boolAndTrueRight _ _ ascending
      have notMemHead : memBool head rest = false := by
        apply memBool_ascendingFrom_below (start + 1) rest head restAsc
        rw [headEq]; exact natBltSelfSucc start
      have distRest : isDistinctList rest = true := isDistinctList_ofAscendingFrom (start + 1) rest restAsc
      show (not (memBool head rest) && isDistinctList rest) = true
      rw [notMemHead, distRest]; rfl

/-- ★ **The identity permutation `List.range count` is distinct** — the base of the fold's genuine-permutation
invariant. -/
theorem isDistinctList_range (count : Nat) : isDistinctList (List.range count) = true :=
  isDistinctList_ofAscendingFrom 0 (List.range count) (isAscendingFrom_range count)

/-- Folding adjacent swaps preserves distinctness (each swap does). -/
private theorem isDistinctList_foldlSwap : (positions perm : List Nat) →
    isDistinctList perm = true → isDistinctList (positions.foldl applyAdjacentSwap perm) = true
  | [], _, distinct => distinct
  | position :: rest, perm, distinct => by
      show isDistinctList (rest.foldl applyAdjacentSwap (applyAdjacentSwap perm position)) = true
      exact isDistinctList_foldlSwap rest (applyAdjacentSwap perm position)
        (isDistinctList_applyAdjacentSwap perm position distinct)

/-- ★ **Every realized permutation is genuine (distinct entries)** — `permuteOfCrossingWord` folds swaps over the
distinct identity `List.range bottomCount`, so its output is distinct.  The `perm`-side hypothesis the fold's
`InRangeInsertionStep` call needs. -/
theorem isDistinctList_permuteOfCrossingWord (bottomCount : Nat) (positions : List Nat) :
    isDistinctList (permuteOfCrossingWord bottomCount positions) = true := by
  show isDistinctList (positions.foldl applyAdjacentSwap (List.range bottomCount)) = true
  exact isDistinctList_foldlSwap positions (List.range bottomCount) (isDistinctList_range bottomCount)

/-! ### Well-formedness projections + the in-range last letter -/

/-- A prefix of a well-formed crossing word is well-formed.  Structural on the prefix. -/
private theorem wellFormedCrossingWord_snoc_left : (bottomCount : Nat) → (prefixPositions : List Nat) →
    (lastPosition : Nat) → wellFormedCrossingWord bottomCount (prefixPositions ++ [lastPosition]) = true →
    wellFormedCrossingWord bottomCount prefixPositions = true
  | _, [], _, _ => rfl
  | bottomCount, position :: rest, lastPosition, wf => by
      show (Nat.blt (position + 1) bottomCount && wellFormedCrossingWord bottomCount rest) = true
      rw [boolAndTrueLeft _ _ wf,
        wellFormedCrossingWord_snoc_left bottomCount rest lastPosition (boolAndTrueRight _ _ wf)]; rfl

/-- The last letter of a well-formed crossing word is in range.  Structural on the prefix. -/
private theorem wellFormedCrossingWord_snoc_right : (bottomCount : Nat) → (prefixPositions : List Nat) →
    (lastPosition : Nat) → wellFormedCrossingWord bottomCount (prefixPositions ++ [lastPosition]) = true →
    Nat.blt (lastPosition + 1) bottomCount = true
  | _, [], _, wf => boolAndTrueLeft _ _ wf
  | bottomCount, _ :: rest, lastPosition, wf =>
      wellFormedCrossingWord_snoc_right bottomCount rest lastPosition (boolAndTrueRight _ _ wf)

/-- Reflect a true `Nat.ble` to a propositional `≤` — structural on the `Nat`s. -/
private theorem leOfBleTrue : (lower upper : Nat) → Nat.ble lower upper = true → lower ≤ upper
  | 0, upper, _ => Nat.zero_le upper
  | _ + 1, 0, bleTrue => Bool.noConfusion bleTrue
  | lower + 1, upper + 1, bleTrue => Nat.succ_le_succ (leOfBleTrue lower upper bleTrue)

/-- Reflect a true `Nat.blt` to a propositional `<`. -/
private theorem ltOfBltTrue (lower upper : Nat) (bltTrue : Nat.blt lower upper = true) : lower < upper :=
  leOfBleTrue (lower + 1) upper bltTrue

/-- ★ **The peeled last letter of a well-formed word is in range** — `position + 1 < perm.length` for
`perm = permuteOfCrossingWord bottomCount prefix` (length `bottomCount`).  The `position`-side hypothesis the fold's
`InRangeInsertionStep` call needs. -/
theorem lastPosition_inRange_ofWellFormed (bottomCount : Nat) (prefixPositions : List Nat) (lastPosition : Nat)
    (wf : wellFormedCrossingWord bottomCount (prefixPositions ++ [lastPosition]) = true) :
    lastPosition + 1 < (permuteOfCrossingWord bottomCount prefixPositions).length := by
  rw [permuteOfCrossingWord_length bottomCount prefixPositions]
  exact ltOfBltTrue (lastPosition + 1) bottomCount
    (wellFormedCrossingWord_snoc_right bottomCount prefixPositions lastPosition wf)

/-! ### The REVISED fold — consuming `InRangeInsertionStep` under well-formedness -/

/-- The reformulated fold, fuel-indexed by word length.  Line-for-line the r5 `crossingOnly_straightensFueled`, plus
the two discharge lemmas at the `insertionStep` call site: `isDistinctList_permuteOfCrossingWord` (the perm is genuine)
and `lastPosition_inRange_ofWellFormed` (the peeled letter is in range).  The well-formedness of the prefix is threaded
by `wellFormedCrossingWord_snoc_left`. -/
theorem crossingOnly_straightensFueled_wellFormed (bottomCount : Nat)
    (insertionStep : InRangeInsertionStep) :
    (fuel : Nat) → (word : List Nat) → word.length = fuel →
    wellFormedCrossingWord bottomCount word = true →
    BrauerConvFree7 (crossingWord word)
      (crossingWord (canonicalCrossingWord (permuteOfCrossingWord bottomCount word)))
  | 0, [], _, _ => by
      show BrauerConvFree7 [] (crossingWord (canonicalCrossingWord (List.range bottomCount)))
      rw [canonicalCrossingWord_range bottomCount]
      exact BrauerConvFree7.ofFree (BrauerConvFree.refl [])
  | 0, _ :: _, lengthEq, _ => Nat.noConfusion lengthEq
  | fuel + 1, word, lengthEq, wfWord => by
      cases listNilOrSnoc word with
      | inl wordNil => subst wordNil; exact Nat.noConfusion lengthEq
      | inr wordSnoc =>
          obtain ⟨prefixPositions, lastPosition, wordEq⟩ := wordSnoc
          subst wordEq
          rw [lengthSnoc prefixPositions lastPosition] at lengthEq
          have prefixLengthEq : prefixPositions.length = fuel := Nat.succ.inj lengthEq
          have wfPrefix : wellFormedCrossingWord bottomCount prefixPositions = true :=
            wellFormedCrossingWord_snoc_left bottomCount prefixPositions lastPosition wfWord
          have straightenedPrefix :=
            crossingOnly_straightensFueled_wellFormed bottomCount insertionStep fuel prefixPositions
              prefixLengthEq wfPrefix
          rw [permuteOfCrossingWord_snoc bottomCount prefixPositions lastPosition]
          refine BrauerConvFree7.trans ?_
            (insertionStep (permuteOfCrossingWord bottomCount prefixPositions) lastPosition
              (isDistinctList_permuteOfCrossingWord bottomCount prefixPositions)
              (lastPosition_inRange_ofWellFormed bottomCount prefixPositions lastPosition wfWord))
          rw [crossingWord_append prefixPositions [lastPosition],
            crossingWord_append (canonicalCrossingWord (permuteOfCrossingWord bottomCount prefixPositions))
              [lastPosition]]
          exact BrauerConvFree7.whiskerRight [crossingAt lastPosition] straightenedPrefix

/-- ★ **Every WELL-FORMED crossing word straightens to the canonical word of its permutation — CONDITIONAL on the
in-range insertion step.**  The un-fueled reformulated fold: the HONEST version of
`crossingOnly_straightens_ofInsertionStep`, whose hypothesis (`InRangeInsertionStep`) is TRUE (not FALSE out-of-range
like the r5 one). -/
theorem crossingOnly_straightens_wellFormed (bottomCount : Nat) (insertionStep : InRangeInsertionStep)
    (word : List Nat) (wfWord : wellFormedCrossingWord bottomCount word = true) :
    BrauerConvFree7 (crossingWord word)
      (crossingWord (canonicalCrossingWord (permuteOfCrossingWord bottomCount word))) :=
  crossingOnly_straightensFueled_wellFormed bottomCount insertionStep word.length word rfl wfWord

/-- ★★ **The symmetric-group WORD PROBLEM (well-formed scope) — CONDITIONAL on the in-range insertion step.**  Two
well-formed crossing words with EQUAL realized permutation are `BrauerConvFree7`-convertible: both straighten to the
canonical word of that common permutation.  The honest reformulation of `crossingWords_equalPerm_conv_ofInsertionStep`
— its hypothesis is the TRUE `InRangeInsertionStep`, and its scope (well-formed words over genuine permutations) is the
honest scope where the crossing generators actually act. -/
theorem crossingWords_equalPerm_conv_wellFormed (bottomCount : Nat) (insertionStep : InRangeInsertionStep)
    (wordLeft wordRight : List Nat)
    (wfLeft : wellFormedCrossingWord bottomCount wordLeft = true)
    (wfRight : wellFormedCrossingWord bottomCount wordRight = true)
    (permEq : permuteOfCrossingWord bottomCount wordLeft = permuteOfCrossingWord bottomCount wordRight) :
    BrauerConvFree7 (crossingWord wordLeft) (crossingWord wordRight) := by
  have straightenedRight :=
    crossingOnly_straightens_wellFormed bottomCount insertionStep wordRight wfRight
  rw [← permEq] at straightenedRight
  exact BrauerConvFree7.trans
    (crossingOnly_straightens_wellFormed bottomCount insertionStep wordLeft wfLeft)
    (BrauerConvFree7.symm straightenedRight)

/-! ## WP-BRAUER r7 — the EXTEND mode (general, over genuine permutations)

The EXTEND mode inserts a position `position < leftmostDescent perm`.  Under distinctness the entry pair at `position`
is a STRICT ascent, so the swap creates a fresh descent exactly there: `leftmostDescent (perm · s_position) = position`
and `perm · s_position` is non-identity.  The staircase-snoc identity then makes the insertion REFLEXIVITY:
`canonicalCrossingWord (perm · s_position) = canonicalCrossingWord perm ++ [position]` (using the involution
`perm · s_position · s_position = perm`).  The distinctness hypothesis is essential — the marker's named counterexample
`[1, 1, 0]` fails `leftmostDescent (perm · s_0) = 0`.  Björner–Brenti: this is the `¬IsRightDescent` / `ℓ(ws) = ℓ(w)+1`
extend branch of the length dichotomy, driven by the computable test `perm[position] < perm[position+1]`. -/

/-! ### Local propext-free boolean / order helpers -/

/-- `Nat.blt larger smaller = false → Nat.ble smaller larger = true` — the antisymmetric complement.  Structural. -/
private theorem bleOfNotBltSwap : (smaller larger : Nat) → Nat.blt larger smaller = false →
    Nat.ble smaller larger = true
  | 0, _, _ => rfl
  | _ + 1, 0, bltFalse => Bool.noConfusion bltFalse
  | smaller + 1, larger + 1, bltFalse => bleOfNotBltSwap smaller larger bltFalse

/-- `Nat.ble a b = true → Nat.beq a b = false → Nat.blt a b = true` — a distinct `≤` pair is `<`.  Structural. -/
private theorem bltOfBleNeq : (smaller larger : Nat) → Nat.ble smaller larger = true →
    Nat.beq smaller larger = false → Nat.blt smaller larger = true
  | 0, 0, _, beqFalse => Bool.noConfusion beqFalse
  | 0, _ + 1, _, _ => rfl
  | _ + 1, 0, bleTrue, _ => Bool.noConfusion bleTrue
  | smaller + 1, larger + 1, bleTrue, beqFalse => bltOfBleNeq smaller larger bleTrue beqFalse

/-- `Nat.ble` transitivity — structural on all three `Nat`s, `propext`-free. -/
private theorem bleTrans : (lower mid upper : Nat) →
    Nat.ble lower mid = true → Nat.ble mid upper = true → Nat.ble lower upper = true
  | 0, _, _, _, _ => rfl
  | _ + 1, 0, _, bleLowerMid, _ => Bool.noConfusion bleLowerMid
  | _ + 1, _ + 1, 0, _, bleMidUpper => Bool.noConfusion bleMidUpper
  | lower + 1, mid + 1, upper + 1, bleLowerMid, bleMidUpper => bleTrans lower mid upper bleLowerMid bleMidUpper

/-- `Nat.ble a b = true → Nat.blt b a = false` — `a ≤ b` rules out `b < a`.  Structural. -/
private theorem bltFalseOfBle : (smaller larger : Nat) → Nat.ble smaller larger = true →
    Nat.blt larger smaller = false
  | 0, _, _ => rfl
  | _ + 1, 0, bleTrue => Bool.noConfusion bleTrue
  | smaller + 1, larger + 1, bleTrue => bltFalseOfBle smaller larger bleTrue

/-! ### Head / cons structural helpers for the leftmost-descent tracking -/

/-- The head of a `Nat` list (`0` on empty). -/
private def firstEntry : List Nat → Nat
  | [] => 0
  | head :: _ => head

/-- The tail of a `Nat` list. -/
private def dropFirst : List Nat → List Nat
  | [] => []
  | _ :: tail => tail

/-- A list of successor length is its head cons its tail — the propext-free `cons` eta. -/
private theorem consEta : (list : List Nat) → (predLength : Nat) → list.length = predLength + 1 →
    list = firstEntry list :: dropFirst list
  | [], _, lengthEq => Nat.noConfusion lengthEq
  | _ :: _, _, _ => rfl

/-- Swapping at a positive position leaves the head untouched — the head-eta of `applyAdjacentSwap` at `position+1`. -/
private theorem applyAdjacentSwap_cons_succ : (headElement : Nat) → (list : List Nat) → (position : Nat) →
    applyAdjacentSwap (headElement :: list) (position + 1) = headElement :: applyAdjacentSwap list position
  | _, [], _ => rfl
  | _, _ :: _, _ => rfl

/-- ★ **`applyAdjacentSwap` is an involution** — applying the same adjacent swap twice restores the list (a no-op past
the end is trivially involutive; an in-range swap undoes itself).  Structural on the swap's own matcher; the reflexivity
witness EXTEND stands on. -/
theorem applyAdjacentSwap_involutive : (perm : List Nat) → (position : Nat) →
    applyAdjacentSwap (applyAdjacentSwap perm position) position = perm
  | [], _ => rfl
  | _ :: [], _ => rfl
  | _ :: _ :: _, 0 => rfl
  | first :: second :: rest, position + 1 => by
      rw [applyAdjacentSwap_cons_succ first (second :: rest) position,
        applyAdjacentSwap_cons_succ first (applyAdjacentSwap (second :: rest) position) position,
        applyAdjacentSwap_involutive (second :: rest) position]

/-- With no descent at the junction (`Nat.blt firstY head = false`), the leftmost descent of a cons steps by one. -/
private theorem leftmostDescent_cons_headBltFalse (head firstY : Nat) (restY : List Nat)
    (noJunctionDescent : Nat.blt firstY head = false) :
    leftmostDescent (head :: firstY :: restY) = leftmostDescent (firstY :: restY) + 1 :=
  condFalse 0 (leftmostDescent (firstY :: restY) + 1) (Nat.blt firstY head) noJunctionDescent

/-- With no descent at the junction, the cons keeps the tail's identity status. -/
private theorem isIdentityPerm_cons_headBltFalse (head firstY : Nat) (restY : List Nat)
    (noJunctionDescent : Nat.blt firstY head = false) :
    isIdentityPerm (head :: firstY :: restY) = isIdentityPerm (firstY :: restY) :=
  condFalse false (isIdentityPerm (firstY :: restY)) (Nat.blt firstY head) noJunctionDescent

/-- ★ **The head does not drop below a descent** — for a swap at a below-leftmost-descent position the head of the
result is `≥` the head of the input (a `position+1` swap fixes the head; a `position = 0` swap raises it from `first`
to `second`, an ascent since `0 < leftmostDescent`).  The junction-monotonicity leg of the EXTEND leftmost-descent
computation. -/
private theorem firstEntry_applyAdjacentSwap_belowDescent_ge :
    (perm : List Nat) → (position : Nat) →
    Nat.blt position (leftmostDescent perm) = true →
    Nat.ble (firstEntry perm) (firstEntry (applyAdjacentSwap perm position)) = true
  | [], _, hbelow => Bool.noConfusion hbelow
  | _ :: [], _, hbelow => Bool.noConfusion hbelow
  | first :: second :: rest, 0, hbelow =>
      match hDescent : Nat.blt second first with
      | true => by
          have ld0 : leftmostDescent (first :: second :: rest) = 0 :=
            condTrue 0 (leftmostDescent (second :: rest) + 1) (Nat.blt second first) hDescent
          rw [ld0] at hbelow
          exact Bool.noConfusion hbelow
      | false => by
          show Nat.ble first second = true
          exact bleOfNotBltSwap first second hDescent
  | first :: second :: rest, _ + 1, _ => by
      show Nat.ble first first = true
      exact natBleRefl first

/-- ★★ **The swap at a below-leftmost-descent position lands its NEW leftmost descent exactly at that position (and is
non-identity).**  The structural core of the EXTEND mode: for `position < leftmostDescent perm` over a genuine
permutation, `leftmostDescent (perm · s_position) = position` and `perm · s_position` has a descent (is non-identity).
Structural induction on `perm` / `position`; the `position+1` step threads the head-monotonicity
(`firstEntry_applyAdjacentSwap_belowDescent_ge`) so the junction is descent-free and the leftmost descent steps in. -/
theorem leftmostDescent_applyAdjacentSwap_belowDescent :
    (perm : List Nat) → (position : Nat) →
    isDistinctList perm = true → Nat.blt position (leftmostDescent perm) = true →
    leftmostDescent (applyAdjacentSwap perm position) = position
      ∧ isIdentityPerm (applyAdjacentSwap perm position) = false
  | [], _, _, hbelow => Bool.noConfusion hbelow
  | _ :: [], _, _, hbelow => Bool.noConfusion hbelow
  | first :: second :: rest, 0, distinct, hbelow =>
      match hDescent : Nat.blt second first with
      | true => by
          have ld0 : leftmostDescent (first :: second :: rest) = 0 :=
            condTrue 0 (leftmostDescent (second :: rest) + 1) (Nat.blt second first) hDescent
          rw [ld0] at hbelow
          exact Bool.noConfusion hbelow
      | false => by
          have memFirst : memBool first (second :: rest) = false :=
            eqFalseOfNotTrue _ (boolAndTrueLeft _ _ distinct)
          have beqSecondFirst : Nat.beq second first = false := boolOrFalseLeft _ _ memFirst
          have beqFirstSecond : Nat.beq first second = false := (natBeqSymm first second).trans beqSecondFirst
          have bltFirstSecond : Nat.blt first second = true :=
            bltOfBleNeq first second (bleOfNotBltSwap first second hDescent) beqFirstSecond
          refine ⟨?_, ?_⟩
          · show leftmostDescent (second :: first :: rest) = 0
            exact condTrue 0 (leftmostDescent (first :: rest) + 1) (Nat.blt first second) bltFirstSecond
          · show isIdentityPerm (second :: first :: rest) = false
            exact condTrue false (isIdentityPerm (first :: rest)) (Nat.blt first second) bltFirstSecond
  | first :: second :: rest, position + 1, distinct, hbelow =>
      match hDescent : Nat.blt second first with
      | true => by
          have ld0 : leftmostDescent (first :: second :: rest) = 0 :=
            condTrue 0 (leftmostDescent (second :: rest) + 1) (Nat.blt second first) hDescent
          rw [ld0] at hbelow
          exact Bool.noConfusion hbelow
      | false => by
          have ldSucc : leftmostDescent (first :: second :: rest) = leftmostDescent (second :: rest) + 1 :=
            condFalse 0 (leftmostDescent (second :: rest) + 1) (Nat.blt second first) hDescent
          rw [ldSucc] at hbelow
          have hbelowTail : Nat.blt position (leftmostDescent (second :: rest)) = true := hbelow
          have distTail : isDistinctList (second :: rest) = true := boolAndTrueRight _ _ distinct
          have ih := leftmostDescent_applyAdjacentSwap_belowDescent (second :: rest) position distTail hbelowTail
          have noJunction : Nat.blt (firstEntry (applyAdjacentSwap (second :: rest) position)) first = false :=
            bltFalseOfBle first (firstEntry (applyAdjacentSwap (second :: rest) position))
              (bleTrans first second (firstEntry (applyAdjacentSwap (second :: rest) position))
                (bleOfNotBltSwap first second hDescent)
                (firstEntry_applyAdjacentSwap_belowDescent_ge (second :: rest) position hbelowTail))
          have ysCons : applyAdjacentSwap (second :: rest) position
              = firstEntry (applyAdjacentSwap (second :: rest) position)
                :: dropFirst (applyAdjacentSwap (second :: rest) position) :=
            consEta (applyAdjacentSwap (second :: rest) position) rest.length
              (applyAdjacentSwap_length (second :: rest) position)
          refine ⟨?_, ?_⟩
          · show leftmostDescent (first :: applyAdjacentSwap (second :: rest) position) = position + 1
            rw [ysCons, leftmostDescent_cons_headBltFalse first
              (firstEntry (applyAdjacentSwap (second :: rest) position))
              (dropFirst (applyAdjacentSwap (second :: rest) position)) noJunction, ← ysCons, ih.1]
          · show isIdentityPerm (first :: applyAdjacentSwap (second :: rest) position) = false
            rw [ysCons, isIdentityPerm_cons_headBltFalse first
              (firstEntry (applyAdjacentSwap (second :: rest) position))
              (dropFirst (applyAdjacentSwap (second :: rest) position)) noJunction, ← ysCons, ih.2]

/-- ★★ **The insertion step — EXTEND mode, GENERAL (over genuine permutations).**  For any distinct-entry `perm` and
`position < leftmostDescent perm`, inserting `position` at the tail of the canonical word STAYS canonical — the residual
holds by REFLEXIVITY.  PROOF: the swap `perm · s_position` has its new leftmost descent at `position` and is
non-identity (`leftmostDescent_applyAdjacentSwap_belowDescent`), so staircase-snoc gives
`canonicalCrossingWord (perm · s_position) = canonicalCrossingWord (perm · s_position · s_position) ++ [position]`, and
the involution `perm · s_position · s_position = perm` (`applyAdjacentSwap_involutive`) collapses the prefix to
`canonicalCrossingWord perm ++ [position]`.  The general form of `crossingInsertionStep_extend_smoke`; the distinctness
hypothesis is essential (`[1, 1, 0]` is the marker's named counterexample). -/
theorem crossingInsertionStep_extend (perm : List Nat) (position : Nat)
    (distinct : isDistinctList perm = true)
    (belowDescent : Nat.blt position (leftmostDescent perm) = true) :
    BrauerConvFree7 (crossingWord (canonicalCrossingWord perm ++ [position]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm position))) := by
  have swapFacts :=
    leftmostDescent_applyAdjacentSwap_belowDescent perm position distinct belowDescent
  have snoc :=
    canonicalCrossingWord_snoc_leftmostDescent (applyAdjacentSwap perm position) swapFacts.2
  rw [swapFacts.1, applyAdjacentSwap_involutive perm position] at snoc
  rw [snoc]
  exact BrauerConvFree7.ofFree (BrauerConvFree.refl _)

/-- Non-vacuity — the GENERAL EXTEND mode on the 3-cycle `[1, 2, 0]` (leftmost descent `1`) inserting `0 < 1`:
`canonicalCrossingWord [1, 2, 0] ++ [0] = [0, 1, 0]` is already the canonical word of the reversal
`applyAdjacentSwap [1, 2, 0] 0 = [2, 1, 0]`, so the step is reflexivity. -/
theorem crossingInsertionStep_extend_general_smoke :
    BrauerConvFree7 (crossingWord (canonicalCrossingWord [1, 2, 0] ++ [0]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap [1, 2, 0] 0))) :=
  crossingInsertionStep_extend [1, 2, 0] 0 (by decide) (by decide)

/-! ## WP-BRAUER r7 — the COMMUTE mode, LOCAL reduction (general, IH-free)

The COMMUTE mode inserts a position `position ≥ leftmostDescent perm + 2` — distant from the trailing canonical letter
`d = leftmostDescent perm` (staircase-snoc: `canonicalCrossingWord perm = canonicalCrossingWord (perm · s_d) ++ [d]`).
The distant pair `[d, position]` commutes freely (`crossingCommuteFree`, `d + 2 ≤ position`), so the inserted letter
slides PAST the trailing `d`.  This lemma ships that single commute step as a GENERAL, IH-free reduction:
`canonicalCrossingWord perm ++ [position] ~ canonicalCrossingWord (perm · s_d) ++ [position, d]`.  The residual after it
is `canonicalCrossingWord (perm · s_d) ++ [position]` — an insertion at the strictly-smaller permutation `perm · s_d`
(`inversionCount` dropped by one, `inversionCount_ofLeftmostDescentSwap_succ`), which the full COMMUTE mode discharges
by the outer `inversionCount` induction (the IH that the BRAID wall still gates — see the residual marker). -/

/-- ★★ **The insertion step — COMMUTE mode, LOCAL reduction (general).**  For any non-identity `perm` and a distant
`position ≥ leftmostDescent perm + 2`, the inserted letter commutes past the trailing canonical descent `d`:
`canonicalCrossingWord perm ++ [position]` is `BrauerConvFree7` to `canonicalCrossingWord (perm · s_d) ++ [position, d]`.
PROOF: staircase-snoc rewrites `canonicalCrossingWord perm = canonicalCrossingWord (perm · s_d) ++ [d]`, so the tail is
`[d, position]`, and `crossingCommuteFree d position` (whiskered left over `canonicalCrossingWord (perm · s_d)`)
transposes it to `[position, d]`.  IH-free; it is the single Coxeter COMMUTE step of the mode (the full mode re-inserts
`position` at `perm · s_d` via the `inversionCount` induction). -/
theorem crossingInsertionStep_commute_localReduction (perm : List Nat) (position : Nat)
    (nonIdentity : isIdentityPerm perm = false)
    (disjoint : leftmostDescent perm + 2 ≤ position) :
    BrauerConvFree7 (crossingWord (canonicalCrossingWord perm ++ [position]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm (leftmostDescent perm))
        ++ [position, leftmostDescent perm])) := by
  rw [canonicalCrossingWord_snoc_leftmostDescent perm nonIdentity,
    appendSnocAssoc (canonicalCrossingWord (applyAdjacentSwap perm (leftmostDescent perm)))
      (leftmostDescent perm) [position],
    crossingWord_append (canonicalCrossingWord (applyAdjacentSwap perm (leftmostDescent perm)))
      [leftmostDescent perm, position],
    crossingWord_append (canonicalCrossingWord (applyAdjacentSwap perm (leftmostDescent perm)))
      [position, leftmostDescent perm]]
  exact BrauerConvFree7.whiskerLeft
    (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm (leftmostDescent perm))))
    (crossingCommuteFree (leftmostDescent perm) position disjoint)

/-- Non-vacuity — the GENERAL COMMUTE local move on `[1, 0, 2, 3]` (leftmost descent `0`) inserting the distant `2`:
`canonicalCrossingWord [1, 0, 2, 3] ++ [2] = [0, 2]` commutes to `[2, 0] = canonicalCrossingWord [0, 1, 2, 3] ++ [2, 0]`
(the canonical word of `applyAdjacentSwap [1, 0, 2, 3] 0 = [0, 1, 2, 3]` is empty). -/
theorem crossingInsertionStep_commute_localReduction_smoke :
    BrauerConvFree7 (crossingWord (canonicalCrossingWord [1, 0, 2, 3] ++ [2]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap [1, 0, 2, 3] (leftmostDescent [1, 0, 2, 3]))
        ++ [2, leftmostDescent [1, 0, 2, 3]])) :=
  crossingInsertionStep_commute_localReduction [1, 0, 2, 3] 2 (by decide) (by decide)

/-! ## WP-BRAUER r8 — the BRAID mode, LOCAL reduction (Regime B, general, IH-free)

The BRAID mode inserts `position = leftmostDescent perm + 1` — adjacent to the trailing canonical descent
`d = leftmostDescent perm`, so it neither cancels (R2 needs equal generators) nor commutes (needs `|Δ| ≥ 2`).  A braid
(R3) needs a THIRD generator, supplied by the second-to-last canonical letter `d2 = leftmostDescent (perm · s_d)`.  The
recon's hand-verified dichotomy splits on `d2`: in Regime B (`d2 = d + 1`, the tail-local regime) the trailing three
canonical letters are `s_{d+1} s_d s_{d+1}`, which braid to `s_d s_{d+1} s_d`.  This lemma ships that single braid step
as a GENERAL, IH-free reduction — the exact analog of `crossingInsertionStep_commute_localReduction`:
`canonicalCrossingWord perm ++ [d+1] ~ canonicalCrossingWord (perm · s_d · s_{d+1}) ++ [d, d+1, d]`.  The residual after
it — the moved trailing `[d, d+1, d]` re-interacting leftward through the shorter prefix `perm · s_d · s_{d+1}` — is the
CARRY, whose fold is the standing lexicographic wall (Regime A additionally reaches into the prefix BEFORE braiding, so
the carry is not tail-local; see the residual marker). -/

/-- ★★ **The insertion step — BRAID mode, LOCAL reduction (Regime B, general, IH-free).**  For any `perm` whose leftmost
descent `d` and once-bubbled `perm · s_d` are both genuine descents (non-identity) with
`leftmostDescent (perm · s_d) = d + 1` (Regime B), the inserted `s_{d+1}` braids past the trailing canonical
`s_d s_{d+1}`: `canonicalCrossingWord perm ++ [d+1]` is `BrauerConvFree7` to
`canonicalCrossingWord (perm · s_d · s_{d+1}) ++ [d, d+1, d]`.  PROOF: two staircase-snocs
(`canonicalCrossingWord_snoc_leftmostDescent` on `perm`, then on `perm · s_d` with its descent rewritten to `d + 1` by
the Regime-B hypothesis) expose the trailing triple `s_{d+1} s_d s_{d+1}`, which `crossingBraidFree d` (symm, whiskered
left) transposes to `s_d s_{d+1} s_d`.  IH-free; it is the single Coxeter BRAID step of the mode.  The residual
`… ++ [d, d+1, d]` re-inserts leftward via the carry fold (the standing wall). -/
theorem crossingInsertionStep_braid_localReduction (perm : List Nat)
    (nonIdentity : isIdentityPerm perm = false)
    (nonIdentitySwapped : isIdentityPerm (applyAdjacentSwap perm (leftmostDescent perm)) = false)
    (regimeB : leftmostDescent (applyAdjacentSwap perm (leftmostDescent perm)) = leftmostDescent perm + 1) :
    BrauerConvFree7 (crossingWord (canonicalCrossingWord perm ++ [leftmostDescent perm + 1]))
      (crossingWord (canonicalCrossingWord
          (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1))
        ++ [leftmostDescent perm, leftmostDescent perm + 1, leftmostDescent perm])) := by
  have snocOuter := canonicalCrossingWord_snoc_leftmostDescent perm nonIdentity
  have snocInner :=
    canonicalCrossingWord_snoc_leftmostDescent (applyAdjacentSwap perm (leftmostDescent perm)) nonIdentitySwapped
  rw [regimeB] at snocInner
  rw [snocInner] at snocOuter
  rw [snocOuter,
    appendSnocAssoc (canonicalCrossingWord
          (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1))
        ++ [leftmostDescent perm + 1]) (leftmostDescent perm) [leftmostDescent perm + 1],
    appendSnocAssoc (canonicalCrossingWord
          (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1)))
        (leftmostDescent perm + 1) [leftmostDescent perm, leftmostDescent perm + 1],
    crossingWord_append (canonicalCrossingWord
          (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1)))
        [leftmostDescent perm + 1, leftmostDescent perm, leftmostDescent perm + 1],
    crossingWord_append (canonicalCrossingWord
          (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1)))
        [leftmostDescent perm, leftmostDescent perm + 1, leftmostDescent perm]]
  exact BrauerConvFree7.whiskerLeft
    (crossingWord (canonicalCrossingWord
      (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1))))
    (BrauerConvFree7.symm (crossingBraidFree (leftmostDescent perm)))

/-- Non-vacuity — the GENERAL Regime-B BRAID local move on the reversal `[2, 1, 0]` (leftmost descent `0`, once-bubbled
`[1, 2, 0]` with leftmost descent `1 = 0 + 1`) inserting `1`: `canonicalCrossingWord [2, 1, 0] ++ [1] = [0, 1, 0, 1]`
braids to `[0, 0, 1, 0] = canonicalCrossingWord [1, 0, 2] ++ [0, 1, 0]`
(`applyAdjacentSwap (applyAdjacentSwap [2, 1, 0] 0) 1 = [1, 0, 2]`). -/
theorem crossingInsertionStep_braid_localReduction_smoke :
    BrauerConvFree7 (crossingWord (canonicalCrossingWord [2, 1, 0] ++ [leftmostDescent [2, 1, 0] + 1]))
      (crossingWord (canonicalCrossingWord
          (applyAdjacentSwap (applyAdjacentSwap [2, 1, 0] (leftmostDescent [2, 1, 0]))
            (leftmostDescent [2, 1, 0] + 1))
        ++ [leftmostDescent [2, 1, 0], leftmostDescent [2, 1, 0] + 1, leftmostDescent [2, 1, 0]])) :=
  crossingInsertionStep_braid_localReduction [2, 1, 0] (by decide) (by decide) (by decide)

/-! ## WP-BRAUER r8 — the distant-swap kit (the two structural lemmas the residual marker named)

The outer `inversionCount` insertion induction re-inserts `position` at the strictly-smaller `perm · s_d`, which needs
two structural facts about a DISTANT swap (`position ≥ d + 2`): (1) disjoint adjacent swaps COMMUTE
(`applyAdjacentSwap_swap_disjoint`), so `perm · s_d · s_position = perm · s_position · s_d`; and (2) the leftmost
descent is INVARIANT under a distant swap (`leftmostDescent_applyAdjacentSwap_distant`), so the trailing canonical
letter of `perm · s_position` is still `d`.  Both were named as the missing structural inductions in the r7 residual
marker; this section ships them, retiring those two named sub-obligations. -/

/-- `(value + 1) + offset = (value + offset) + 1` — the head successor floats out (local `Nat.succ_add`, structural
on `offset`, `propext`-free). -/
private theorem succAddSwap : (value offset : Nat) → (value + 1) + offset = (value + offset) + 1
  | _, 0 => rfl
  | value, offset + 1 => congrArg Nat.succ (succAddSwap value offset)

/-- `value ≤ value + gap` as a `Nat.ble` — structural on `value` (`propext`-free), the distant-position witness. -/
private theorem natBleAddRight : (value gap : Nat) → Nat.ble value (value + gap) = true
  | 0, _ => rfl
  | value + 1, gap => by rw [succAddSwap value gap]; exact natBleAddRight value gap

/-- ★★ **Disjoint adjacent swaps COMMUTE.**  A swap at `posLow` and a swap at the distant `posLow + gap + 2` (windows
`{posLow, posLow+1}` and `{posLow+gap+2, posLow+gap+3}` disjoint) apply in either order.  Structural on `perm` /
`posLow`; the common head is stripped by `applyAdjacentSwap_cons_succ` and the position bookkeeping by `succAddSwap`.
This is the disjoint-swap-commutation leg named by the r7 residual marker
(`applyAdjacentSwap (perm · s_d) position = applyAdjacentSwap (perm · s_position) d` when `position ≥ d + 2`). -/
theorem applyAdjacentSwap_swap_disjoint :
    (perm : List Nat) → (posLow gap : Nat) →
    applyAdjacentSwap (applyAdjacentSwap perm posLow) (posLow + gap + 2)
      = applyAdjacentSwap (applyAdjacentSwap perm (posLow + gap + 2)) posLow
  | [], _, _ => rfl
  | _ :: [], _, _ => rfl
  | first :: second :: rest, 0, gap => by
      show second :: applyAdjacentSwap (first :: rest) (0 + gap + 1)
          = applyAdjacentSwap (first :: applyAdjacentSwap (second :: rest) (0 + gap + 1)) 0
      rw [applyAdjacentSwap_cons_succ second rest (0 + gap),
        applyAdjacentSwap_cons_succ first rest (0 + gap)]
      rfl
  | first :: second :: rest, posLow + 1, gap => by
      show applyAdjacentSwap (first :: applyAdjacentSwap (second :: rest) posLow) (posLow + 1 + gap + 1 + 1)
          = applyAdjacentSwap (first :: applyAdjacentSwap (second :: rest) (posLow + 1 + gap + 1)) (posLow + 1)
      rw [applyAdjacentSwap_cons_succ first (applyAdjacentSwap (second :: rest) posLow) (posLow + 1 + gap + 1),
        applyAdjacentSwap_cons_succ first (applyAdjacentSwap (second :: rest) (posLow + 1 + gap + 1)) posLow,
        succAddSwap posLow gap]
      exact congrArg (first :: ·) (applyAdjacentSwap_swap_disjoint (second :: rest) posLow gap)

/-- The head of a swap at a POSITIVE position is unchanged — a `position + 1` swap fixes the head (arm 4 / the
singleton no-op).  Structural on `perm`, `propext`-free. -/
private theorem firstEntry_applyAdjacentSwap_succ : (perm : List Nat) → (position : Nat) →
    firstEntry (applyAdjacentSwap perm (position + 1)) = firstEntry perm
  | [], _ => rfl
  | _ :: [], _ => rfl
  | _ :: _ :: _, _ => rfl

/-- ★★ **The leftmost descent is INVARIANT under a DISTANT swap.**  For a non-identity `perm` and a position
`≥ leftmostDescent perm + 2` (strictly past the trailing canonical descent `d` and its partner strand), the swap
touches only strands beyond `d + 1`, so the leftmost descent stays at `d` and the permutation stays non-identity.
Structural on `perm` / `position` (mirrors `leftmostDescent_applyAdjacentSwap_belowDescent`); the head-preservation
`firstEntry_applyAdjacentSwap_succ` keeps the junction descent-free.  This is the leftmost-descent-invariance leg named
by the r7 residual marker (`leftmostDescent (perm · s_position) = d` for `position ≥ d + 2`). -/
theorem leftmostDescent_applyAdjacentSwap_distant :
    (perm : List Nat) → (position : Nat) →
    isIdentityPerm perm = false → Nat.ble (leftmostDescent perm + 2) position = true →
    leftmostDescent (applyAdjacentSwap perm position) = leftmostDescent perm
      ∧ isIdentityPerm (applyAdjacentSwap perm position) = false
  | [], _, nonIdentity, _ => Bool.noConfusion nonIdentity
  | _ :: [], _, nonIdentity, _ => Bool.noConfusion nonIdentity
  | first :: second :: rest, 0, _, distant => Bool.noConfusion distant
  | first :: second :: rest, 1, _, distant => Bool.noConfusion distant
  | first :: second :: rest, position + 2, nonIdentity, distant =>
      match hDescent : Nat.blt second first with
      | true => by
          have ld0 : leftmostDescent (first :: second :: rest) = 0 :=
            condTrue 0 (leftmostDescent (second :: rest) + 1) (Nat.blt second first) hDescent
          refine ⟨?_, ?_⟩
          · show leftmostDescent (first :: applyAdjacentSwap (second :: rest) (position + 1))
                = leftmostDescent (first :: second :: rest)
            rw [applyAdjacentSwap_cons_succ second rest position, ld0]
            exact condTrue 0 (leftmostDescent (second :: applyAdjacentSwap rest position) + 1)
              (Nat.blt second first) hDescent
          · show isIdentityPerm (first :: applyAdjacentSwap (second :: rest) (position + 1)) = false
            rw [applyAdjacentSwap_cons_succ second rest position]
            exact condTrue false (isIdentityPerm (second :: applyAdjacentSwap rest position))
              (Nat.blt second first) hDescent
      | false => by
          have ldSucc : leftmostDescent (first :: second :: rest) = leftmostDescent (second :: rest) + 1 :=
            condFalse 0 (leftmostDescent (second :: rest) + 1) (Nat.blt second first) hDescent
          have identityReduces : isIdentityPerm (first :: second :: rest) = isIdentityPerm (second :: rest) :=
            condFalse false (isIdentityPerm (second :: rest)) (Nat.blt second first) hDescent
          have tailNonIdentity : isIdentityPerm (second :: rest) = false := identityReduces ▸ nonIdentity
          have distantTail : Nat.ble (leftmostDescent (second :: rest) + 2) (position + 1) = true := by
            rw [ldSucc] at distant; exact distant
          have ih := leftmostDescent_applyAdjacentSwap_distant (second :: rest) (position + 1)
            tailNonIdentity distantTail
          have headPreserved : firstEntry (applyAdjacentSwap (second :: rest) (position + 1)) = second :=
            firstEntry_applyAdjacentSwap_succ (second :: rest) position
          have noJunction : Nat.blt (firstEntry (applyAdjacentSwap (second :: rest) (position + 1))) first = false := by
            rw [headPreserved]; exact hDescent
          have ysCons : applyAdjacentSwap (second :: rest) (position + 1)
              = firstEntry (applyAdjacentSwap (second :: rest) (position + 1))
                :: dropFirst (applyAdjacentSwap (second :: rest) (position + 1)) :=
            consEta (applyAdjacentSwap (second :: rest) (position + 1)) rest.length
              (applyAdjacentSwap_length (second :: rest) (position + 1))
          refine ⟨?_, ?_⟩
          · show leftmostDescent (first :: applyAdjacentSwap (second :: rest) (position + 1))
                = leftmostDescent (first :: second :: rest)
            rw [ysCons, leftmostDescent_cons_headBltFalse first
              (firstEntry (applyAdjacentSwap (second :: rest) (position + 1)))
              (dropFirst (applyAdjacentSwap (second :: rest) (position + 1))) noJunction, ← ysCons, ih.1, ldSucc]
          · show isIdentityPerm (first :: applyAdjacentSwap (second :: rest) (position + 1)) = false
            rw [ysCons, isIdentityPerm_cons_headBltFalse first
              (firstEntry (applyAdjacentSwap (second :: rest) (position + 1)))
              (dropFirst (applyAdjacentSwap (second :: rest) (position + 1))) noJunction, ← ysCons, ih.2]

/-! ## WP-BRAUER r8 — the COMMUTE mode, FULL reduction (conditional on the smaller-permutation insertion step)

The COMMUTE local move (`crossingInsertionStep_commute_localReduction`) slides the inserted `position` past the
trailing canonical descent `d`, leaving `canonicalCrossingWord (perm · s_d) ++ [position, d]`.  This lemma completes
the COMMUTE case: GIVEN the insertion step at the strictly-smaller `perm · s_d` (the outer-`inversionCount`-induction
IH), the moved letter re-canonicalises to `canonicalCrossingWord (perm · s_position)`.  The two distant-swap kit
lemmas do the alignment: `applyAdjacentSwap_swap_disjoint` gives `perm · s_d · s_position = perm · s_position · s_d`
and `leftmostDescent_applyAdjacentSwap_distant` gives `leftmostDescent (perm · s_position) = d`, so staircase-snoc on
`perm · s_position` reads its trailing letter as exactly the carried `d`.  The COMMUTE case is thus fully assembled
modulo the IH — the residual is now EXACTLY the BRAID carry fold (the standing wall). -/

/-- ★★ **The insertion step — COMMUTE mode, FULL reduction (conditional on the smaller-permutation insertion step).**
For a non-identity `perm` and a distant `position = leftmostDescent perm + gap + 2`, GIVEN the insertion step at the
strictly-smaller `perm · s_d` (`d = leftmostDescent perm`) — the `inversionCount`-induction hypothesis `ih` — the full
COMMUTE case holds:
`canonicalCrossingWord perm ++ [position] ~ canonicalCrossingWord (perm · s_position)`.  PROOF: the local move
(`crossingInsertionStep_commute_localReduction`) gives `~ canonicalCrossingWord (perm · s_d) ++ [position, d]`; the
IH whiskered right by `[d]` rewrites the `[position]` prefix to `canonicalCrossingWord (perm · s_d · s_position)`; then
`applyAdjacentSwap_swap_disjoint` (`perm · s_d · s_position = perm · s_position · s_d`) and staircase-snoc on
`perm · s_position` (whose leftmost descent is `d` by `leftmostDescent_applyAdjacentSwap_distant`, non-identity by the
same) identify `canonicalCrossingWord (perm · s_position · s_d) ++ [d]` with `canonicalCrossingWord (perm · s_position)`.
The COMMUTE case is assembled modulo the IH; the ONLY remaining leg of `InRangeInsertionStep` is the BRAID carry fold. -/
theorem crossingInsertionStep_commute_full (perm : List Nat) (gap : Nat)
    (nonIdentity : isIdentityPerm perm = false)
    (ih : BrauerConvFree7
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm (leftmostDescent perm))
        ++ [leftmostDescent perm + gap + 2]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm))
        (leftmostDescent perm + gap + 2))))) :
    BrauerConvFree7 (crossingWord (canonicalCrossingWord perm ++ [leftmostDescent perm + gap + 2]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm (leftmostDescent perm + gap + 2)))) := by
  have disjoint : leftmostDescent perm + 2 ≤ leftmostDescent perm + gap + 2 :=
    leOfBleTrue (leftmostDescent perm + 2) (leftmostDescent perm + gap + 2)
      (natBleAddRight (leftmostDescent perm) gap)
  have localMove := crossingInsertionStep_commute_localReduction perm (leftmostDescent perm + gap + 2)
    nonIdentity disjoint
  have swapCommute := applyAdjacentSwap_swap_disjoint perm (leftmostDescent perm) gap
  have ldInvariant := leftmostDescent_applyAdjacentSwap_distant perm (leftmostDescent perm + gap + 2)
    nonIdentity (natBleAddRight (leftmostDescent perm) gap)
  have snocTarget :=
    canonicalCrossingWord_snoc_leftmostDescent (applyAdjacentSwap perm (leftmostDescent perm + gap + 2))
      ldInvariant.2
  rw [ldInvariant.1, ← swapCommute] at snocTarget
  have step2 : BrauerConvFree7
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm (leftmostDescent perm))
        ++ [leftmostDescent perm + gap + 2, leftmostDescent perm]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm))
          (leftmostDescent perm + gap + 2))
        ++ [leftmostDescent perm])) := by
    rw [← appendSnocAssoc (canonicalCrossingWord (applyAdjacentSwap perm (leftmostDescent perm)))
        (leftmostDescent perm + gap + 2) [leftmostDescent perm],
      crossingWord_append (canonicalCrossingWord (applyAdjacentSwap perm (leftmostDescent perm))
        ++ [leftmostDescent perm + gap + 2]) [leftmostDescent perm],
      crossingWord_append (canonicalCrossingWord (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm))
        (leftmostDescent perm + gap + 2))) [leftmostDescent perm]]
    exact BrauerConvFree7.whiskerRight (crossingWord [leftmostDescent perm]) ih
  rw [snocTarget]
  exact BrauerConvFree7.trans localMove step2

/-- Non-vacuity — the GENERAL COMMUTE-full reduction on `[1, 0, 2, 3]` (leftmost descent `0`) inserting the distant `2`
(`gap = 0`).  The smaller permutation `perm · s_0 = [0, 1, 2, 3]` is the identity, so its insertion step `ih` is
reflexivity (`crossingWord [2] ~ crossingWord [2]`), and the theorem then yields
`crossingWord [0, 2] ~ crossingWord [2, 0]` — the distant commute. -/
theorem crossingInsertionStep_commute_full_smoke :
    BrauerConvFree7
      (crossingWord (canonicalCrossingWord [1, 0, 2, 3] ++ [leftmostDescent [1, 0, 2, 3] + 0 + 2]))
      (crossingWord (canonicalCrossingWord
        (applyAdjacentSwap [1, 0, 2, 3] (leftmostDescent [1, 0, 2, 3] + 0 + 2)))) :=
  crossingInsertionStep_commute_full [1, 0, 2, 3] 0 (by decide)
    (BrauerConvFree7.ofFree (BrauerConvFree.refl _))

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

/-- ★ **Honesty marker — the CANCEL mode of the insertion step is CLOSED GENERALLY, with its structural kit.**
`crossingInsertionStep_atLeftmostDescent` proves the insertion step for EVERY non-identity `perm` (arbitrary
`List Nat`) at `position = leftmostDescent perm`: the `[d, d]` R2 cancellation, upgraded from the single
`crossingInsertionStep_cancel_smoke` to a general theorem.  It stands on the reusable, zero-axiom kit landed here:
the staircase-snoc identity `canonicalCrossingWord perm = canonicalCrossingWord (perm · s_d) ++ [d]`
(`canonicalCrossingWord_snoc_leftmostDescent`), the Lehmer measure drop `inversionCount (perm · s_d) + 1 =
inversionCount perm` (`inversionCount_ofLeftmostDescentSwap_succ`), the multiset-invariance leg
`countEntriesBelow_applyAdjacentSwap`, and the propext-free `reverse_cons` (`reverseConsLocal`; Init's leaks
`propext`).  Non-vacuous: `crossingInsertionStep_atLeftmostDescent_smoke` on the reversal `[2, 1, 0]`.

**TWO honest diagnoses this closure exposes about the r5 residual `fxBrauer_hasCrossingInsertionStepGeneralResidual`:**

  1. **The `∀ (perm) (position)` `insertionStep` hypothesis is NOT dischargeable as stated** — it is FALSE for
     out-of-range `position`.  For `perm = [0, 1]`, `position = 5`: `canonicalCrossingWord [0, 1] = []` and
     `applyAdjacentSwap [0, 1] 5 = [0, 1]` (a no-op past the end), so the step reduces to
     `BrauerConvFree7 [crossingAt 5] []` — a lone crossing convertible to the empty word, which no relation
     derives.  The genuinely provable residual is the IN-RANGE step (`position + 1 < perm.length`, where the crossing
     acts); the r5 conditional folds (`crossingOnly_straightens_ofInsertionStep`, …) are correct as conditionals but
     their hypothesis holds only for in-range words.
  2. **Only CANCEL closes at full `List Nat` generality.**  EXTEND (`position < d`, append stays canonical) and
     COMMUTE (`position ≥ d + 2`) additionally need `perm` to be a GENUINE permutation (distinct entries): the EXTEND
     stability `position < leftmostDescent perm → leftmostDescent (applyAdjacentSwap perm position) = position` is
     FALSE for lists with repeats (`[1, 1, 0]`).  BRAID (`position = d + 1`) is the Matsumoto inner induction (the
     `pureCupSpine_sort`-magnitude wall) on top of that permutation structure.

So the residual shrinks to "the IN-RANGE braid mode over genuine permutations"; the master markers
`fxBrauer_hasCrossingOnlyStraightening` / `fxBrauer_hasCrossingStraighteningInsertionResidual` stay `false`.  `= true`. -/
def fxBrauer_hasInsertionCancelMode : Bool := true

/-- ★ **Honesty marker — WP-BRAUER r7: the insertion residual is REFORMULATED honestly, and the fold consumes it.**
The r6 diagnosis proved the r5 `∀ (perm) (position)` hypothesis FALSE out-of-range.  This round defines the GENUINELY
provable residual `InRangeInsertionStep` — quantified only over `isDistinctList` permutations at IN-RANGE positions
(`position + 1 < perm.length`) — and REVISES the fold to consume it (chosen ADDITIVELY: the r5 conditional folds are
KEPT unchanged as honest conditionals; the new `crossingOnly_straightensFueled_wellFormed` /
`crossingOnly_straightens_wellFormed` / `crossingWords_equalPerm_conv_wellFormed` are the reformulated versions whose
hypothesis is TRUE).  The discharge kit is closed zero-axiom: distinctness is preserved by `applyAdjacentSwap`
(`isDistinctList_applyAdjacentSwap`, via `memBool_applyAdjacentSwap`) and true of the identity
(`isDistinctList_range`), so every realized permutation is genuine (`isDistinctList_permuteOfCrossingWord`); the
`wellFormedCrossingWord` predicate guarantees each peeled letter is in range (`lastPosition_inRange_ofWellFormed`).  So
the entire well-formed crossing-only word problem is REDUCED to the single TRUE `InRangeInsertionStep` — no longer a
false hypothesis.  `= true`. -/
def fxBrauer_hasInRangeInsertionReformulation : Bool := true

/-- ★ **Honesty marker — WP-BRAUER r7: the EXTEND mode is CLOSED GENERALLY over genuine permutations.**
`crossingInsertionStep_extend` proves the insertion step for every distinct-entry `perm` and
`position < leftmostDescent perm` by REFLEXIVITY: the swap `perm · s_position` lands its new leftmost descent exactly
at `position` and is non-identity (`leftmostDescent_applyAdjacentSwap_belowDescent`, the structural induction threading
head-monotonicity `firstEntry_applyAdjacentSwap_belowDescent_ge`), so staircase-snoc + the involution
`applyAdjacentSwap_involutive` give `canonicalCrossingWord (perm · s_position) = canonicalCrossingWord perm ++
[position]`.  This is the mechanized `¬IsRightDescent` / `ℓ(ws) = ℓ(w)+1` extend branch of the Björner–Brenti length
dichotomy, driven by the computable ascent test.  The distinctness hypothesis is essential — the marker's named
counterexample `[1, 1, 0]` fails.  Non-vacuous: `crossingInsertionStep_extend_general_smoke` on the 3-cycle
`[1, 2, 0]`.  `= true`. -/
def fxBrauer_hasInsertionExtendMode : Bool := true

/-- ★ **Honesty marker — WP-BRAUER r7: the COMMUTE mode's LOCAL Coxeter step is SHIPPED (general, IH-free).**
`crossingInsertionStep_commute_localReduction` proves, for any non-identity `perm` and a distant
`position ≥ leftmostDescent perm + 2`, that the inserted letter commutes past the trailing canonical descent `d`:
`canonicalCrossingWord perm ++ [position] ~ canonicalCrossingWord (perm · s_d) ++ [position, d]` (staircase-snoc +
`crossingCommuteFree`).  This is the single `|a − b| ≥ 2` commutation move of the mode; the residual it leaves,
`canonicalCrossingWord (perm · s_d) ++ [position]`, is an insertion at the strictly-smaller permutation `perm · s_d`
(`inversionCount` dropped one), which the FULL COMMUTE mode discharges by the outer `inversionCount` induction — the IH
that only closes once the BRAID mode does (see the residual marker below).  Non-vacuous:
`crossingInsertionStep_commute_localReduction_smoke` on `[1, 0, 2, 3]`.  `= true`. -/
def fxBrauer_hasInsertionCommuteLocalMove : Bool := true

/-- ★ **Honesty marker — WP-BRAUER r8: the BRAID mode's LOCAL Coxeter step is SHIPPED (Regime B, general, IH-free).**
`crossingInsertionStep_braid_localReduction` proves, for any `perm` with leftmost descent `d` and once-bubbled
`perm · s_d` both non-identity and `leftmostDescent (perm · s_d) = d + 1` (Regime B, the recon's tail-local dichotomy
branch), that the inserted `s_{d+1}` braids past the trailing canonical `s_d s_{d+1}`:
`canonicalCrossingWord perm ++ [d+1] ~ canonicalCrossingWord (perm · s_d · s_{d+1}) ++ [d, d+1, d]` (two staircase-snocs
exposing the trailing `s_{d+1} s_d s_{d+1}`, then `crossingBraidFree d` symm whiskered left).  This is the single
Coxeter BRAID move of the mode — the FIRST general artifact on the standing BRAID wall itself (the analog of the
shipped COMMUTE local reduction).  The residual it leaves, `canonicalCrossingWord (perm · s_d · s_{d+1}) ++ [d, d+1, d]`,
re-inserts the moved `[d, d+1, d]` leftward through the shorter prefix — the CARRY, whose fold is the standing
lexicographic wall (see the residual marker).  Non-vacuous: `crossingInsertionStep_braid_localReduction_smoke` on the
reversal `[2, 1, 0]`.  `= true`. -/
def fxBrauer_hasInsertionBraidLocalMove : Bool := true

/-- ★ **Honesty marker — WP-BRAUER r8: the DISTANT-SWAP KIT is SHIPPED (the two structural lemmas the r7 residual
marker named).**  The outer `inversionCount` insertion induction re-inserts `position` at the strictly-smaller
`perm · s_d`, which needs two facts about a distant swap (`position ≥ d + 2`), BOTH named as missing structural
inductions in the r7 residual: (1) disjoint adjacent swaps COMMUTE — `applyAdjacentSwap_swap_disjoint`
(`perm · s_d · s_position = perm · s_position · s_d`), structural on `perm` / `posLow`, head stripped by
`applyAdjacentSwap_cons_succ` and positions bookkept by the local `succAddSwap`; and (2) the leftmost descent is
INVARIANT under a distant swap — `leftmostDescent_applyAdjacentSwap_distant` (`leftmostDescent (perm · s_position) = d`
and `perm · s_position` non-identity), structural on `perm` (mirroring `leftmostDescent_applyAdjacentSwap_belowDescent`)
with head-preservation `firstEntry_applyAdjacentSwap_succ`.  Both closed zero-axiom, retiring the two named
sub-obligations.  `= true`. -/
def fxBrauer_hasDistantSwapKit : Bool := true

/-- ★ **Honesty marker — WP-BRAUER r8: the COMMUTE mode's FULL reduction is CLOSED (conditional on the smaller-perm
insertion step).**  `crossingInsertionStep_commute_full` completes the COMMUTE case: for a distant
`position = d + gap + 2`, GIVEN the insertion step at the strictly-smaller `perm · s_d` (the exact
`inversionCount`-induction hypothesis), `canonicalCrossingWord perm ++ [position] ~ canonicalCrossingWord (perm ·
s_position)`.  It chains the shipped local move (`crossingInsertionStep_commute_localReduction`) with the IH whiskered
by `[d]`, then closes with the distant-swap kit: `applyAdjacentSwap_swap_disjoint` commutes the two swaps and
`leftmostDescent_applyAdjacentSwap_distant` makes the trailing canonical letter of `perm · s_position` exactly the
carried `d`, so staircase-snoc identifies the two sides.  This assembles the COMMUTE case in full modulo the IH — so
the residual now shrinks to EXACTLY the BRAID carry fold.  Non-vacuous: `crossingInsertionStep_commute_full_smoke` on
`[1, 0, 2, 3]` (the smaller perm is the identity, so `ih` is reflexivity, and the theorem yields the distant commute
`crossingWord [0, 2] ~ crossingWord [2, 0]`).  `= true`. -/
def fxBrauer_hasInsertionCommuteFullMode : Bool := true

/-- **Honesty marker — the FULL insertion step stays `false`; after r8 the residual is EXACTLY the BRAID CARRY FOLD.**
Of the four modes of the honest `InRangeInsertionStep` (in-range, genuine permutations), THREE now close as general
theorems and the fourth's local step ships:

  * CANCEL (`crossingInsertionStep_atLeftmostDescent`, `position = d`) — general, R2;
  * EXTEND (`crossingInsertionStep_extend`, `position < d`) — general, reflexivity;
  * COMMUTE (`position ≥ d + 2`) — the local Coxeter step is general (`crossingInsertionStep_commute_localReduction`)
    AND the FULL COMMUTE case is now assembled MODULO the IH (`crossingInsertionStep_commute_full`), using the r8
    distant-swap kit `applyAdjacentSwap_swap_disjoint` + `leftmostDescent_applyAdjacentSwap_distant` (the two structural
    inductions the r7 residual named — now SHIPPED);
  * BRAID (`position = d + 1`) — the local Coxeter step ships (`crossingInsertionStep_braid_localReduction`, Regime B:
    `s_{d+1} s_d s_{d+1} → s_d s_{d+1} s_d`).

So after r8 the two structural sub-obligations the r7 marker named (distant-swap commutation, leftmost-descent
invariance) are DISCHARGED, and the COMMUTE case is fully reduced to the IH.  The SOLE remaining leg of
`InRangeInsertionStep` (hence the flip of `fxBrauer_hasCrossingOnlyStraightening`) is the **BRAID CARRY FOLD**: the
local braid move leaves `canonicalCrossingWord (perm · s_d · s_{d+1}) ++ [d, d+1, d]`, whose trailing `[d, d+1, d]`
re-inserts leftward through the shorter prefix.  The recon's hand-verified dichotomy is the exact jam: in Regime B
(`d2 = d + 1`) the carry is tail-local (braid, then meet the next run and braid/cancel again), but in Regime A
(`d2 = d - 1`) the moved letter is stuck at the tail and must FIRST commute into the canonical prefix (hand-example:
`[2, 0, 1, 2]`, the only legal move is `commute(2, 0)` at the FRONT) before it can braid — so the carry is NOT
tail-local, the recursion is NOT on `inversionCount` (braiding preserves it), and the measure is the secondary
lexicographic `(inversionCount perm, carried-index / prefix-length)`.  This is the standing jam — the
`locateAux` / `pureCupSpine_sort`-magnitude induction (the 1300-line zero-axiom sibling).  The master markers
`fxBrauer_hasCrossingOnlyStraightening` (`Brauer/WiringDescStandardForm.lean`) and
`fxBrauer_hasCrossingStraighteningInsertionResidual` (`Brauer/WiringDescStraightening.lean`) stay `false` because of it
— a route/measure gap, not an obstruction (Lehrer–Zhang Thm 2.6(2): the seven relations DO present the category).
`= false`. -/
def fxBrauer_hasCrossingInsertionStepGeneralResidual : Bool := false

/-! ## WP-BRAUER r9 — the CARRY FOLD outer strong induction: `InRangeInsertionStep` reduced to ONE braid-ascent leaf

The r8 markers assembled CANCEL / EXTEND / COMMUTE (the last modulo the outer `inversionCount` IH) and shipped the
BRAID local Coxeter step, leaving "the braid carry fold" as the residual.  This round CLOSES the outer strong
induction: a structural-fuel recursion on `inversionCount perm` that dispatches EVERY `(perm, position)` case of the
honest `InRangeInsertionStep`, discharging all of them EXCEPT one sharply-characterised braid leaf — the
`BraidAscentInsertionStep` residual (`position = leftmostDescent perm + 1`, an ASCENT there, and the inserted swap does
NOT itself become the new leftmost descent).  So the ENTIRE in-range crossing-only word problem is now reduced, by a
CLOSED machine-checked induction, to that single leaf.

The census sharpening (Python ground truth, permutations of `range n`, `n = 2..6`): of the 547 braid cases
(`position = d + 1`, ascent), 242 have `leftmostDescent (perm · s_{d+1}) = d + 1` and close by pure REFLEXIVITY
(`crossingInsertionStep_reflex`, the r9 general form of EXTEND — the swap lands its new leftmost descent exactly at the
inserted position, so the canonical word simply extends).  Only the remaining 305 (`leftmostDescent (perm · s_{d+1}) = d`
— the target keeps its leftmost descent at `d`) are the true wall: there the moved `[d, d+1]` must sweep leftward into
the canonical prefix before it can braid, a distinguished-active-letter induction of `pureCupSpine_sort` magnitude with
NO literal `inversionCount` / carried-index / regional monovariant descending per shipped-move step (the recon's
machine-documented plateau; consistent with Björner–Brenti / Little's "defect row" hand-argument, which has no
drop-in mechanized precedent — mathlib's `CoxeterSystem` proves only the weak exchange property).

New this round: the general reflexivity lemma `canonicalCrossingWord_snoc_ofNewLeftmostDescent` + its convertibility
corollary `crossingInsertionStep_reflex` (closes the 242 braid-reflex cases AND the identity base); the descent lemma
`crossingInsertionStep_ofInvolutionIH` (any position whose swap DROPS the inversion count reduces to the IH at the
smaller permutation via the involution + one R2 cancel); the identity-range EXTEND bridge
`leftmostDescent_gt_ofIdentityInRange`; the `inversionCount = 0 → identity` base fact; and the outer fuel recursion
`inRangeInsertionStepFueled_ofBraidAscent` assembling them into `inRangeInsertionStep_ofBraidAscent :
BraidAscentInsertionStep → InRangeInsertionStep`.

Raw Lean 4 + Init; structural fuel on `inversionCount`; no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`. -/

/-- `value + 1 ≠ 0` — structural (`Nat.noConfusion` on the successor), avoiding the `propext`-tainted
`Nat.succ_ne_zero`. -/
private theorem natSuccNeZeroLocal : (value : Nat) → ¬ (value + 1 = 0)
  | _, succEqZero => Nat.noConfusion succEqZero

/-- `value ≤ 0 → value = 0` — structural, `propext`-free. -/
private theorem natEqZeroOfLeZero : (value : Nat) → value ≤ 0 → value = 0
  | 0, _ => rfl
  | _ + 1, succLeZero => absurd succLeZero (Nat.not_succ_le_zero _)

/-- ★ **`inversionCount perm = 0 ⟹ perm is the identity`** — the base fact of the outer fuel recursion.  If `perm`
had a descent, the leftmost-descent swap would witness `inversionCount perm = inversionCount (perm · s_d) + 1 ≠ 0`
(`inversionCount_ofLeftmostDescentSwap_succ`).  Structural via the shipped Lehmer drop. -/
theorem isIdentityPerm_ofInversionCountZero (perm : List Nat) (invZero : inversionCount perm = 0) :
    isIdentityPerm perm = true := by
  match hId : isIdentityPerm perm with
  | true => rfl
  | false =>
      have drop := inversionCount_ofLeftmostDescentSwap_succ perm hId
      rw [invZero] at drop
      exact absurd drop (natSuccNeZeroLocal _)

/-- ★ **For an identity (ascending) permutation, every in-range position is strictly below the leftmost descent.**
`leftmostDescent` of an ascending list is `length - 1` (it steps to the end), so `position + 1 < length` forces
`position < leftmostDescent perm`.  This is the bridge that lets the general EXTEND theorem
(`crossingInsertionStep_extend`) close the IDENTITY BASE of the fuel recursion (canonical word empty; the swap creates a
fresh descent exactly at `position`).  Structural on `perm` / `position`. -/
theorem leftmostDescent_gt_ofIdentityInRange : (perm : List Nat) → (position : Nat) →
    isIdentityPerm perm = true → position + 1 < perm.length →
    Nat.blt position (leftmostDescent perm) = true
  | [], position, _, inRange => absurd inRange (Nat.not_lt_zero (position + 1))
  | _ :: [], position, _, inRange =>
      absurd (Nat.lt_of_succ_lt_succ inRange) (Nat.not_lt_zero position)
  | first :: second :: rest, position, hId, inRange =>
      match hDescent : Nat.blt second first with
      | true => by
          exact Bool.noConfusion
            (hId.symm.trans (condTrue false (isIdentityPerm (second :: rest)) (Nat.blt second first) hDescent))
      | false => by
          have tailId : isIdentityPerm (second :: rest) = true :=
            (isIdentityPerm_cons_headBltFalse first second rest hDescent).symm.trans hId
          rw [leftmostDescent_cons_headBltFalse first second rest hDescent]
          match position with
          | 0 => rfl
          | predPosition + 1 =>
              have inRangeTail : predPosition + 1 < (second :: rest).length :=
                Nat.lt_of_succ_lt_succ inRange
              show Nat.blt (predPosition + 1) (leftmostDescent (second :: rest) + 1) = true
              exact leftmostDescent_gt_ofIdentityInRange (second :: rest) predPosition tailId inRangeTail

/-- ★★ **General reflexivity — the inserted swap becomes the NEW leftmost descent, so the canonical word simply
EXTENDS.**  When `applyAdjacentSwap perm position` is non-identity with its leftmost descent exactly at `position`, the
staircase-snoc identity peels that descent and the involution `perm · s_position · s_position = perm` collapses the
prefix: `canonicalCrossingWord (perm · s_position) = canonicalCrossingWord perm ++ [position]`.  Generalises the
shipped `crossingInsertionStep_extend` (which derives the descent-landing from `position < leftmostDescent perm`) to
take the landing as a hypothesis — so it covers BOTH the identity base and the braid-ascent `leftmostDescent (perm ·
s_{d+1}) = d + 1` cases. -/
theorem canonicalCrossingWord_snoc_ofNewLeftmostDescent (perm : List Nat) (position : Nat)
    (nonIdSwapped : isIdentityPerm (applyAdjacentSwap perm position) = false)
    (newDescent : leftmostDescent (applyAdjacentSwap perm position) = position) :
    canonicalCrossingWord (applyAdjacentSwap perm position)
      = canonicalCrossingWord perm ++ [position] := by
  have snoc := canonicalCrossingWord_snoc_leftmostDescent (applyAdjacentSwap perm position) nonIdSwapped
  rw [newDescent, applyAdjacentSwap_involutive perm position] at snoc
  exact snoc

/-- ★★ **The insertion step — REFLEX mode.**  Under the descent-landing hypothesis of
`canonicalCrossingWord_snoc_ofNewLeftmostDescent`, the insertion step holds by pure reflexivity (appending `position`
IS the canonical word of the swap).  This closes the identity base of the fuel recursion and the 242 braid-ascent cases
whose swap keeps its new leftmost descent at the inserted position. -/
theorem crossingInsertionStep_reflex (perm : List Nat) (position : Nat)
    (nonIdSwapped : isIdentityPerm (applyAdjacentSwap perm position) = false)
    (newDescent : leftmostDescent (applyAdjacentSwap perm position) = position) :
    BrauerConvFree7 (crossingWord (canonicalCrossingWord perm ++ [position]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm position))) := by
  rw [canonicalCrossingWord_snoc_ofNewLeftmostDescent perm position nonIdSwapped newDescent]
  exact BrauerConvFree7.ofFree (BrauerConvFree.refl _)

/-- ★★ **The insertion step — DESCENT reduction (via the involution IH).**  If the reverse insertion step is known —
`canonicalCrossingWord (perm · s_position) ++ [position] ~ canonicalCrossingWord perm` (the IH at the strictly-smaller
`perm · s_position`, whose target is `perm` by involution) — then the forward step follows: whisker the IH by
`[position]` and collapse the trailing `[position, position]` by R2.  This is how EVERY position whose swap DROPS the
inversion count (a right descent) reduces to the IH at the smaller permutation.  IH-form input, no permutation-side
condition. -/
theorem crossingInsertionStep_ofInvolutionIH (perm : List Nat) (position : Nat)
    (ih : BrauerConvFree7
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm position) ++ [position]))
      (crossingWord (canonicalCrossingWord perm))) :
    BrauerConvFree7 (crossingWord (canonicalCrossingWord perm ++ [position]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm position))) := by
  have cancelTail : BrauerConvFree7
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm position) ++ [position, position]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm position))) := by
    rw [crossingWord_append (canonicalCrossingWord (applyAdjacentSwap perm position)) [position, position]]
    have base := BrauerConvFree7.whiskerLeft
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm position)))
      (crossingCancelFree position)
    rw [appendNilLocal (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm position)))] at base
    exact base
  refine BrauerConvFree7.trans ?_ cancelTail
  have step := BrauerConvFree7.whiskerRight (crossingWord [position]) (BrauerConvFree7.symm ih)
  rw [← crossingWord_append (canonicalCrossingWord perm) [position],
    ← crossingWord_append (canonicalCrossingWord (applyAdjacentSwap perm position) ++ [position]) [position],
    appendSnocAssoc (canonicalCrossingWord (applyAdjacentSwap perm position)) position [position]] at step
  exact step

/-- Not below the leftmost descent forces non-identity — the contrapositive of `leftmostDescent_gt_ofIdentityInRange`
(an identity permutation puts every in-range position strictly below its leftmost descent).  So the fuel recursion,
having routed the `< leftmostDescent` positions to EXTEND, may treat the remaining permutation as non-identity. -/
theorem isIdentityPerm_eq_false_ofNotBelowLeftmost (perm : List Nat) (position : Nat)
    (inRange : position + 1 < perm.length)
    (notBelow : Nat.blt position (leftmostDescent perm) = false) :
    isIdentityPerm perm = false := by
  match hId : isIdentityPerm perm with
  | false => rfl
  | true =>
      exact Bool.noConfusion
        (notBelow.symm.trans (leftmostDescent_gt_ofIdentityInRange perm position hId inRange))

/-- ★★ **The sharp braid-ascent residual — the SINGLE remaining leaf of `InRangeInsertionStep`.**  A genuine
(distinct-entry) NON-IDENTITY permutation with its leftmost descent `d`, an in-range insert at `position = d + 1` that
is NOT the reflex case (the swap `perm · s_{d+1}` does not itself land its new leftmost descent at `d + 1`) and NOT a
descent (the swap does not drop the inversion count — an ascent at `d + 1`).  Concretely (census): exactly the
`leftmostDescent (perm · s_{d+1}) = d` braid cases, where the inserted `[d, d+1]` must sweep leftward into the canonical
prefix before it can braid.  The recon's machine-documented plateau: no literal `inversionCount` / carried-index /
regional monovariant descends per shipped-move step; the termination is carried by the distinguished-active-letter
position, a `pureCupSpine_sort`-magnitude induction.  This is the honest wall; every OTHER case is discharged by the
closed fuel recursion below. -/
def BraidAscentInsertionStep : Prop :=
  ∀ (perm : List Nat),
    isDistinctList perm = true →
    isIdentityPerm perm = false →
    leftmostDescent perm + 1 + 1 < perm.length →
    (Nat.beq (leftmostDescent (applyAdjacentSwap perm (leftmostDescent perm + 1))) (leftmostDescent perm + 1)
      && not (isIdentityPerm (applyAdjacentSwap perm (leftmostDescent perm + 1)))) = false →
    Nat.blt (inversionCount (applyAdjacentSwap perm (leftmostDescent perm + 1))) (inversionCount perm) = false →
    BrauerConvFree7 (crossingWord (canonicalCrossingWord perm ++ [leftmostDescent perm + 1]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm (leftmostDescent perm + 1))))

/-- ★★★ **The OUTER STRONG-INDUCTION FOLD — `InRangeInsertionStep` reduced to `BraidAscentInsertionStep`.**  Structural
fuel on `inversionCount perm`.  Every `(perm, position)` case is discharged:

  * **base / EXTEND** (`position < leftmostDescent perm`, includes the identity base where every in-range position is
    below the leftmost descent) — the general reflexivity EXTEND `crossingInsertionStep_extend`;
  * **CANCEL** (`position = leftmostDescent perm`) — the shipped `crossingInsertionStep_atLeftmostDescent`;
  * **COMMUTE** (`position ≥ leftmostDescent perm + 2`) — the shipped `crossingInsertionStep_commute_full` fed the IH
    at the strictly-smaller `perm · s_d` (`inversionCount` dropped one, `inversionCount_ofLeftmostDescentSwap_succ`);
  * **REFLEX** (`position = leftmostDescent perm + 1` and the swap lands its new leftmost descent there) — the r9
    `crossingInsertionStep_reflex`;
  * **DESCENT** (`position = leftmostDescent perm + 1`, the swap DROPS `inversionCount`) — the r9
    `crossingInsertionStep_ofInvolutionIH` fed the IH at the strictly-smaller swap;
  * **RESIDUAL** (`position = leftmostDescent perm + 1`, ascent, non-reflex) — the `BraidAscentInsertionStep`
    hypothesis (the honest wall; NO recursive call — pure Coxeter at constant realised permutation).

So `InRangeInsertionStep` is CLOSED modulo the single braid-ascent leaf, by a machine-checked induction on the Lehmer
measure. -/
theorem inRangeInsertionStepFueled_ofBraidAscent (residual : BraidAscentInsertionStep) :
    (fuel : Nat) → (perm : List Nat) → (position : Nat) →
    inversionCount perm ≤ fuel → isDistinctList perm = true → position + 1 < perm.length →
    BrauerConvFree7 (crossingWord (canonicalCrossingWord perm ++ [position]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm position)))
  | 0, perm, position, invLe, distinct, inRange => by
      have invZero : inversionCount perm = 0 := natEqZeroOfLeZero _ invLe
      have hId : isIdentityPerm perm = true := isIdentityPerm_ofInversionCountZero perm invZero
      exact crossingInsertionStep_extend perm position distinct
        (leftmostDescent_gt_ofIdentityInRange perm position hId inRange)
  | fuel + 1, perm, position, invLe, distinct, inRange => by
      match hlt : Nat.blt position (leftmostDescent perm) with
      | true =>
          exact crossingInsertionStep_extend perm position distinct hlt
      | false =>
          have hId : isIdentityPerm perm = false :=
            isIdentityPerm_eq_false_ofNotBelowLeftmost perm position inRange hlt
          match hbeq : Nat.beq position (leftmostDescent perm) with
          | true =>
              have hpd : position = leftmostDescent perm := natEqOfBeq position (leftmostDescent perm) hbeq
              rw [hpd]
              exact crossingInsertionStep_atLeftmostDescent perm hId
          | false =>
              have dLePos : leftmostDescent perm ≤ position :=
                leOfBleTrue (leftmostDescent perm) position (bleOfNotBltSwap (leftmostDescent perm) position hlt)
              have dLtPos : leftmostDescent perm < position :=
                ltOfBltTrue (leftmostDescent perm) position
                  (bltOfBleNeq (leftmostDescent perm) position
                    (bleOfNotBltSwap (leftmostDescent perm) position hlt)
                    ((natBeqSymm position (leftmostDescent perm)).symm.trans hbeq))
              match hlt2 : Nat.blt (leftmostDescent perm + 1) position with
              | true =>
                  have hle : leftmostDescent perm + 2 ≤ position :=
                    ltOfBltTrue (leftmostDescent perm + 1) position hlt2
                  obtain ⟨gap, hgap⟩ := Nat.le.dest hle
                  have hpos : position = leftmostDescent perm + gap + 2 :=
                    hgap.symm.trans (Nat.add_right_comm (leftmostDescent perm) 2 gap)
                  have invDrop := inversionCount_ofLeftmostDescentSwap_succ perm hId
                  have succLe : inversionCount (applyAdjacentSwap perm (leftmostDescent perm)) + 1 ≤ fuel + 1 := by
                    rw [invDrop]; exact invLe
                  have invLeSwap : inversionCount (applyAdjacentSwap perm (leftmostDescent perm)) ≤ fuel :=
                    Nat.le_of_succ_le_succ succLe
                  have inRangeSwap : leftmostDescent perm + gap + 2 + 1
                      < (applyAdjacentSwap perm (leftmostDescent perm)).length := by
                    rw [applyAdjacentSwap_length perm (leftmostDescent perm), ← hpos]; exact inRange
                  have ih := inRangeInsertionStepFueled_ofBraidAscent residual fuel
                    (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + gap + 2)
                    invLeSwap (isDistinctList_applyAdjacentSwap perm (leftmostDescent perm) distinct) inRangeSwap
                  rw [hpos]
                  exact crossingInsertionStep_commute_full perm gap hId ih
              | false =>
                  have posLeD1 : position ≤ leftmostDescent perm + 1 :=
                    leOfBleTrue position (leftmostDescent perm + 1)
                      (bleOfNotBltSwap position (leftmostDescent perm + 1) hlt2)
                  have hp1 : position = leftmostDescent perm + 1 := Nat.le_antisymm posLeD1 dLtPos
                  rw [hp1]
                  match hreflex : (Nat.beq (leftmostDescent (applyAdjacentSwap perm (leftmostDescent perm + 1)))
                                    (leftmostDescent perm + 1)
                                  && not (isIdentityPerm (applyAdjacentSwap perm (leftmostDescent perm + 1)))) with
                  | true =>
                      have newDescent : leftmostDescent (applyAdjacentSwap perm (leftmostDescent perm + 1))
                          = leftmostDescent perm + 1 :=
                        natEqOfBeq _ _ (boolAndTrueLeft _ _ hreflex)
                      have nonIdSwapped :
                          isIdentityPerm (applyAdjacentSwap perm (leftmostDescent perm + 1)) = false :=
                        eqFalseOfNotTrue _ (boolAndTrueRight _ _ hreflex)
                      exact crossingInsertionStep_reflex perm (leftmostDescent perm + 1) nonIdSwapped newDescent
                  | false =>
                      match hdesc : Nat.blt (inversionCount (applyAdjacentSwap perm (leftmostDescent perm + 1)))
                                      (inversionCount perm) with
                      | true =>
                          have invLtPerm : inversionCount (applyAdjacentSwap perm (leftmostDescent perm + 1))
                              < inversionCount perm := ltOfBltTrue _ _ hdesc
                          have invLeSwap :
                              inversionCount (applyAdjacentSwap perm (leftmostDescent perm + 1)) ≤ fuel :=
                            Nat.le_of_lt_succ (Nat.lt_of_lt_of_le invLtPerm invLe)
                          have inRangeSwap : leftmostDescent perm + 1 + 1
                              < (applyAdjacentSwap perm (leftmostDescent perm + 1)).length := by
                            rw [applyAdjacentSwap_length perm (leftmostDescent perm + 1), ← hp1]; exact inRange
                          have ih := inRangeInsertionStepFueled_ofBraidAscent residual fuel
                            (applyAdjacentSwap perm (leftmostDescent perm + 1)) (leftmostDescent perm + 1)
                            invLeSwap
                            (isDistinctList_applyAdjacentSwap perm (leftmostDescent perm + 1) distinct) inRangeSwap
                          rw [applyAdjacentSwap_involutive perm (leftmostDescent perm + 1)] at ih
                          exact crossingInsertionStep_ofInvolutionIH perm (leftmostDescent perm + 1) ih
                      | false =>
                          exact residual perm distinct hId (hp1 ▸ inRange) hreflex hdesc

/-- ★★★ **`InRangeInsertionStep` holds GIVEN the braid-ascent residual.**  The un-fuelled outer reduction: the entire
in-range crossing-only word problem over genuine permutations is `BrauerConvFree7`-decided modulo the single
`BraidAscentInsertionStep` leaf.  Start the fuel at `inversionCount perm`. -/
theorem inRangeInsertionStep_ofBraidAscent (residual : BraidAscentInsertionStep) : InRangeInsertionStep :=
  fun perm position distinct inRange =>
    inRangeInsertionStepFueled_ofBraidAscent residual (inversionCount perm) perm position
      (Nat.le_refl _) distinct inRange

/-- ★★ **The symmetric-group WORD PROBLEM (well-formed scope), reduced to the braid-ascent leaf.**  Combining the outer
reduction with the r7 well-formed fold: two well-formed crossing words with equal realised permutation are
`BrauerConvFree7`-convertible GIVEN `BraidAscentInsertionStep`.  When that single leaf closes, this becomes
unconditional and `fxBrauer_hasCrossingOnlyStraightening` flips. -/
theorem crossingWords_equalPerm_conv_ofBraidAscent (bottomCount : Nat) (residual : BraidAscentInsertionStep)
    (wordLeft wordRight : List Nat)
    (wfLeft : wellFormedCrossingWord bottomCount wordLeft = true)
    (wfRight : wellFormedCrossingWord bottomCount wordRight = true)
    (permEq : permuteOfCrossingWord bottomCount wordLeft = permuteOfCrossingWord bottomCount wordRight) :
    BrauerConvFree7 (crossingWord wordLeft) (crossingWord wordRight) :=
  crossingWords_equalPerm_conv_wellFormed bottomCount (inRangeInsertionStep_ofBraidAscent residual)
    wordLeft wordRight wfLeft wfRight permEq

/-! ### r9 non-vacuity — the residual leaf is a genuine, inhabited obligation, and the hard pairs are convertible -/

/-- Non-vacuity — the braid pair `[0,1,0] ~ [1,0,1]` is convertible (the smallest R3 witness), and the two words have
equal permutation.  The canonical non-trivial instance of the reduced word problem. -/
theorem crossingWords_conv_braidPair_r9 :
    permuteOfCrossingWord 3 [0, 1, 0] = permuteOfCrossingWord 3 [1, 0, 1]
      ∧ BrauerConvFree7 (crossingWord [0, 1, 0]) (crossingWord [1, 0, 1]) :=
  ⟨by decide, crossingBraidFree 0⟩

/-- Non-vacuity — the S_4 reversal (longest element, length 6): two reduced words `[0,1,0,2,1,0]` and `[1,0,1,2,1,0]`
for `[3,2,1,0]` are convertible by a single front braid `s_0 s_1 s_0 → s_1 s_0 s_1` whiskered by the common tail. -/
theorem crossingWords_conv_fourReversal :
    permuteOfCrossingWord 4 [0, 1, 0, 2, 1, 0] = permuteOfCrossingWord 4 [1, 0, 1, 2, 1, 0]
      ∧ BrauerConvFree7 (crossingWord [0, 1, 0, 2, 1, 0]) (crossingWord [1, 0, 1, 2, 1, 0]) := by
  refine ⟨by decide, ?_⟩
  show BrauerConvFree7 [crossingAt 0, crossingAt 1, crossingAt 0, crossingAt 2, crossingAt 1, crossingAt 0]
    [crossingAt 1, crossingAt 0, crossingAt 1, crossingAt 2, crossingAt 1, crossingAt 0]
  exact BrauerConvFree7.whiskerRight [crossingAt 2, crossingAt 1, crossingAt 0] (crossingBraidFree 0)

/-- ★★ **Non-vacuity — the r8 STUCK EXAMPLE `[2,0,1,2] ~ [0,1,2,1]` (the residual leaf conclusion) IS convertible.**  The
recon's `commute(2,0)`-at-the-front then `braid(1)` path, realized as `BrauerConvFree7`: the distant commute slides the
leading `s_2` past `s_0`, then the trailing `s_2 s_1 s_2` braids to `s_1 s_2 s_1`.  Both words realize `[1,3,2,0]` on 4
strands. -/
theorem crossingWords_conv_residualStuckExample :
    permuteOfCrossingWord 4 [2, 0, 1, 2] = permuteOfCrossingWord 4 [0, 1, 2, 1]
      ∧ BrauerConvFree7 (crossingWord [2, 0, 1, 2]) (crossingWord [0, 1, 2, 1]) := by
  refine ⟨by decide, ?_⟩
  show BrauerConvFree7 [crossingAt 2, crossingAt 0, crossingAt 1, crossingAt 2]
    [crossingAt 0, crossingAt 1, crossingAt 2, crossingAt 1]
  refine BrauerConvFree7.trans
    (BrauerConvFree7.whiskerRight [crossingAt 1, crossingAt 2]
      (BrauerConvFree7.symm (crossingCommuteFree 0 2 (by decide)))) ?_
  exact BrauerConvFree7.whiskerLeft [crossingAt 0] (BrauerConvFree7.symm (crossingBraidFree 1))

/-- ★★ **Non-vacuity — the braid-ascent residual is a GENUINE, SATISFIABLE obligation (not vacuous).**  The concrete
genuine permutation `[1,3,0,2]` HITS the residual leaf: it is distinct, non-identity, in-range at
`position = leftmostDescent + 1 = 2`, and there both residual side-conditions hold (the swap `[1,3,2,0]` does NOT land
its leftmost descent at `2` — it is at `1` — and does NOT drop the inversion count — `3 → 4`, an ascent).  So
`BraidAscentInsertionStep` quantifies over a non-empty domain of genuine stuck configurations. -/
theorem braidAscentResidual_hypotheses_inhabited :
    isDistinctList [1, 3, 0, 2] = true
      ∧ isIdentityPerm [1, 3, 0, 2] = false
      ∧ leftmostDescent [1, 3, 0, 2] + 1 + 1 < ([1, 3, 0, 2] : List Nat).length
      ∧ (Nat.beq (leftmostDescent (applyAdjacentSwap [1, 3, 0, 2] (leftmostDescent [1, 3, 0, 2] + 1)))
            (leftmostDescent [1, 3, 0, 2] + 1)
          && not (isIdentityPerm (applyAdjacentSwap [1, 3, 0, 2] (leftmostDescent [1, 3, 0, 2] + 1)))) = false
      ∧ Nat.blt (inversionCount (applyAdjacentSwap [1, 3, 0, 2] (leftmostDescent [1, 3, 0, 2] + 1)))
            (inversionCount [1, 3, 0, 2]) = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ★★ **Non-vacuity — the residual leaf for `[1,3,0,2]` IS the r8 stuck example.**  Its residual conclusion is exactly
`crossingWord [2,0,1,2] ~ crossingWord [0,1,2,1]` (canonical word `[2,0,1]` snoc `2`, target canonical word `[0,1,2,1]`)
— the pair `crossingWords_conv_residualStuckExample` independently witnesses convertible.  So the single open leaf is a
real relation about a real configuration whose truth is already exhibited on its hardest small instance; the wall is a
route/measure gap, not an obstruction. -/
theorem braidAscentResidual_conclusion_isStuckExample :
    canonicalCrossingWord [1, 3, 0, 2] ++ [leftmostDescent [1, 3, 0, 2] + 1] = [2, 0, 1, 2]
      ∧ canonicalCrossingWord (applyAdjacentSwap [1, 3, 0, 2] (leftmostDescent [1, 3, 0, 2] + 1)) = [0, 1, 2, 1] := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## WP-BRAUER r10 — the BRAID CARRY ALGEBRA: the list-level braid relation and its five-fold collapse

The braid-ascent leaf's only shipped local move (`crossingInsertionStep_braid_localReduction`, Regime B) leaves the
trailing triple `[d, d+1, d]` to re-insert leftward — the CARRY.  This round ships the ALGEBRAIC core of that carry:
the braid relation `s_d s_{d+1} s_d = s_{d+1} s_d s_{d+1}` realized on the ONE-LINE permutation itself
(`applyAdjacentSwap_braid`), and its FIVE-FOLD collapse `s_d s_{d+1} s_d s_{d+1} s_d = s_{d+1}`
(`applyAdjacentSwap_braid_fivefold`).  The five-fold is exactly the Little-bump / column-insertion identity that makes
the carry LAND: re-inserting `[d, d+1, d]` into `perm · s_d · s_{d+1}` (three adjacent swaps `s_d s_{d+1} s_d`) followed
by the two swaps `s_{d+1} s_d` already present from the two staircase peels reaches
`perm · s_d · s_{d+1} · s_d · s_{d+1} · s_d = perm · s_{d+1}` — the leaf's target permutation.  So the displaced letters
DO re-enter at the target; the algebra of the carry is closed here.  (What stays open is the CONVERTIBILITY fold that
sequences the re-insertions and its termination measure — see the residual marker.)

Both are `applyAdjacentSwap`-structural (mirroring `applyAdjacentSwap_swap_disjoint` / `applyAdjacentSwap_involutive`),
in-range (`position + 2 < perm.length`, exactly the leaf's `d + 1 + 1 < perm.length`), zero-axiom. -/

/-- ★★ **The braid relation on the one-line permutation** (`s_d s_{d+1} s_d = s_{d+1} s_d s_{d+1}`).  For a position with
its full braid window in range (`position + 2 < perm.length`, so all three strands `position`, `position + 1`,
`position + 2` genuinely swap), the two orders of the braid triple realize the same permutation.  Structural on `perm` /
`position`; the head is stripped by `applyAdjacentSwap_cons_succ` and the recursion drops to the tail (mirrors the
distant-swap commutation `applyAdjacentSwap_swap_disjoint`).  The in-range hypothesis is essential — on a length-2 list
`s_{d+1}` is a no-op, so `[a, b] · s_0 s_1 s_0 = [a, b]` but `[a, b] · s_1 s_0 s_1 = [b, a]`. -/
theorem applyAdjacentSwap_braid :
    (perm : List Nat) → (position : Nat) → position + 2 < perm.length →
    applyAdjacentSwap (applyAdjacentSwap (applyAdjacentSwap perm position) (position + 1)) position
      = applyAdjacentSwap (applyAdjacentSwap (applyAdjacentSwap perm (position + 1)) position) (position + 1)
  | [], position, inRange => absurd inRange (Nat.not_lt_zero (position + 2))
  | _ :: [], position, inRange => absurd inRange (Nat.not_lt.mpr (Nat.le_add_left 1 (position + 1)))
  | _ :: _ :: [], position, inRange => absurd inRange (Nat.not_lt.mpr (Nat.le_add_left 2 position))
  | _ :: _ :: _ :: _, 0, _ => rfl
  | first :: second :: third :: rest, position + 1, inRange => by
      have inRangeTail : position + 2 < (second :: third :: rest).length :=
        Nat.lt_of_succ_lt_succ inRange
      rw [applyAdjacentSwap_cons_succ first (second :: third :: rest) position,
        applyAdjacentSwap_cons_succ first (applyAdjacentSwap (second :: third :: rest) position) (position + 1),
        applyAdjacentSwap_cons_succ first
          (applyAdjacentSwap (applyAdjacentSwap (second :: third :: rest) position) (position + 1)) position,
        applyAdjacentSwap_cons_succ first (second :: third :: rest) (position + 1),
        applyAdjacentSwap_cons_succ first (applyAdjacentSwap (second :: third :: rest) (position + 1)) position,
        applyAdjacentSwap_cons_succ first
          (applyAdjacentSwap (applyAdjacentSwap (second :: third :: rest) (position + 1)) position) (position + 1)]
      exact congrArg (first :: ·) (applyAdjacentSwap_braid (second :: third :: rest) position inRangeTail)

/-- ★★ **The five-fold braid collapse** (`s_d s_{d+1} s_d s_{d+1} s_d = s_{d+1}`).  Applying the braid triple
`s_d s_{d+1} s_d` and then `s_{d+1} s_d` collapses to the single swap `s_{d+1}`: rewrite the leading braid triple to
`s_{d+1} s_d s_{d+1}` (`applyAdjacentSwap_braid`), then the two adjacent `s_{d+1}` and the two adjacent `s_d` each
annihilate by involution (`applyAdjacentSwap_involutive`).  This is the exact identity by which the braid-ascent carry
LANDS at the leaf's target `perm · s_{d+1}`: re-inserting `[d, d+1, d]` after the two staircase peels realizes precisely
these five swaps.  In-range (`position + 2 < perm.length`), zero-axiom. -/
theorem applyAdjacentSwap_braid_fivefold (perm : List Nat) (position : Nat)
    (inRange : position + 2 < perm.length) :
    applyAdjacentSwap (applyAdjacentSwap (applyAdjacentSwap (applyAdjacentSwap
        (applyAdjacentSwap perm position) (position + 1)) position) (position + 1)) position
      = applyAdjacentSwap perm (position + 1) := by
  rw [applyAdjacentSwap_braid perm position inRange,
    applyAdjacentSwap_involutive (applyAdjacentSwap (applyAdjacentSwap perm (position + 1)) position) (position + 1),
    applyAdjacentSwap_involutive (applyAdjacentSwap perm (position + 1)) position]

/-- Non-vacuity — the braid relation on `[0, 1, 2, 3]` at position `0`: both orders realize `[2, 1, 0, 3]`. -/
theorem applyAdjacentSwap_braid_smoke :
    applyAdjacentSwap (applyAdjacentSwap (applyAdjacentSwap [0, 1, 2, 3] 0) 1) 0
      = applyAdjacentSwap (applyAdjacentSwap (applyAdjacentSwap [0, 1, 2, 3] 1) 0) 1 :=
  applyAdjacentSwap_braid [0, 1, 2, 3] 0 (by decide)

/-- Non-vacuity — the five-fold collapse on the canonical residual permutation `[1, 3, 0, 2]` at position `1`
(`d = leftmostDescent = 1`): the five swaps `s_1 s_2 s_1 s_2 s_1` collapse to `s_2`, landing at
`applyAdjacentSwap [1, 3, 0, 2] 2 = [1, 3, 2, 0]` — exactly `perm · s_{d+1}`, the leaf's target permutation. -/
theorem applyAdjacentSwap_braid_fivefold_smoke :
    applyAdjacentSwap (applyAdjacentSwap (applyAdjacentSwap (applyAdjacentSwap
        (applyAdjacentSwap [1, 3, 0, 2] 1) 2) 1) 2) 1 = applyAdjacentSwap [1, 3, 0, 2] 2 :=
  applyAdjacentSwap_braid_fivefold [1, 3, 0, 2] 1 (by decide)

/-! ## WP-BRAUER r10 — the BRAID-ASCENT CARRY RE-INSERTION (Regime B, conditional on the three swept sub-steps)

The honest analog, for the BRAID mode, of the shipped `crossingInsertionStep_commute_full`.  In Regime B the local
braid move (`crossingInsertionStep_braid_localReduction`) turns the leaf's `canonicalCrossingWord perm ++ [d+1]` into
`canonicalCrossingWord (perm · s_d · s_{d+1}) ++ [d, d+1, d]` — the trailing triple `[d, d+1, d]` is the CARRY.  This
lemma re-inserts that triple one letter at a time, left to right, GIVEN the three insertion steps at the swept
permutations `p0 = perm · s_d · s_{d+1}`, `p1 = p0 · s_d`, `p2 = p1 · s_{d+1}` — and the five-fold braid collapse
(`applyAdjacentSwap_braid_fivefold`) certifies the final swept permutation `p2 · s_d` IS the leaf's target
`perm · s_{d+1}`.  So the leaf (in Regime B) is `BrauerConvFree7` GIVEN `step0`, `step1`, `step2`.

Why this SHARPENS but does NOT close: by the inversion-count arithmetic of the ascent (all three re-insertions are
themselves ascents, `inv p0 = inv perm - 2`, `inv p1 = inv perm - 1`, `inv p2 = inv perm`), the outer Lehmer induction
discharges `step0` and `step1` (strictly smaller inversion count) but NOT `step2` — an insertion at `inv perm`, the SAME
Lehmer level.  So the braid-ascent carry re-inserts to a residual at the same level, precisely the recon's plateau: the
recursion is NOT on `inversionCount`.  And this covers only Regime B — Regime A (`leftmostDescent (perm · s_d) = d - 1`,
the canonical example `[1, 3, 0, 2]`) needs a preparatory commute into the prefix BEFORE any braid, so the local braid
move does not even apply.  See the residual marker.  Zero-axiom; pure convertibility chaining + the five-fold. -/

/-- ★★ **The braid-ascent carry re-insertion (Regime B).**  For a Regime-B `perm` (`d = leftmostDescent perm`, once-
bubbled `perm · s_d` non-identity with `leftmostDescent (perm · s_d) = d + 1`) in range, GIVEN the three insertion steps
re-inserting `[d, d+1, d]` at the swept permutations `p0 = perm · s_d · s_{d+1}`, `p1 = p0 · s_d`, `p2 = p1 · s_{d+1}`,
the braid-ascent leaf holds: `canonicalCrossingWord perm ++ [d+1] ~ canonicalCrossingWord (perm · s_{d+1})`.  PROOF:
the shipped local braid move gives `~ canonicalCrossingWord p0 ++ [d, d+1, d]`; the three steps (each whiskered by the
remaining tail) re-canonicalise the triple to `canonicalCrossingWord (p2 · s_d)`; the five-fold collapse
`applyAdjacentSwap_braid_fivefold` identifies `p2 · s_d = perm · s_{d+1}`. -/
theorem crossingInsertionStep_braidAscent_reInsert (perm : List Nat)
    (nonIdentity : isIdentityPerm perm = false)
    (nonIdentitySwapped : isIdentityPerm (applyAdjacentSwap perm (leftmostDescent perm)) = false)
    (regimeB : leftmostDescent (applyAdjacentSwap perm (leftmostDescent perm)) = leftmostDescent perm + 1)
    (inRange : leftmostDescent perm + 2 < perm.length)
    (step0 : BrauerConvFree7
      (crossingWord (canonicalCrossingWord
          (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1))
        ++ [leftmostDescent perm]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap
          (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1))
          (leftmostDescent perm)))))
    (step1 : BrauerConvFree7
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap
          (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1))
          (leftmostDescent perm))
        ++ [leftmostDescent perm + 1]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap (applyAdjacentSwap
          (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1))
          (leftmostDescent perm)) (leftmostDescent perm + 1)))))
    (step2 : BrauerConvFree7
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap (applyAdjacentSwap
          (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1))
          (leftmostDescent perm)) (leftmostDescent perm + 1))
        ++ [leftmostDescent perm]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap (applyAdjacentSwap (applyAdjacentSwap
          (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1))
          (leftmostDescent perm)) (leftmostDescent perm + 1)) (leftmostDescent perm))))) :
    BrauerConvFree7 (crossingWord (canonicalCrossingWord perm ++ [leftmostDescent perm + 1]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap perm (leftmostDescent perm + 1)))) := by
  have fivefold : applyAdjacentSwap (applyAdjacentSwap (applyAdjacentSwap
        (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1))
        (leftmostDescent perm)) (leftmostDescent perm + 1)) (leftmostDescent perm)
      = applyAdjacentSwap perm (leftmostDescent perm + 1) :=
    applyAdjacentSwap_braid_fivefold perm (leftmostDescent perm) inRange
  have localMove :=
    crossingInsertionStep_braid_localReduction perm nonIdentity nonIdentitySwapped regimeB
  have conv1 : BrauerConvFree7
      (crossingWord (canonicalCrossingWord
          (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1))
        ++ [leftmostDescent perm, leftmostDescent perm + 1, leftmostDescent perm]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap
          (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1))
          (leftmostDescent perm))
        ++ [leftmostDescent perm + 1, leftmostDescent perm])) := by
    rw [← appendSnocAssoc (canonicalCrossingWord
          (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1)))
          (leftmostDescent perm) [leftmostDescent perm + 1, leftmostDescent perm],
      crossingWord_append (canonicalCrossingWord
          (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1))
        ++ [leftmostDescent perm]) [leftmostDescent perm + 1, leftmostDescent perm],
      crossingWord_append (canonicalCrossingWord (applyAdjacentSwap
          (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1))
          (leftmostDescent perm))) [leftmostDescent perm + 1, leftmostDescent perm]]
    exact BrauerConvFree7.whiskerRight
      (crossingWord [leftmostDescent perm + 1, leftmostDescent perm]) step0
  have conv2 : BrauerConvFree7
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap
          (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1))
          (leftmostDescent perm))
        ++ [leftmostDescent perm + 1, leftmostDescent perm]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap (applyAdjacentSwap
          (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1))
          (leftmostDescent perm)) (leftmostDescent perm + 1))
        ++ [leftmostDescent perm])) := by
    rw [← appendSnocAssoc (canonicalCrossingWord (applyAdjacentSwap
          (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1))
          (leftmostDescent perm))) (leftmostDescent perm + 1) [leftmostDescent perm],
      crossingWord_append (canonicalCrossingWord (applyAdjacentSwap
          (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1))
          (leftmostDescent perm))
        ++ [leftmostDescent perm + 1]) [leftmostDescent perm],
      crossingWord_append (canonicalCrossingWord (applyAdjacentSwap (applyAdjacentSwap
          (applyAdjacentSwap (applyAdjacentSwap perm (leftmostDescent perm)) (leftmostDescent perm + 1))
          (leftmostDescent perm)) (leftmostDescent perm + 1))) [leftmostDescent perm]]
    exact BrauerConvFree7.whiskerRight (crossingWord [leftmostDescent perm]) step1
  rw [← fivefold]
  exact BrauerConvFree7.trans localMove (BrauerConvFree7.trans conv1 (BrauerConvFree7.trans conv2 step2))

/-- Non-vacuity — the carry re-insertion CLOSES a concrete Regime-B braid-ascent leaf.  On `[2, 0, 1, 3]`
(`d = leftmostDescent = 0`, insert `s_1`, an ascent to `[2, 1, 0, 3]`, non-reflex, Regime B), the swept permutation
`p0 = perm · s_0 · s_1 = [0, 1, 2, 3]` is the identity, so all three re-insertion steps are pure reflexivity.  The
reduction then yields the leaf conclusion `crossingWord [1, 0, 1] ~ crossingWord [0, 1, 0]` — exactly the braid pair,
reached THROUGH the carry mechanism (local braid + five-fold-aligned triple re-insertion). -/
theorem crossingInsertionStep_braidAscent_reInsert_smoke :
    BrauerConvFree7 (crossingWord (canonicalCrossingWord [2, 0, 1, 3] ++ [leftmostDescent [2, 0, 1, 3] + 1]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap [2, 0, 1, 3] (leftmostDescent [2, 0, 1, 3] + 1)))) :=
  crossingInsertionStep_braidAscent_reInsert [2, 0, 1, 3] (by decide) (by decide) (by decide) (by decide)
    (BrauerConvFree7.ofFree (BrauerConvFree.refl _))
    (BrauerConvFree7.ofFree (BrauerConvFree.refl _))
    (BrauerConvFree7.ofFree (BrauerConvFree.refl _))

/-! ## Honesty markers -/

/-- ★ **Honesty marker — WP-BRAUER r9: the REFLEX mode + the DESCENT reduction are SHIPPED.**  The general reflexivity
lemma `canonicalCrossingWord_snoc_ofNewLeftmostDescent` (take the descent-landing as hypothesis, not derived from
`position < leftmostDescent`) and its convertibility corollary `crossingInsertionStep_reflex` close, by pure
reflexivity, both the IDENTITY BASE of the outer recursion (every in-range position is below the leftmost descent of an
identity — `leftmostDescent_gt_ofIdentityInRange`) AND the 242-of-547 braid-ascent cases whose swap lands its new
leftmost descent at the inserted position (`leftmostDescent (perm · s_{d+1}) = d + 1`).  The DESCENT reduction
`crossingInsertionStep_ofInvolutionIH` sends any position whose swap DROPS the inversion count to the IH at the
strictly-smaller permutation (involution + one R2 cancel).  Both closed zero-axiom.  `= true`. -/
def fxBrauer_hasInsertionReflexAndDescentModes : Bool := true

/-- ★★ **Honesty marker — WP-BRAUER r9: the OUTER STRONG INDUCTION is CLOSED; the whole in-range word problem is reduced
to ONE braid-ascent leaf.**  `inRangeInsertionStepFueled_ofBraidAscent` is a structural-fuel recursion on
`inversionCount perm` dispatching EVERY `(perm, position)` case of `InRangeInsertionStep`: EXTEND / identity base
(`crossingInsertionStep_extend`), CANCEL (`crossingInsertionStep_atLeftmostDescent`), COMMUTE
(`crossingInsertionStep_commute_full` + IH at `inversionCount − 1`), REFLEX (`crossingInsertionStep_reflex`), DESCENT
(`crossingInsertionStep_ofInvolutionIH` + IH at `inversionCount − 1`), and — the SOLE leaf left open — the
`BraidAscentInsertionStep` residual.  Hence `inRangeInsertionStep_ofBraidAscent : BraidAscentInsertionStep →
InRangeInsertionStep` and `crossingWords_equalPerm_conv_ofBraidAscent`.  This SHARPENS the r8 residual: from "the braid
carry fold" to the single machine-defined leaf (`position = leftmostDescent perm + 1`, ascent, non-reflex), with the
entire rest of the word problem CLOSED by a machine-checked induction on the Lehmer measure.  Non-vacuous:
`crossingWords_conv_{braidPair_r9, fourReversal, residualStuckExample}` witness the conclusion on the braid pair, the
S_4 reversal, and the r8 stuck example; `braidAscentResidual_hypotheses_inhabited` +
`braidAscentResidual_conclusion_isStuckExample` show the residual leaf is a genuine, satisfiable obligation whose
hardest small instance IS that stuck example.  `= true`. -/
def fxBrauer_hasInsertionOuterInductionAssembly : Bool := true

/-- **Honesty marker — the SOLE remaining leg of `InRangeInsertionStep` is the BRAID-ASCENT residual (`false`).**  After
r9's closed outer induction, `fxBrauer_hasCrossingOnlyStraightening` (`Brauer/WiringDescStandardForm.lean`) and
`fxBrauer_hasCrossingStraighteningInsertionResidual` (`Brauer/WiringDescStraightening.lean`) stay `false` because of ONE
leaf: `BraidAscentInsertionStep` — `position = leftmostDescent perm + 1` over a genuine permutation, an ASCENT there,
where the swap does NOT become the new leftmost descent (`leftmostDescent (perm · s_{d+1}) = d`, the 305-of-547 census
cases the reflex mode does NOT catch).  There the moved `[d, d+1]` must sweep leftward into the canonical prefix before
it can braid; the recon's exhaustive simulation found NO literal `inversionCount` / carried-index / regional monovariant
descending per shipped-move step (the machine-documented plateau), consistent with the Björner–Brenti / Little
"defect-row" hand-argument, which has no drop-in mechanized precedent (mathlib's `CoxeterSystem` proves only the weak
exchange property, via inversion count, not the strong exchange this leaf needs).  The termination is carried by the
distinguished-active-letter position — a `pureCupSpine_sort`-magnitude induction (the 1300-line zero-axiom sibling), the
work of a further round.  This is a route/measure gap, not an obstruction (Lehrer–Zhang Thm 2.6(2): the seven relations
DO present the category).  `= false`. -/
def fxBrauer_hasBraidAscentResidual : Bool := false

end FX1Poly.Polygraph
