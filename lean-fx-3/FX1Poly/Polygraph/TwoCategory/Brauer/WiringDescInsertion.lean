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

/-- **Honesty marker — the FULL insertion step stays `false`; after r7 the residual is exactly the IN-RANGE BRAID mode
plus its `inversionCount` assembly.**  Three of the four modes of the honest `InRangeInsertionStep` (in-range, genuine
permutations) now close as GENERAL theorems: CANCEL (`crossingInsertionStep_atLeftmostDescent`, `position = d`),
EXTEND (`crossingInsertionStep_extend`, `position < d`, reflexivity), and the COMMUTE local Coxeter step
(`crossingInsertionStep_commute_localReduction`, `position ≥ d + 2`).  What remains for a full proof of
`InRangeInsertionStep` (hence the flip of `fxBrauer_hasCrossingOnlyStraightening`) is:

  1. **the outer `inversionCount` induction** assembling CANCEL / EXTEND / COMMUTE, where the COMMUTE and BRAID cases
     re-insert `position` at the strictly-smaller `perm · s_d` via the IH — this needs the distant-swap commutation
     `applyAdjacentSwap (perm · s_d) position = applyAdjacentSwap (perm · s_position) d` and the leftmost-descent
     invariance under a distant swap (`leftmostDescent (perm · s_position) = d` for `position ≥ d + 2`), both further
     structural inductions; and
  2. **the BRAID mode itself** (`position = d + 1`): the inserted `s_{d+1}` meets the trailing `s_d`, which neither
     cancels nor commutes — it must BRAID (`crossingBraidFree`) and then the moved letter can KEEP interacting leftward
     through the canonical prefix of arbitrary length, so the recursion is NOT on `inversionCount` (it can rise) and
     needs the secondary lexicographic measure `(inversionCount perm, position)`.  This is the standing jam — the exact
     jamming configuration is *the braided `s_{d+1}` becoming `d`-adjacent to the next canonical run, forcing another
     braid up to `O(word length)` times* — the `locateAux` / `pureCupSpine_sort`-magnitude induction (the 1300-line
     zero-axiom sibling).

So the residual has shrunk from "the general insertion step" (r6) to "the IN-RANGE BRAID mode + the `inversionCount`
assembly"; the master markers `fxBrauer_hasCrossingOnlyStraightening` (`Brauer/WiringDescStandardForm.lean`) and
`fxBrauer_hasCrossingStraighteningInsertionResidual` (`Brauer/WiringDescStraightening.lean`) stay `false` because of it
— a route/measure gap, not an obstruction (Lehrer–Zhang Thm 2.6(2): the seven relations DO present the category).
`= false`. -/
def fxBrauer_hasCrossingInsertionStepGeneralResidual : Bool := false

end FX1Poly.Polygraph
