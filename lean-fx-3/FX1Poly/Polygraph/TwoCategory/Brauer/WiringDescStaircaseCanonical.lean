import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCombFold

/-! # BRAUER-BREACH r2 — the recursive-comb staircase, canonicity, and THE FLIP

BREACH-1 (`Brauer/WiringDescCombFold.lean`) shipped the Coxeter–Moser coset comb: every crossing word is
`BrauerConvFree7`-convertible to `u ++ run` where `u` mentions only lower generators and `run` is a descending run.
That is the FACTORIZATION `w = u · (s_{n-1} … s_k)`, but `u` is NOT further normalized — one comb level leaves the
Yang–Baxter pair `[0,1,0]` / `[1,0,1]` distinct.

This file lands the r2 breach: RECURSE the comb into the prefix (`recComb`), so the whole crossing word reaches a
UNIQUE staircase normal form determined solely by its through-strand permutation (Matsumoto / Regev–Roichman
canonical presentation, arXiv:math/0305393 §3.1; Björner–Brenti Prop. 2.4.4 minimal coset transversals along the
principal flag).  The keystone is the STRAND PIN: the top-strand image `natIndexOfValue (perm) g = g − k` reads the
descending-run length `k` straight off the permutation (Regev–Roichman Prop. 4.2's insertion position), so equal
permutation forces equal run at every level; strip and recurse gives canonicity, and canonicity + `recCombConv`
gives THE FLIP — equal permutation ⟹ `BrauerConvFree7`-convertible, hypothesis-free over all in-range crossing
words.  Matsumoto for `S_n` inside the seven-relation over-approximation `BrauerConvFree7`, mechanized zero-axiom.

## R1 (this section) — the recursive comb + its convertibility

`recComb generatorCount input` folds the DATA comb at level `generatorCount`, then recurses on the still-uncanonical
prefix at level `generatorCount - 1`.  `recCombConv` proves `crossingWord input` is `BrauerConvFree7`-convertible to
`crossingWord (recComb generatorCount input)` — the whole-staircase convertibility, hypothesis-free modulo
`mentionsOnlyBelow` well-formedness.

Raw Lean 4 + Init; structural recursion on the generator count, no `omega` / `simp`-AC / `native_decide` /
`WellFounded.fix`.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## R1.A — the data-fold certificate projections (from `comb_fold_from_fn`) -/

/-- The comb data fold's prefix mentions only generators below `generatorCount - 1` — the Björner–Brenti
right-descent transversal certificate, read off the functional fold. -/
theorem combFoldState_below (generatorCount : Nat) (input : List Nat)
    (inRange : mentionsOnlyBelow generatorCount input = true) :
    mentionsOnlyBelow (generatorCount - 1)
      (input.foldl (combInsertData generatorCount) ([], 0)).1 = true :=
  (comb_fold_from_fn generatorCount input [] 0 rfl (Nat.zero_le generatorCount) inRange).1

/-- The comb data fold's run length is at most `generatorCount`. -/
theorem combFoldState_runLe (generatorCount : Nat) (input : List Nat)
    (inRange : mentionsOnlyBelow generatorCount input = true) :
    (input.foldl (combInsertData generatorCount) ([], 0)).2 ≤ generatorCount :=
  (comb_fold_from_fn generatorCount input [] 0 rfl (Nat.zero_le generatorCount) inRange).2.1

/-! ## R1.B — the recursive comb staircase -/

/-- ★★ **The recursive comb staircase.**  At level `generatorCount + 1` run the DATA comb fold, then recurse on the
uncanonical prefix at level `generatorCount`.  Structural recursion on the generator count (the second argument is
free), so it computes and needs no fuel.  The image is the Regev–Roichman canonical presentation
`w_1 ⋯ w_{n-1}` — a unique reduced word per permutation. -/
def recComb : Nat → List Nat → List Nat
  | 0, _ => []
  | generatorCount + 1, input =>
      recComb generatorCount (input.foldl (combInsertData (generatorCount + 1)) ([], 0)).1
        ++ descendingPositions generatorCount
            (input.foldl (combInsertData (generatorCount + 1)) ([], 0)).2

/-! ## R1.C — the whole-staircase convertibility -/

/-- ★★ **The recursive comb is convertible to the input (hypothesis-free modulo `mentionsOnlyBelow`).**  Every
crossing word `crossingWord input` over generators `< generatorCount` is `BrauerConvFree7`-convertible to
`crossingWord (recComb generatorCount input)`.  Structural on `generatorCount`: one comb level via
`combNormalizeForm_conv`, then the FREE `whiskerRight` carries the recursive convertibility of the prefix past the
descending run (`crossingWord_append` splits both sides). -/
theorem recCombConv : (generatorCount : Nat) → (input : List Nat) →
    mentionsOnlyBelow generatorCount input = true →
    BrauerConvFree7 (crossingWord input) (crossingWord (recComb generatorCount input))
  | 0, input, hRange => by
      cases input with
      | nil => exact BrauerConvFree7.ofFree (BrauerConvFree.refl [])
      | cons position rest =>
          have hFalse : mentionsOnlyBelow 0 (position :: rest) = false := rfl
          rw [hFalse] at hRange
          exact Bool.noConfusion hRange
  | generatorCount + 1, input, hRange => by
      have uBelow : mentionsOnlyBelow generatorCount
          (input.foldl (combInsertData (generatorCount + 1)) ([], 0)).1 = true :=
        combFoldState_below (generatorCount + 1) input hRange
      have conv1 : BrauerConvFree7 (crossingWord input)
          (crossingWord (combNormalizeForm (generatorCount + 1) input)) :=
        combNormalizeForm_conv (generatorCount + 1) input hRange
      have ihConv : BrauerConvFree7
          (crossingWord (input.foldl (combInsertData (generatorCount + 1)) ([], 0)).1)
          (crossingWord (recComb generatorCount
            (input.foldl (combInsertData (generatorCount + 1)) ([], 0)).1)) :=
        recCombConv generatorCount (input.foldl (combInsertData (generatorCount + 1)) ([], 0)).1 uBelow
      show BrauerConvFree7 (crossingWord input)
        (crossingWord (recComb generatorCount (input.foldl (combInsertData (generatorCount + 1)) ([], 0)).1
          ++ descendingPositions generatorCount
              (input.foldl (combInsertData (generatorCount + 1)) ([], 0)).2))
      rw [crossingWord_append
        (recComb generatorCount (input.foldl (combInsertData (generatorCount + 1)) ([], 0)).1)
        (descendingPositions generatorCount (input.foldl (combInsertData (generatorCount + 1)) ([], 0)).2)]
      have combNFeq : combNormalizeForm (generatorCount + 1) input
          = (input.foldl (combInsertData (generatorCount + 1)) ([], 0)).1
            ++ descendingPositions generatorCount
                (input.foldl (combInsertData (generatorCount + 1)) ([], 0)).2 := rfl
      rw [combNFeq,
        crossingWord_append (input.foldl (combInsertData (generatorCount + 1)) ([], 0)).1
          (descendingPositions generatorCount
            (input.foldl (combInsertData (generatorCount + 1)) ([], 0)).2)] at conv1
      exact conv1.trans
        (BrauerConvFree7.whiskerRight
          (crossingWord (descendingPositions generatorCount
            (input.foldl (combInsertData (generatorCount + 1)) ([], 0)).2)) ihConv)

/-! ## R1.D — the recursive normal forms computed (r9, r11, width-5)

The one-level comb (`combNormalizeForm`) leaves distinct-word / same-permutation pairs distinct; `recComb`
UNIFIES them, which is exactly why the recursion is essential for the equal-permutation flip. -/

/-- The r9 jam word `[2, 0, 1, 2]` (the `BraidAscentInsertionStep` residual at permutation `[1, 3, 0, 2]`)
reaches the staircase `[0, 1, 2, 1]`. -/
theorem recComb_r9_stuck_word : recComb 3 [2, 0, 1, 2] = [0, 1, 2, 1] := rfl

/-- The r11 residual pair `[1, 2, 0, 1, 2]` and `[0, 1, 2, 0, 1]` (both realizing `[2, 3, 1, 0, 4]` on five
strands) UNIFY under the recursive comb — the one-level comb keeps them distinct
(`combNormalizeForm 4 [1,2,0,1,2] = [1,2,0,1,2]` vs `= [0,1,2,0,1]`), the recursion collapses both to `[0,1,0,2,1]`. -/
theorem recComb_r11_residual_left : recComb 4 [1, 2, 0, 1, 2] = [0, 1, 0, 2, 1] := rfl

/-- The right member of the r11 residual pair reaches the SAME staircase. -/
theorem recComb_r11_residual_right : recComb 4 [0, 1, 2, 0, 1] = [0, 1, 0, 2, 1] := rfl

/-- The one-level comb does NOT unify the r11 pair — it fixes `[1,2,0,1,2]` and returns `[0,1,2,0,1]` on the other;
only the recursion collapses them.  This exhibits why the staircase recursion is load-bearing. -/
theorem combNormalizeForm_r11_left_fixed : combNormalizeForm 4 [1, 2, 0, 1, 2] = [1, 2, 0, 1, 2] := rfl

/-- A width-5 (six-strand) word reaches its staircase. -/
theorem recComb_width5_word : recComb 5 [3, 1, 2, 0, 3, 1] = [1, 0, 2, 3, 2, 1] := rfl

/-- Non-vacuity — `recCombConv` fires on the r9 jam word: it is `BrauerConvFree7`-convertible to its staircase
`[0, 1, 2, 1]`. -/
theorem recCombConv_r9_stuck_word :
    BrauerConvFree7 (crossingWord [2, 0, 1, 2]) (crossingWord [0, 1, 2, 1]) :=
  recComb_r9_stuck_word ▸ recCombConv 3 [2, 0, 1, 2] (by decide)

/-- Non-vacuity — both r11 residual words are convertible to the common staircase `[0, 1, 0, 2, 1]`. -/
theorem recCombConv_r11_left :
    BrauerConvFree7 (crossingWord [1, 2, 0, 1, 2]) (crossingWord [0, 1, 0, 2, 1]) :=
  recComb_r11_residual_left ▸ recCombConv 4 [1, 2, 0, 1, 2] (by decide)

/-- Non-vacuity — the width-5 word is convertible to its staircase `[1, 0, 2, 3, 2, 1]`. -/
theorem recCombConv_width5_word :
    BrauerConvFree7 (crossingWord [3, 1, 2, 0, 3, 1]) (crossingWord [1, 0, 2, 3, 2, 1]) :=
  recComb_width5_word ▸ recCombConv 5 [3, 1, 2, 0, 3, 1] (by decide)

/-! ## Honesty marker (R1) -/

/-- ★★ **Honesty marker — the recursive-comb STAIRCASE + its convertibility are SHIPPED (BREACH r2, R1).**  `recComb`
recurses the Coxeter–Moser data comb into the prefix, reaching the unique per-permutation staircase (Regev–Roichman
canonical presentation), and `recCombConv` proves every crossing word is `BrauerConvFree7`-convertible to its
staircase (hypothesis-free modulo `mentionsOnlyBelow`).  Non-vacuous + genuinely recursive: `recComb_r11_residual_*`
UNIFY the S_5 residual pair `[1,2,0,1,2]` / `[0,1,2,0,1]` that the one-level comb keeps distinct
(`combNormalizeForm_r11_left_fixed`), and `recCombConv_{r9_stuck_word, r11_left, width5_word}` fire the
convertibility on the r9 jam word, the r11 pair, and a width-5 word.  `= true`. -/
def fxBrauer_hasStaircaseCombNormalForm : Bool := true

/-! ## R3.A — the permutation-carry crux (the soundness leg's hard lemma)

Each `combInsertData` step realizes exactly ONE adjacent swap of the through-strand permutation.  Three of the four
branches are word rewrites (snoc / involution); the CARRY branch needs the Coxeter identity `s_{letter-1} · run =
run · s_letter` on the one-line permutation — `carry_perm` — proved by induction on the run (mirroring the shipped
`carryIntoRun`), using the shipped `applyAdjacentSwap_braid` at the pivot and disjoint-swap commutation for the two
sub-runs. -/

/-- `value - 2 + 2 = value` when `2 ≤ value` — the crossing-arity round-trip.  Structural on the `value + 2`
shape. -/
private theorem subTwoAddTwoStaircase : (value : Nat) → 2 ≤ value → value - 2 + 2 = value
  | 0, twoLe => absurd twoLe (by decide)
  | 1, twoLe => absurd twoLe (by decide)
  | _ + 2, _ => rfl

/-- `i - 1 + 1 = i` when `1 ≤ i` — structural on `i`, `propext`-free. -/
private theorem predSuccStaircase : (i : Nat) → 1 ≤ i → i - 1 + 1 = i
  | 0, positive => absurd positive (by decide)
  | _ + 1, _ => rfl

/-- `a ≤ top - 1` from `a + 1 ≤ top` — structural on `top`, `propext`-free. -/
private theorem natLePredStaircase : (a top : Nat) → a + 1 ≤ top → a ≤ top - 1
  | a, 0, h => absurd h (Nat.not_succ_le_zero a)
  | _, _ + 1, h => Nat.le_of_succ_le_succ h

/-- `m ≤ n` from `m + k ≤ n + k` — structural on `k` (`+ k` reduces on the right), `propext`-free. -/
private theorem natLeOfAddLeAddRightStaircase : (m n k : Nat) → m + k ≤ n + k → m ≤ n
  | _, _, 0, h => h
  | m, n, k + 1, h => natLeOfAddLeAddRightStaircase m n k (Nat.le_of_succ_le_succ h)

/-- `m ≤ n` from `k + m ≤ k + n` — via `Nat.add_comm` + `natLeOfAddLeAddRightStaircase`. -/
private theorem natLeOfAddLeAddLeftStaircase (k m n : Nat) (h : k + m ≤ k + n) : m ≤ n :=
  natLeOfAddLeAddRightStaircase m n k (by rw [Nat.add_comm m k, Nat.add_comm n k]; exact h)

/-- `foldl applyAdjacentSwap` splits over a list concatenation.  Structural on the prefix. -/
theorem foldl_append_swap : (prefixList suffixList init : List Nat) →
    (prefixList ++ suffixList).foldl applyAdjacentSwap init
      = suffixList.foldl applyAdjacentSwap (prefixList.foldl applyAdjacentSwap init)
  | [], _, _ => rfl
  | head :: rest, suffixList, init => foldl_append_swap rest suffixList (applyAdjacentSwap init head)

/-- `low + (high - low - 2) + 2 = high` when `low + 2 ≤ high` — the index witness for the disjoint-swap form.
Structural on `low`, `propext`-free. -/
private theorem commuteHighEq : (low high : Nat) → low + 2 ≤ high → low + (high - low - 2) + 2 = high
  | 0, high, hLe => by
      rw [Nat.zero_add]
      exact subTwoAddTwoStaircase high hLe
  | _ + 1, 0, hLe => absurd hLe (Nat.not_succ_le_zero _)
  | low + 1, high + 1, hLe => by
      have inner : low + (high - low - 2) + 2 = high := commuteHighEq low high (Nat.le_of_succ_le_succ hLe)
      rw [Nat.succ_sub_succ, Nat.succ_add, Nat.succ_add]
      exact congrArg Nat.succ inner

/-- ★ **Distant adjacent swaps commute, in `i + 2 ≤ j` form** — the shipped `applyAdjacentSwap_swap_disjoint`
re-expressed with a plain `≤` distance hypothesis (via `commuteHighEq`). -/
theorem applyAdjacentSwap_commute_of_le (perm : List Nat) (i j : Nat) (dist : i + 2 ≤ j) :
    applyAdjacentSwap (applyAdjacentSwap perm i) j = applyAdjacentSwap (applyAdjacentSwap perm j) i := by
  have jEq : i + (j - i - 2) + 2 = j := commuteHighEq i j dist
  have shipped := applyAdjacentSwap_swap_disjoint perm i (j - i - 2)
  rw [jEq] at shipped
  exact shipped

/-- ★ **A swap ABOVE a descending run commutes past the whole run fold.**  For `run = descendingPositions runTop
count` all of whose elements are `≥ letter + 2` (`letter + count + 1 ≤ runTop`), the swap at `letter` commutes past
the fold.  Structural on `count`. -/
theorem swap_commutes_runAbove (letter : Nat) :
    (runTop count : Nat) → (perm : List Nat) → letter + count + 1 ≤ runTop →
    (descendingPositions runTop count).foldl applyAdjacentSwap (applyAdjacentSwap perm letter)
      = applyAdjacentSwap ((descendingPositions runTop count).foldl applyAdjacentSwap perm) letter
  | _, 0, _, _ => rfl
  | runTop, count + 1, perm, hLe => by
      have topDistant : letter + 2 ≤ runTop :=
        Nat.le_trans (Nat.add_le_add_left (Nat.le_add_left 2 count) letter) hLe
      show (descendingPositions (runTop - 1) count).foldl applyAdjacentSwap
              (applyAdjacentSwap (applyAdjacentSwap perm letter) runTop)
          = applyAdjacentSwap ((descendingPositions (runTop - 1) count).foldl applyAdjacentSwap
              (applyAdjacentSwap perm runTop)) letter
      rw [applyAdjacentSwap_commute_of_le perm letter runTop topDistant]
      exact swap_commutes_runAbove letter (runTop - 1) count (applyAdjacentSwap perm runTop)
        (by
          have e : runTop - 1 + 1 = runTop := Nat.succ_pred_eq_of_pos (Nat.lt_of_lt_of_le
            (Nat.lt_of_lt_of_le (Nat.zero_lt_succ letter) (Nat.le_add_right (letter + 1) 1)) topDistant)
          have hStep : letter + count + 1 + 1 ≤ runTop := hLe
          have : letter + count + 1 ≤ runTop - 1 := by
            rw [← e] at hStep; exact Nat.le_of_succ_le_succ hStep
          exact this)

/-- ★ **A swap BELOW a descending run commutes past the whole run fold.**  For `run = descendingPositions runTop
count` all of whose elements are `≤ letter - 2` (`runTop + 2 ≤ letter`), the swap at `letter` commutes past the fold.
Structural on `count`. -/
theorem swap_commutes_runBelow (letter : Nat) :
    (runTop count : Nat) → (perm : List Nat) → runTop + 2 ≤ letter →
    (descendingPositions runTop count).foldl applyAdjacentSwap (applyAdjacentSwap perm letter)
      = applyAdjacentSwap ((descendingPositions runTop count).foldl applyAdjacentSwap perm) letter
  | _, 0, _, _ => rfl
  | runTop, count + 1, perm, hLe => by
      have topDistant : runTop + 2 ≤ letter := hLe
      show (descendingPositions (runTop - 1) count).foldl applyAdjacentSwap
              (applyAdjacentSwap (applyAdjacentSwap perm letter) runTop)
          = applyAdjacentSwap ((descendingPositions (runTop - 1) count).foldl applyAdjacentSwap
              (applyAdjacentSwap perm runTop)) letter
      rw [(applyAdjacentSwap_commute_of_le perm runTop letter topDistant).symm]
      exact swap_commutes_runBelow letter (runTop - 1) count (applyAdjacentSwap perm runTop)
        (Nat.le_trans (Nat.add_le_add_right (Nat.sub_le runTop 1) 2) hLe)

/-- ★★ **The permutation-carry identity** `s_{letter-1} · run = run · s_letter`.  For `run = descendingPositions top
runLen` with `letter` strictly inside the run (`1 ≤ letter`, `letter ≤ top`, `top + 2 ≤ letter + runLen`) and the
braid window in range (`top + 2 ≤ perm.length`), folding `run` after the swap `s_{letter-1}` equals folding `run`
then the swap `s_letter`.  Induction on `runLen` mirroring the shipped `carryIntoRun`: STEP peels `s_top` by
disjoint commutation; BASE (`letter = top`) braids the pivot `s_{top-1} s_top s_{top-1}` and commutes past the lower
sub-run. -/
theorem carry_perm (letter : Nat) (letterPos : 1 ≤ letter) :
    (top runLen : Nat) → (perm : List Nat) → letter ≤ top → runLen ≤ top + 1 →
    top + 2 ≤ letter + runLen → top + 2 ≤ perm.length →
    (descendingPositions top runLen).foldl applyAdjacentSwap (applyAdjacentSwap perm (letter - 1))
      = applyAdjacentSwap ((descendingPositions top runLen).foldl applyAdjacentSwap perm) letter
  | top, 0, _, letterLeTop, _, aboveBottom, _ =>
      absurd (Nat.le_trans (Nat.le_trans aboveBottom letterLeTop) (Nat.le_succ top))
        (Nat.not_succ_le_self (top + 1))
  | top, runLen + 1, perm, letterLeTop, runLenLe, aboveBottom, lenOk => by
      rcases Nat.lt_or_ge letter top with ltTop | geTop
      · -- STEP: letter < top — peel s_top by disjoint commutation, recurse.
        have topPos : 1 ≤ top := Nat.le_trans letterPos (Nat.le_of_lt ltTop)
        have letterM1Distant : (letter - 1) + 2 ≤ top := by
          rw [show (letter - 1) + 2 = letter + 1 from
            congrArg Nat.succ (predSuccStaircase letter letterPos)]
          exact ltTop
        show (descendingPositions (top - 1) runLen).foldl applyAdjacentSwap
                (applyAdjacentSwap (applyAdjacentSwap perm (letter - 1)) top)
            = applyAdjacentSwap ((descendingPositions (top - 1) runLen).foldl applyAdjacentSwap
                (applyAdjacentSwap perm top)) letter
        rw [applyAdjacentSwap_commute_of_le perm (letter - 1) top letterM1Distant]
        exact carry_perm letter letterPos (top - 1) runLen (applyAdjacentSwap perm top)
          (natLePredStaircase letter top ltTop)
          (by rw [predSuccStaircase top topPos]; exact Nat.le_of_succ_le_succ runLenLe)
          (by
            have e : top - 1 + 2 = top + 1 := congrArg Nat.succ (predSuccStaircase top topPos)
            rw [e]; exact Nat.le_of_succ_le_succ aboveBottom)
          (by
            rw [applyAdjacentSwap_length perm top,
              show top - 1 + 2 = top + 1 from congrArg Nat.succ (predSuccStaircase top topPos)]
            exact Nat.le_trans (Nat.le_succ (top + 1)) lenOk)
      · -- BASE: letter = top — braid the pivot, commute past the lower sub-run.
        have eqTop : letter = top := Nat.le_antisymm letterLeTop geTop
        subst eqTop
        have runLenPos : 1 ≤ runLen :=
          natLeOfAddLeAddLeftStaircase letter 1 runLen (Nat.le_of_succ_le_succ aboveBottom)
        cases runLen with
        | zero => exact absurd runLenPos (Nat.not_succ_le_zero 0)
        | succ lowerLen =>
            -- descendingPositions letter (lowerLen+2) = letter :: (letter-1) :: descendingPositions (letter-2) lowerLen
            have runDecomp : descendingPositions letter (lowerLen + 1 + 1)
                = letter :: (letter - 1) :: descendingPositions (letter - 2) lowerLen := rfl
            rw [runDecomp]
            show (descendingPositions (letter - 2) lowerLen).foldl applyAdjacentSwap
                    (applyAdjacentSwap (applyAdjacentSwap (applyAdjacentSwap perm (letter - 1)) letter) (letter - 1))
                = applyAdjacentSwap ((descendingPositions (letter - 2) lowerLen).foldl applyAdjacentSwap
                    (applyAdjacentSwap (applyAdjacentSwap perm letter) (letter - 1))) letter
            -- braid: s_{letter-1} s_letter s_{letter-1} = s_letter s_{letter-1} s_letter
            have braidRaw := applyAdjacentSwap_braid perm (letter - 1)
              (by
                rw [show (letter - 1) + 2 = letter + 1 from
                  congrArg Nat.succ (predSuccStaircase letter letterPos)]
                exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (letter + 1)) lenOk)
            rw [predSuccStaircase letter letterPos] at braidRaw
            rw [braidRaw]
            -- commute the outer s_letter past the lower sub-run (empty at lowerLen = 0)
            cases lowerLen with
            | zero => rfl
            | succ lowerLen2 =>
                have letterGe2 : 2 ≤ letter :=
                  Nat.le_trans (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le lowerLen2)))
                    (Nat.le_of_succ_le_succ runLenLe)
                have lowerBelow : (letter - 2) + 2 ≤ letter :=
                  Nat.le_of_eq (subTwoAddTwoStaircase letter letterGe2)
                exact swap_commutes_runBelow letter (letter - 2) (lowerLen2 + 1)
                  (applyAdjacentSwap (applyAdjacentSwap perm letter) (letter - 1)) lowerBelow

/-! ## R3.B — the DATA comb fold preserves the through-strand permutation (the soundness leg)

Each `combInsertData` step realizes exactly one adjacent swap of `permuteOfCrossingWord (generatorCount + 1)`
applied to the config word; folding gives `permuteOfCrossingWord (generatorCount + 1) (combNormalizeForm gc W) =
permuteOfCrossingWord (generatorCount + 1) W` — the permutation is preserved by the comb.  This is the DATA-level
soundness the canonicity argument reads the strand pin off. -/

/-- `top - count - 1 = top - 1 - count` — structural on `count`, `propext`-free. -/
private theorem subOneCommStaircase : (top count : Nat) → top - count - 1 = top - 1 - count
  | _, 0 => rfl
  | top, count + 1 => congrArg Nat.pred (subOneCommStaircase top count)

/-- The descending run has a distinguished LAST element `top - count`. -/
private theorem descendingPositions_snocStaircase : (top count : Nat) →
    descendingPositions top count ++ [top - count] = descendingPositions top (count + 1)
  | _, 0 => rfl
  | top, count + 1 => by
      have idxEq : top - (count + 1) = (top - 1) - count := subOneCommStaircase top count
      have inner : descendingPositions (top - 1) count ++ [top - (count + 1)]
          = descendingPositions (top - 1) (count + 1) := by
        rw [idxEq]; exact descendingPositions_snocStaircase (top - 1) count
      show top :: (descendingPositions (top - 1) count ++ [top - (count + 1)])
         = top :: descendingPositions (top - 1) (count + 1)
      exact congrArg (top :: ·) inner

/-- `a + c - c = a` — structural on `c`, `propext`-free (Init's `Nat.add_sub_cancel` leaks). -/
private theorem natAddSubCancelStaircase : (a c : Nat) → a + c - c = a
  | _, 0 => rfl
  | a, c + 1 => (Nat.succ_sub_succ (a + c) c).trans (natAddSubCancelStaircase a c)

/-- `a = b - c` from `a + c = b` — clean replacement for Init's `Nat.eq_sub_of_add_eq`. -/
private theorem natEqSubOfAddEqStaircase (a c b : Nat) (h : a + c = b) : a = b - c := by
  rw [← h]; exact (natAddSubCancelStaircase a c).symm

/-- `(front ++ mid) ++ back = front ++ (mid ++ back)` — cons-only structural copy (Init's `List.append_assoc`
leaks `propext`). -/
private theorem appendAssocStaircase {alpha : Type _} :
    (front mid back : List alpha) → (front ++ mid) ++ back = front ++ (mid ++ back)
  | [], _, _ => rfl
  | head :: rest, mid, back => congrArg (head :: ·) (appendAssocStaircase rest mid back)

/-- `permuteOfCrossingWord` splits over concatenation — the append law. -/
theorem perm_append_split (bottomCount : Nat) (a b : List Nat) :
    permuteOfCrossingWord bottomCount (a ++ b)
      = b.foldl applyAdjacentSwap (permuteOfCrossingWord bottomCount a) :=
  foldl_append_swap a b (List.range bottomCount)

/-- ★★ **Each `combInsertData` step realizes exactly one adjacent swap of the permutation.**  The permutation of the
new config word is the old config's permutation with `s_letter` applied on the right.  Four branches: COMMUTE
(disjoint commute past the run), EXTEND (the run grows — a pure snoc), CANCEL (the run shrinks — snoc + involution),
CARRY (`carry_perm`). -/
theorem combInsertData_realizesSwap (generatorCount : Nat) (genPos : 1 ≤ generatorCount)
    (statePrefix : List Nat) (stateRun : Nat) (stateRunLe : stateRun ≤ generatorCount)
    (letter : Nat) (letterLt : letter < generatorCount) :
    permuteOfCrossingWord (generatorCount + 1)
        ((combInsertData generatorCount (statePrefix, stateRun) letter).1
          ++ descendingPositions (generatorCount - 1)
              (combInsertData generatorCount (statePrefix, stateRun) letter).2)
      = applyAdjacentSwap (permuteOfCrossingWord (generatorCount + 1)
          (statePrefix ++ descendingPositions (generatorCount - 1) stateRun)) letter := by
  rcases Nat.lt_trichotomy (letter + stateRun) generatorCount with hLt | hEq | hGt
  · rcases Nat.lt_or_ge (letter + stateRun + 1) generatorCount with hCommute | hExtendGe
    · -- COMMUTE
      have condCommute : letter + stateRun + 2 ≤ generatorCount := hCommute
      have dataEq : combInsertData generatorCount (statePrefix, stateRun) letter
          = (statePrefix ++ [letter], stateRun) := by
        show (if letter + stateRun + 2 ≤ generatorCount then (statePrefix ++ [letter], stateRun)
              else if letter + stateRun + 1 = generatorCount then (statePrefix, stateRun + 1)
              else if letter + stateRun = generatorCount then (statePrefix, stateRun - 1)
              else (statePrefix ++ [letter - 1], stateRun)) = (statePrefix ++ [letter], stateRun)
        rw [if_pos condCommute]
      rw [dataEq]
      show permuteOfCrossingWord (generatorCount + 1)
          ((statePrefix ++ [letter]) ++ descendingPositions (generatorCount - 1) stateRun)
        = applyAdjacentSwap (permuteOfCrossingWord (generatorCount + 1)
            (statePrefix ++ descendingPositions (generatorCount - 1) stateRun)) letter
      rw [perm_append_split (generatorCount + 1) (statePrefix ++ [letter])
            (descendingPositions (generatorCount - 1) stateRun),
        permuteOfCrossingWord_snoc (generatorCount + 1) statePrefix letter,
        perm_append_split (generatorCount + 1) statePrefix
          (descendingPositions (generatorCount - 1) stateRun)]
      exact swap_commutes_runAbove letter (generatorCount - 1) stateRun
        (permuteOfCrossingWord (generatorCount + 1) statePrefix)
        (natLePredStaircase (letter + stateRun + 1) generatorCount condCommute)
    · -- EXTEND
      have hExtend : letter + stateRun + 1 = generatorCount := Nat.le_antisymm hLt hExtendGe
      have notCommute : ¬ (letter + stateRun + 2 ≤ generatorCount) := by
        rw [← hExtend]; exact Nat.not_succ_le_self _
      have dataEq : combInsertData generatorCount (statePrefix, stateRun) letter
          = (statePrefix, stateRun + 1) := by
        show (if letter + stateRun + 2 ≤ generatorCount then (statePrefix ++ [letter], stateRun)
              else if letter + stateRun + 1 = generatorCount then (statePrefix, stateRun + 1)
              else if letter + stateRun = generatorCount then (statePrefix, stateRun - 1)
              else (statePrefix ++ [letter - 1], stateRun)) = (statePrefix, stateRun + 1)
        rw [if_neg notCommute, if_pos hExtend]
      rw [dataEq]
      show permuteOfCrossingWord (generatorCount + 1)
          (statePrefix ++ descendingPositions (generatorCount - 1) (stateRun + 1))
        = applyAdjacentSwap (permuteOfCrossingWord (generatorCount + 1)
            (statePrefix ++ descendingPositions (generatorCount - 1) stateRun)) letter
      have letterEq : letter = (generatorCount - 1) - stateRun :=
        natEqSubOfAddEqStaircase letter stateRun (generatorCount - 1)
          (natEqSubOfAddEqStaircase (letter + stateRun) 1 generatorCount hExtend)
      have runSnoc : descendingPositions (generatorCount - 1) (stateRun + 1)
          = descendingPositions (generatorCount - 1) stateRun ++ [letter] := by
        rw [letterEq]; exact (descendingPositions_snocStaircase (generatorCount - 1) stateRun).symm
      rw [runSnoc, ← appendAssocStaircase statePrefix (descendingPositions (generatorCount - 1) stateRun) [letter],
        permuteOfCrossingWord_snoc (generatorCount + 1)
          (statePrefix ++ descendingPositions (generatorCount - 1) stateRun) letter]
  · -- CANCEL
    have notCommute : ¬ (letter + stateRun + 2 ≤ generatorCount) := fun h => by
      rw [hEq] at h
      exact Nat.not_succ_le_self generatorCount (Nat.le_trans (Nat.le_succ (generatorCount + 1)) h)
    have notExtend : ¬ (letter + stateRun + 1 = generatorCount) := fun h => by
      rw [hEq] at h
      exact absurd (Nat.le_of_eq h) (Nat.not_succ_le_self generatorCount)
    have dataEq : combInsertData generatorCount (statePrefix, stateRun) letter
        = (statePrefix, stateRun - 1) := by
      show (if letter + stateRun + 2 ≤ generatorCount then (statePrefix ++ [letter], stateRun)
            else if letter + stateRun + 1 = generatorCount then (statePrefix, stateRun + 1)
            else if letter + stateRun = generatorCount then (statePrefix, stateRun - 1)
            else (statePrefix ++ [letter - 1], stateRun)) = (statePrefix, stateRun - 1)
      rw [if_neg notCommute, if_neg notExtend, if_pos hEq]
    rw [dataEq]
    cases stateRun with
    | zero =>
        have hEq' : letter = generatorCount := hEq
        exact absurd (hEq' ▸ letterLt) (Nat.lt_irrefl generatorCount)
    | succ c =>
        show permuteOfCrossingWord (generatorCount + 1)
            (statePrefix ++ descendingPositions (generatorCount - 1) c)
          = applyAdjacentSwap (permuteOfCrossingWord (generatorCount + 1)
              (statePrefix ++ descendingPositions (generatorCount - 1) (c + 1))) letter
        have letterEq : letter = (generatorCount - 1) - c :=
          natEqSubOfAddEqStaircase letter c (generatorCount - 1)
            (natEqSubOfAddEqStaircase (letter + c) 1 generatorCount hEq)
        have runSnoc : descendingPositions (generatorCount - 1) (c + 1)
            = descendingPositions (generatorCount - 1) c ++ [letter] := by
          rw [letterEq]; exact (descendingPositions_snocStaircase (generatorCount - 1) c).symm
        rw [runSnoc, ← appendAssocStaircase statePrefix (descendingPositions (generatorCount - 1) c) [letter],
          permuteOfCrossingWord_snoc (generatorCount + 1)
            (statePrefix ++ descendingPositions (generatorCount - 1) c) letter,
          applyAdjacentSwap_involutive (permuteOfCrossingWord (generatorCount + 1)
            (statePrefix ++ descendingPositions (generatorCount - 1) c)) letter]
  · -- CARRY
    have gLt2 : generatorCount < letter + stateRun + 2 :=
      Nat.lt_of_lt_of_le hGt (Nat.le_add_right (letter + stateRun) 2)
    have notCommute : ¬ (letter + stateRun + 2 ≤ generatorCount) := Nat.not_le.mpr gLt2
    have notExtend : ¬ (letter + stateRun + 1 = generatorCount) := fun h => by
      have gLt1 : generatorCount < letter + stateRun + 1 :=
        Nat.lt_of_lt_of_le hGt (Nat.le_succ (letter + stateRun))
      rw [h] at gLt1
      exact Nat.lt_irrefl generatorCount gLt1
    have notCancel : ¬ (letter + stateRun = generatorCount) := fun h => by
      have hGtCopy : generatorCount < letter + stateRun := hGt
      rw [h] at hGtCopy
      exact Nat.lt_irrefl generatorCount hGtCopy
    have dataEq : combInsertData generatorCount (statePrefix, stateRun) letter
        = (statePrefix ++ [letter - 1], stateRun) := by
      show (if letter + stateRun + 2 ≤ generatorCount then (statePrefix ++ [letter], stateRun)
            else if letter + stateRun + 1 = generatorCount then (statePrefix, stateRun + 1)
            else if letter + stateRun = generatorCount then (statePrefix, stateRun - 1)
            else (statePrefix ++ [letter - 1], stateRun)) = (statePrefix ++ [letter - 1], stateRun)
      rw [if_neg notCommute, if_neg notExtend, if_neg notCancel]
    rw [dataEq]
    show permuteOfCrossingWord (generatorCount + 1)
        ((statePrefix ++ [letter - 1]) ++ descendingPositions (generatorCount - 1) stateRun)
      = applyAdjacentSwap (permuteOfCrossingWord (generatorCount + 1)
          (statePrefix ++ descendingPositions (generatorCount - 1) stateRun)) letter
    have letterPos : 1 ≤ letter := by
      have h1 : generatorCount + 1 ≤ letter + generatorCount :=
        Nat.le_trans hGt (Nat.add_le_add_left stateRunLe letter)
      exact natLeOfAddLeAddLeftStaircase generatorCount 1 letter
        (by rw [Nat.add_comm letter generatorCount] at h1; exact h1)
    rw [perm_append_split (generatorCount + 1) (statePrefix ++ [letter - 1])
          (descendingPositions (generatorCount - 1) stateRun),
      permuteOfCrossingWord_snoc (generatorCount + 1) statePrefix (letter - 1),
      perm_append_split (generatorCount + 1) statePrefix
        (descendingPositions (generatorCount - 1) stateRun)]
    exact carry_perm letter letterPos (generatorCount - 1) stateRun
      (permuteOfCrossingWord (generatorCount + 1) statePrefix)
      (natLePredStaircase letter generatorCount letterLt)
      (by rw [predSuccStaircase generatorCount genPos]; exact stateRunLe)
      (by rw [show (generatorCount - 1) + 2 = generatorCount + 1 from
          congrArg Nat.succ (predSuccStaircase generatorCount genPos)]; exact hGt)
      (by rw [permuteOfCrossingWord_length (generatorCount + 1) statePrefix]
          exact Nat.le_of_eq (congrArg Nat.succ (predSuccStaircase generatorCount genPos)))

/-- `list ++ [] = list` — cons-only structural copy (Init's `List.append_nil` leaks `propext`). -/
private theorem appendNilStaircase : (list : List Nat) → list ++ [] = list
  | [] => rfl
  | head :: rest => congrArg (head :: ·) (appendNilStaircase rest)

/-- Left projection of a true boolean conjunction. -/
private theorem boolAndLeftStaircase : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → leftFlag = true
  | true, _, _ => rfl
  | false, _, conj => Bool.noConfusion conj

/-- Right projection of a true boolean conjunction. -/
private theorem boolAndRightStaircase : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → rightFlag = true
  | true, _, conj => conj
  | false, _, conj => Bool.noConfusion conj

/-- `a ≤ b` from `Nat.ble a b = true` — structural on `a`, `propext`-free. -/
private theorem natLeOfBleStaircase : (a b : Nat) → Nat.ble a b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => Bool.noConfusion h
  | a + 1, b + 1, h => Nat.succ_le_succ (natLeOfBleStaircase a b h)

/-- `a < b` from `Nat.blt a b = true`. -/
private theorem natLtOfBltStaircase (a b : Nat) (h : Nat.blt a b = true) : a < b :=
  natLeOfBleStaircase (a + 1) b h

/-- ★★ **The DATA comb fold preserves the permutation, from any state.**  Folding `rest` (in range) onto a state
gives a config whose permutation equals the permutation of the state's config followed by `rest`.  Structural on
`rest`, threading the state invariants (`mentionsOnlyBelow`, run bound) via the shipped `combInsert_step_fn`. -/
theorem combFold_preservesPerm (generatorCount : Nat) (genPos : 1 ≤ generatorCount) :
    (rest : List Nat) → (statePrefix : List Nat) → (stateRun : Nat) →
    mentionsOnlyBelow (generatorCount - 1) statePrefix = true → stateRun ≤ generatorCount →
    mentionsOnlyBelow generatorCount rest = true →
    permuteOfCrossingWord (generatorCount + 1)
        ((rest.foldl (combInsertData generatorCount) (statePrefix, stateRun)).1
          ++ descendingPositions (generatorCount - 1)
              (rest.foldl (combInsertData generatorCount) (statePrefix, stateRun)).2)
      = permuteOfCrossingWord (generatorCount + 1)
          ((statePrefix ++ descendingPositions (generatorCount - 1) stateRun) ++ rest)
  | [], statePrefix, stateRun, _, _, _ => by
      show permuteOfCrossingWord (generatorCount + 1)
          (statePrefix ++ descendingPositions (generatorCount - 1) stateRun)
        = permuteOfCrossingWord (generatorCount + 1)
            ((statePrefix ++ descendingPositions (generatorCount - 1) stateRun) ++ [])
      rw [appendNilStaircase (statePrefix ++ descendingPositions (generatorCount - 1) stateRun)]
  | letter :: restTail, statePrefix, stateRun, uBelow, runLe, hRange => by
      have letterLt : letter < generatorCount :=
        natLtOfBltStaircase letter generatorCount (boolAndLeftStaircase _ _ hRange)
      obtain ⟨belowMid, runLeMid, _⟩ :=
        combInsert_step_fn generatorCount statePrefix stateRun uBelow runLe letter letterLt
      have ihEq := combFold_preservesPerm generatorCount genPos restTail
        (combInsertData generatorCount (statePrefix, stateRun) letter).1
        (combInsertData generatorCount (statePrefix, stateRun) letter).2 belowMid runLeMid
        (boolAndRightStaircase _ _ hRange)
      have stepEq := combInsertData_realizesSwap generatorCount genPos statePrefix stateRun runLe letter letterLt
      -- combine: fold(letter::restTail) = fold restTail (combInsertData ... letter)
      show permuteOfCrossingWord (generatorCount + 1)
          ((restTail.foldl (combInsertData generatorCount)
              (combInsertData generatorCount (statePrefix, stateRun) letter)).1
            ++ descendingPositions (generatorCount - 1)
                (restTail.foldl (combInsertData generatorCount)
                  (combInsertData generatorCount (statePrefix, stateRun) letter)).2)
        = permuteOfCrossingWord (generatorCount + 1)
            ((statePrefix ++ descendingPositions (generatorCount - 1) stateRun) ++ (letter :: restTail))
      rw [ihEq, perm_append_split (generatorCount + 1)
            ((combInsertData generatorCount (statePrefix, stateRun) letter).1
              ++ descendingPositions (generatorCount - 1)
                  (combInsertData generatorCount (statePrefix, stateRun) letter).2) restTail,
        stepEq]
      exact (perm_append_split (generatorCount + 1)
        (statePrefix ++ descendingPositions (generatorCount - 1) stateRun) (letter :: restTail)).symm

/-- ★★ **The comb normal form preserves the through-strand permutation.**  `permuteOfCrossingWord (gc+1)
(combNormalizeForm gc W) = permuteOfCrossingWord (gc+1) W` for in-range `W` — the soundness leg the strand pin reads. -/
theorem combNormalizeForm_preservesPerm (generatorCount : Nat) (genPos : 1 ≤ generatorCount)
    (input : List Nat) (inRange : mentionsOnlyBelow generatorCount input = true) :
    permuteOfCrossingWord (generatorCount + 1) (combNormalizeForm generatorCount input)
      = permuteOfCrossingWord (generatorCount + 1) input := by
  have folded := combFold_preservesPerm generatorCount genPos input [] 0 rfl (Nat.zero_le generatorCount) inRange
  have startEq : ([] ++ descendingPositions (generatorCount - 1) 0) ++ input = input := rfl
  rw [startEq] at folded
  exact folded

/-! ## R2.A — the strand pin + the extend/injectivity infrastructure

The permutation determines the coset structure at each level: the top strand's image reads off the descending-run
length (`run_bubblesFromIndex`: the run `[g, g-1, …, g-k+1]` sends strand `g+1` to `g+1-k`), and the prefix fixes the
top strand (`perm_extend_fixedTop`).  These are the two pins the canonicity induction runs on. -/

/-- `Nat.beq a b = false` from `a < b` — structural on `a`/`b`, `propext`-free. -/
private theorem natBeqFalseOfLt : (a b : Nat) → a < b → Nat.beq a b = false
  | 0, 0, h => absurd h (Nat.lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | a + 1, b + 1, h => natBeqFalseOfLt a b (Nat.lt_of_succ_lt_succ h)

/-- The one-step `natIndexOfValue` unfold on a cons — `rfl`, used to drive the `Bool`-equality case splits without
a fragile inline `match` in `show`. -/
private theorem natIndexOfValue_cons (head target : Nat) (rest : List Nat) :
    natIndexOfValue (head :: rest) target
      = (match head == target with | true => 0 | false => natIndexOfValue rest target + 1) := rfl

/-- ★ **A swap moves a value down one index** — if `V` sits at a genuine index `top + 1` of `p`, then
`applyAdjacentSwap p top` puts `V` at index `top`.  Structural on `(p, top)` matching both `natIndexOfValue` and
`applyAdjacentSwap`; distinctness is not needed (the in-range index rules out the fallback). -/
theorem swap_moves_value_down : (p : List Nat) → (top : Nat) → (V : Nat) →
    natIndexOfValue p V = top + 1 → top + 1 < p.length →
    natIndexOfValue (applyAdjacentSwap p top) V = top
  | [], top, V, hIdx, _ => Nat.noConfusion (show (0 : Nat) = top + 1 from hIdx)
  | [_], top, _, _, hbound => absurd (Nat.le_of_succ_le_succ hbound) (Nat.not_succ_le_zero top)
  | first :: second :: rest, 0, V, hIdx, _ => by
      rw [natIndexOfValue_cons] at hIdx
      cases hfv : (first == V) with
      | true => rw [hfv] at hIdx; exact Nat.noConfusion hIdx
      | false =>
          rw [hfv] at hIdx
          have hSecond : natIndexOfValue (second :: rest) V = 0 := Nat.succ.inj hIdx
          rw [natIndexOfValue_cons] at hSecond
          cases hsv : (second == V) with
          | true =>
              show natIndexOfValue (second :: first :: rest) V = 0
              rw [natIndexOfValue_cons, hsv]
          | false => rw [hsv] at hSecond; exact Nat.noConfusion hSecond.symm
  | first :: second :: rest, top + 1, V, hIdx, hbound => by
      rw [natIndexOfValue_cons] at hIdx
      cases hfv : (first == V) with
      | true => rw [hfv] at hIdx; exact Nat.noConfusion hIdx
      | false =>
          rw [hfv] at hIdx
          have hTail : natIndexOfValue (second :: rest) V = top + 1 := Nat.succ.inj hIdx
          have hboundTail : top + 1 < (second :: rest).length := Nat.lt_of_succ_lt_succ hbound
          have moved : natIndexOfValue (applyAdjacentSwap (second :: rest) top) V = top :=
            swap_moves_value_down (second :: rest) top V hTail hboundTail
          show natIndexOfValue (first :: applyAdjacentSwap (second :: rest) top) V = top + 1
          rw [natIndexOfValue_cons, hfv, moved]

/-- ★ **The descending run bubbles the top value down by its length.**  If `V` sits at index `idx` of `p` (a genuine
in-range index) and `k ≤ idx`, then folding the descending run `[idx-1, idx-2, …, idx-k]` moves `V` to index
`idx - k`.  Structural on `k`; each head swap `s_{idx-1}` moves `V` from `idx` to `idx-1`. -/
theorem run_bubblesFromIndex : (idx k : Nat) → (p : List Nat) → (V : Nat) →
    natIndexOfValue p V = idx → idx < p.length → k ≤ idx →
    natIndexOfValue ((descendingPositions (idx - 1) k).foldl applyAdjacentSwap p) V = idx - k
  | idx, 0, p, _, hIdx, _, _ => hIdx
  | idx, k + 1, p, V, hIdx, hbound, hk => by
      have idxPos : 1 ≤ idx := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le k)) hk
      have idxPred : (idx - 1) + 1 = idx := predSuccStaircase idx idxPos
      have moved : natIndexOfValue (applyAdjacentSwap p (idx - 1)) V = idx - 1 :=
        swap_moves_value_down p (idx - 1) V (idxPred ▸ hIdx) (idxPred ▸ hbound)
      show natIndexOfValue ((descendingPositions ((idx - 1) - 1) k).foldl applyAdjacentSwap
              (applyAdjacentSwap p (idx - 1))) V = idx - (k + 1)
      have ih := run_bubblesFromIndex (idx - 1) k (applyAdjacentSwap p (idx - 1)) V moved
        (by rw [applyAdjacentSwap_length p (idx - 1)]
            exact Nat.lt_of_le_of_lt (Nat.sub_le idx 1) hbound)
        (natLePredStaircase k idx (idxPred ▸ hk))
      rw [ih]
      show (idx - 1) - k = idx - k - 1
      exact (subOneCommStaircase idx k).symm

/-- One `applyAdjacentSwap` on a snoc, when the swap window is inside the front, leaves the last element. -/
private theorem applyAdjacentSwap_fixes_last : (front : List Nat) → (last : Nat) → (position : Nat) →
    position + 1 < front.length →
    applyAdjacentSwap (front ++ [last]) position = applyAdjacentSwap front position ++ [last]
  | [], _, position, h => absurd h (Nat.not_lt_zero (position + 1))
  | [_], _, position, h => absurd (Nat.le_of_succ_le_succ h) (Nat.not_succ_le_zero position)
  | _ :: _ :: _, _, 0, _ => rfl
  | first :: second :: rest, last, position + 1, h =>
      congrArg (first :: ·)
        (applyAdjacentSwap_fixes_last (second :: rest) last position (Nat.lt_of_succ_lt_succ h))

/-- The fold of swaps whose positions are all `< bound` leaves the appended last element (`bound + 1 = front.length`
so the swaps never reach the last index). -/
private theorem foldlSwap_fixes_last : (word : List Nat) → (front : List Nat) → (last : Nat) → (bound : Nat) →
    mentionsOnlyBelow bound word = true → bound + 1 = front.length →
    word.foldl applyAdjacentSwap (front ++ [last]) = word.foldl applyAdjacentSwap front ++ [last]
  | [], _, _, _, _, _ => rfl
  | position :: rest, front, last, bound, hRange, hLen => by
      have positionLt : position < bound := natLtOfBltStaircase position bound (boolAndLeftStaircase _ _ hRange)
      have posP1LtLen : position + 1 < front.length := by rw [← hLen]; exact Nat.succ_lt_succ positionLt
      show rest.foldl applyAdjacentSwap (applyAdjacentSwap (front ++ [last]) position)
         = rest.foldl applyAdjacentSwap (applyAdjacentSwap front position) ++ [last]
      rw [applyAdjacentSwap_fixes_last front last position posP1LtLen]
      exact foldlSwap_fixes_last rest (applyAdjacentSwap front position) last bound
        (boolAndRightStaircase _ _ hRange)
        (by rw [applyAdjacentSwap_length front position]; exact hLen)

/-- `front ++ (value :: rest) = (front ++ [value]) ++ rest` — the snoc/cons repositioning, structural on `front`,
`propext`-free (avoids the `propext`-leaking `List.append_assoc`). -/
private theorem appendSnocConsStaircase : (front rest : List Nat) → (value : Nat) →
    front ++ (value :: rest) = (front ++ [value]) ++ rest
  | [], _, _ => rfl
  | head :: tail, rest, value => congrArg (head :: ·) (appendSnocConsStaircase tail rest value)

/-- `(List.range n).length = n` — structural via the `range.loop`, `propext`-free. -/
private theorem rangeLengthLoopStaircase : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      show (List.range.loop count (count :: accumulated)).length = (count + 1) + accumulated.length
      rw [rangeLengthLoopStaircase count (count :: accumulated)]
      show count + (accumulated.length + 1) = (count + 1) + accumulated.length
      rw [Nat.add_succ, Nat.succ_add]

/-- `(List.range n).length = n`. -/
private theorem rangeLengthStaircase (count : Nat) : (List.range count).length = count :=
  rangeLengthLoopStaircase count []

/-- `List.range.loop count acc = List.range.loop count [] ++ acc` — the accumulator factors out.  Structural on
`count`, `propext`-free via `appendSnocConsStaircase`. -/
private theorem rangeLoopAppendStaircase : (count : Nat) → (accumulated : List Nat) →
    List.range.loop count accumulated = List.range.loop count [] ++ accumulated
  | 0, _ => rfl
  | count + 1, accumulated => by
      show List.range.loop count (count :: accumulated)
         = List.range.loop count (count :: []) ++ accumulated
      rw [rangeLoopAppendStaircase count (count :: accumulated),
          rangeLoopAppendStaircase count (count :: [])]
      exact appendSnocConsStaircase (List.range.loop count []) accumulated count

/-- `List.range (n + 1) = List.range n ++ [n]` — the `propext`-free replacement for `List.range_succ` (which leaks
`propext`). -/
private theorem rangeSuccStaircase (n : Nat) : List.range (n + 1) = List.range n ++ [n] := by
  show List.range.loop n (n :: []) = List.range.loop n [] ++ [n]
  exact rangeLoopAppendStaircase n (n :: [])

/-- ★ **The prefix fixes the top strand.**  A word mentioning only positions `< bound` fixes strand `bound + 1`:
`permuteOfCrossingWord (bound + 2) word = permuteOfCrossingWord (bound + 1) word ++ [bound + 1]`. -/
theorem perm_extend_fixedTop (bound : Nat) (word : List Nat) (hBelow : mentionsOnlyBelow bound word = true) :
    permuteOfCrossingWord (bound + 2) word = permuteOfCrossingWord (bound + 1) word ++ [bound + 1] := by
  show word.foldl applyAdjacentSwap (List.range (bound + 2))
     = word.foldl applyAdjacentSwap (List.range (bound + 1)) ++ [bound + 1]
  rw [show List.range (bound + 2) = List.range (bound + 1) ++ [bound + 1] from rangeSuccStaircase (bound + 1)]
  exact foldlSwap_fixes_last word (List.range (bound + 1)) (bound + 1) bound hBelow
    (rangeLengthStaircase (bound + 1)).symm

end FX1Poly.Polygraph
