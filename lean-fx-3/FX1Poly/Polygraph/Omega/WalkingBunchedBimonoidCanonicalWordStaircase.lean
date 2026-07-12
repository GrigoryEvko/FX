import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidPermMatrixExtractorKit

/-! # Polygraph/Omega/WalkingBunchedBimonoidCanonicalWordStaircase — the canonical reduced-word engine: the
Coxeter–Moser comb, the recursive staircase, and the pure permutation round-trip (WP-PROP r14, #2033)

★ **THE r14 CANONICAL WORD — the Omega mirror of the Brauer `recComb` staircase, the pure `List Nat` layer of
`CoxeterWordUnique`.**  r13 shipped the perm-middle matrix→`List Nat` reduction
(`evalCell (permWord w1) = evalCell (permWord w2) -> permOfWord w1 = permOfWord w2`, the extractor composed with
`permMatrixInjective`).  The next node of the goal chain is `permOfWord w1 = permOfWord w2 -> recComb (W-1) w1 =
recComb (W-1) w2` — the canonicity of the recursive-comb staircase.  This file ships that staircase's DATA engine
and the pure soundness leg it rests on: the Coxeter–Moser four-case comb-insertion (`combInsertData`), the
one-level normal form (`combNormalizeForm`), the recursive staircase (`recComb`, the Regev–Roichman / Lehmer
reduced word — a UNIQUE reduced word per permutation), and the KEYSTONE

  `combInsertData_realizesSwap` — each comb-insert step applies exactly ONE adjacent swap to the running
  through-strand permutation (four branches COMMUTE / EXTEND / CANCEL / CARRY)

folded to `combNormalizeForm_preservesPerm` — one comb level preserves the permutation.  All PURE `List Nat`
over the shipped Omega symmetric-group engine (`bunchedBimonoidApplyAdjacentSwap` / `bunchedBimonoidPermOfWord`,
byte-identical to the Brauer canonicity lane, re-derived in-namespace — never imported).  ZERO CONV: the cell /
`SaturatedConvOverWithId` layer is untouched here (the `recCombConv` CONV-fold mirror and its `permWord_append`
spelling bridge are the r15 residual, named at the foot of this file).

## What this round is NOT (the honest scope)

This is the pure-permutation soundness leg, NOT the CONV-fold.  The `combInsertStepConv` single-letter CONV
insertion (firing the r9 `bunchedBimonoid{YangBaxter,Involution,DistantSwap}AtPosition` moves through a
`permWord`/`sigmaAt` chain) needs the vcomp-vs-list-append spelling bridge (the fixed base legs
`bunchedBimonoidSigmaInvolutionLeftLeg = vcomp addSigmaGen addSigmaGen` are NOT the `sigmaAt`-chain
`vcomp (sigmaAt w k) (sigmaAt w k)` definitionally — only up to `whiskerLeft/RightFunctorial`); that bridge is the
r15 headline.  The star does NOT flip: no hypothesis-free inhabitant of
`bunchedBimonoidStarStatementAdditiveWellTyped` is produced, and every star / residual marker stays byte-intact
`= false`.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin.  Mirror of the Brauer canonicity lane (`WiringDescStaircaseCanonical`);
never imported from it. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

/-! The width-4/5 permutation round-trip `rfl` pins exceed the default heartbeat budget; the raise is a compute
allowance only, the proof terms stay `Eq.refl` / structural, axiom-free (uniform with the r6-r13 lane files). -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # C0 — THE CANONICAL-WORD DATA ENGINE (the Coxeter–Moser comb + the recursive staircase)
    # =========================================================================================

★ Verbatim ports (renamed into the Omega namespace) of the Brauer `descendingPositions` / `mentionsOnlyBelow` /
`combInsertData` / `combNormalizeForm` / `recComb`, over the SHIPPED Omega symmetric-group engine
`bunchedBimonoidApplyAdjacentSwap` / `bunchedBimonoidPermOfWord`. -/

/-- ★ **A descending run of positions** — `descendingPositions top count = [top, top-1, …, top-count+1]`, the
`count` topmost generator indices at-or-below `top`.  Structural on `count`; the run of the Coxeter–Moser coset is
`descendingPositions (width - 2) count` (anchored at the top generator `s_{width-2}`). -/
def bunchedBimonoidDescendingPositions (top : Nat) : Nat → List Nat
  | 0 => []
  | count + 1 => top :: bunchedBimonoidDescendingPositions (top - 1) count

/-- ★ **The `mentionsOnlyBelow` certificate** — every position of the word is strictly below `bound`.  A full-enum
`Bool` all-scan (`Nat.blt`), propext-clean (matching the Kit's `bunchedBimonoidPositionsValid` house style).  For
the comb the prefix carries `mentionsOnlyBelow (width - 2) prefix = true` — the Björner–Brenti right-descent
transversal condition. -/
def bunchedBimonoidMentionsOnlyBelow (bound : Nat) : List Nat → Bool
  | [] => true
  | position :: rest => Nat.blt position bound && bunchedBimonoidMentionsOnlyBelow bound rest

/-- ★ **One data-only comb-insertion step** — the four Coxeter–Moser side conditions on `letter + run` versus
`generatorCount`: COMMUTE (snoc the letter, keep the run), EXTEND (grow the run), CANCEL (shrink the run), CARRY
(snoc `letter - 1`, keep the run).  The pure four-case dispatch the staircase folds. -/
def bunchedBimonoidCombInsertData (generatorCount : Nat) (state : List Nat × Nat) (letter : Nat) :
    List Nat × Nat :=
  if letter + state.2 + 2 ≤ generatorCount then (state.1 ++ [letter], state.2)
  else if letter + state.2 + 1 = generatorCount then (state.1, state.2 + 1)
  else if letter + state.2 = generatorCount then (state.1, state.2 - 1)
  else (state.1 ++ [letter - 1], state.2)

/-- ★ **The one-level comb normal form** — fold the data step from the empty state, then read off
`combPrefix ++ descendingRun`.  The DATA mirror of the single-level `combNormalizeForm_conv`. -/
def bunchedBimonoidCombNormalizeForm (generatorCount : Nat) (input : List Nat) : List Nat :=
  let result := input.foldl (bunchedBimonoidCombInsertData generatorCount) ([], 0)
  result.1 ++ bunchedBimonoidDescendingPositions (generatorCount - 1) result.2

/-- ★★ **The recursive comb staircase** — at level `generatorCount + 1` run the DATA comb fold, then recurse on the
still-uncanonical prefix at level `generatorCount`.  Structural recursion on the generator count (the second
argument is free), so it computes and needs no fuel.  The image is the Regev–Roichman canonical presentation
`w_1 ⋯ w_{width-1}` — a UNIQUE reduced word per permutation. -/
def bunchedBimonoidRecComb : Nat → List Nat → List Nat
  | 0, _ => []
  | generatorCount + 1, input =>
      bunchedBimonoidRecComb generatorCount
          (input.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).1
        ++ bunchedBimonoidDescendingPositions generatorCount
            (input.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).2

/-! # =========================================================================================
    # C0 — TRUTH-PROBES (the canonical-word engine computes; run standalone BEFORE any proof)
    # =========================================================================================

★ The 6 width-3 permutations' realizing words fold to their canonical staircases, and every canonical word
round-trips its permutation (`permOfWord (recComb w) = permOfWord w`). -/

#eval bunchedBimonoidRecComb 2 []          -- perm [0,1,2] -> []
#eval bunchedBimonoidRecComb 2 [1]         -- perm [0,2,1] -> [1]
#eval bunchedBimonoidRecComb 2 [0]         -- perm [1,0,2] -> [0]
#eval bunchedBimonoidRecComb 2 [0, 1]      -- perm [1,2,0] -> [0,1]
#eval bunchedBimonoidRecComb 2 [1, 0]      -- perm [2,0,1] -> [1,0]
#eval bunchedBimonoidRecComb 2 [0, 1, 0]   -- perm [2,1,0] -> [0,1,0]
#eval bunchedBimonoidRecComb 2 [1, 0, 1]   -- perm [2,1,0] -> [0,1,0]  (the braid pair UNIFIES)
#eval bunchedBimonoidRecComb 3 [2, 0, 1, 2]      -- perm [1,3,2,0] -> [0,1,2,1]
#eval bunchedBimonoidPermOfWord (bunchedBimonoidRecComb 3 [2, 0, 1, 2]) 4
#eval bunchedBimonoidPermOfWord [2, 0, 1, 2] 4

/-! # =========================================================================================
    # C0 — THE `rfl` PINS (widths <= 4/5; the engine reaches the recon table on the nose)
    # =========================================================================================
-/

/-- ★ **The r9 jam word `[2, 0, 1, 2]` reaches the staircase `[0, 1, 2, 1]`** (`rfl`) — the exact canonical word the
Brauer insertion residual could not reach, computed by the recursive comb at generator count 3. -/
theorem bunchedBimonoidRecComb_r9_stuck_word : bunchedBimonoidRecComb 3 [2, 0, 1, 2] = [0, 1, 2, 1] := rfl

/-- ★★ **The r11 residual pair `[1,2,0,1,2]` / `[0,1,2,0,1]` UNIFY under the recursive comb** — both reach the
common staircase `[0, 1, 0, 2, 1]` (`rfl`), while the ONE-level comb keeps them distinct
(`combNormalizeForm 4 [1,2,0,1,2] = [1,2,0,1,2]` below).  This is exactly why the recursion is load-bearing for the
equal-permutation flip. -/
theorem bunchedBimonoidRecComb_r11_left : bunchedBimonoidRecComb 4 [1, 2, 0, 1, 2] = [0, 1, 0, 2, 1] := rfl

/-- The right member of the r11 pair reaches the SAME staircase (`rfl`). -/
theorem bunchedBimonoidRecComb_r11_right : bunchedBimonoidRecComb 4 [0, 1, 2, 0, 1] = [0, 1, 0, 2, 1] := rfl

/-- ★ **The one-level comb does NOT unify the r11 pair** — it fixes `[1,2,0,1,2]` (`rfl`); only the recursion
collapses it to `[0,1,0,2,1]`.  The recon's load-bearing witness for the recursion. -/
theorem bunchedBimonoidCombNormalizeForm_r11_left_fixed :
    bunchedBimonoidCombNormalizeForm 4 [1, 2, 0, 1, 2] = [1, 2, 0, 1, 2] := rfl

/-- The r9 braid pair `[0,1,0]` / `[1,0,1]` (both realizing the width-3 reversal `[2,1,0]`) UNIFY to `[0,1,0]`
under the recursive comb at generator count 2 (`rfl`). -/
theorem bunchedBimonoidRecComb_braidPairUnifies :
    bunchedBimonoidRecComb 2 [0, 1, 0] = bunchedBimonoidRecComb 2 [1, 0, 1] := rfl

/-- ★★ **The recursive comb ROUND-TRIPS its permutation** — the staircase of `[2,0,1,2]` realizes the same
through-strand permutation as `[2,0,1,2]` itself (`rfl`, width 4).  The pure soundness the general
`combNormalizeForm_preservesPerm` (r15) generalises. -/
theorem bunchedBimonoidRecComb_r9_roundTrip :
    bunchedBimonoidPermOfWord (bunchedBimonoidRecComb 3 [2, 0, 1, 2]) 4
      = bunchedBimonoidPermOfWord [2, 0, 1, 2] 4 := rfl

/-- The r9 braid pair shares its through-strand permutation `[2,1,0]` (`rfl`) — the pure `List Nat` read-off the
staircase then unifies. -/
theorem bunchedBimonoidBraidPairPermShared :
    bunchedBimonoidPermOfWord [0, 1, 0] 3 = bunchedBimonoidPermOfWord [1, 0, 1] 3 := rfl

/-! ## The C0 honesty marker -/

/-- ★★★ **ESTABLISHED (C0) — the canonical-word DATA engine is SHIPPED and truth-probed.**  `= true` records the
Coxeter–Moser comb (`bunchedBimonoidCombInsertData`, four cases), the one-level normal form
(`bunchedBimonoidCombNormalizeForm`), the recursive staircase (`bunchedBimonoidRecComb`, the Regev–Roichman /
Lehmer reduced word), and the descending run (`bunchedBimonoidDescendingPositions`) + the `mentionsOnlyBelow`
certificate, all over the SHIPPED Omega symmetric-group engine (`bunchedBimonoidApplyAdjacentSwap` /
`bunchedBimonoidPermOfWord`, byte-identical to the Brauer canonicity lane).  Truth-probed + pinned by `rfl`: the r9
jam word `[2,0,1,2]` reaches `[0,1,2,1]`, the r11 pair `[1,2,0,1,2]` / `[0,1,2,0,1]` UNIFY to `[0,1,0,2,1]` (the
one-level comb keeping them distinct), the r9 braid pair `[0,1,0]` / `[1,0,1]` unify to `[0,1,0]`, and the
staircase ROUND-TRIPS its permutation (`recComb_r9_roundTrip`).  The Omega mirror of the Brauer `recComb`
staircase.  Zero-axiom (per-decl `#assert_no_axioms` + independent `#print axioms` in the twin). -/
def fxBunchedBimonoid_canonicalWordStaircaseEngineShipped : Bool := true

/-! # =========================================================================================
    # C1 — THE PURE SOUNDNESS LEG: each comb-insert step realizes ONE adjacent swap
    # =========================================================================================

★ Verbatim ports (renamed) of the Brauer `combInsertData_realizesSwap` / `combFold_preservesPerm` /
`combNormalizeForm_preservesPerm` and their pure support: the arithmetic / list helpers, the four `applyAdjacentSwap`
identities (cons-succ peel, involution, disjoint commutation, braid), the two run-commutation lemmas, and the
permutation-carry crux `carry_perm`.  ALL over the SHIPPED Omega engine, ZERO CONV. -/

/-! ## C1.arith — the propext-clean arithmetic backbone -/

private theorem bunchedBimonoidSubTwoAddTwoStaircase : (value : Nat) → 2 ≤ value → value - 2 + 2 = value
  | 0, twoLe => absurd twoLe (by decide)
  | 1, twoLe => absurd twoLe (by decide)
  | _ + 2, _ => rfl

private theorem bunchedBimonoidPredSuccStaircase : (index : Nat) → 1 ≤ index → index - 1 + 1 = index
  | 0, positive => absurd positive (by decide)
  | _ + 1, _ => rfl

private theorem bunchedBimonoidNatLePredStaircase : (lower top : Nat) → lower + 1 ≤ top → lower ≤ top - 1
  | lower, 0, h => absurd h (Nat.not_succ_le_zero lower)
  | _, _ + 1, h => Nat.le_of_succ_le_succ h

private theorem bunchedBimonoidNatLeOfAddLeAddRightStaircase :
    (m n k : Nat) → m + k ≤ n + k → m ≤ n
  | _, _, 0, h => h
  | m, n, k + 1, h => bunchedBimonoidNatLeOfAddLeAddRightStaircase m n k (Nat.le_of_succ_le_succ h)

private theorem bunchedBimonoidNatLeOfAddLeAddLeftStaircase (k m n : Nat) (h : k + m ≤ k + n) : m ≤ n :=
  bunchedBimonoidNatLeOfAddLeAddRightStaircase m n k
    (by rw [Nat.add_comm m k, Nat.add_comm n k]; exact h)

private theorem bunchedBimonoidCommuteHighEqStaircase :
    (low high : Nat) → low + 2 ≤ high → low + (high - low - 2) + 2 = high
  | 0, high, hLe => by
      rw [Nat.zero_add]
      exact bunchedBimonoidSubTwoAddTwoStaircase high hLe
  | _ + 1, 0, hLe => absurd hLe (Nat.not_succ_le_zero _)
  | low + 1, high + 1, hLe => by
      have inner : low + (high - low - 2) + 2 = high :=
        bunchedBimonoidCommuteHighEqStaircase low high (Nat.le_of_succ_le_succ hLe)
      rw [Nat.succ_sub_succ, Nat.succ_add, Nat.succ_add]
      exact congrArg Nat.succ inner

private theorem bunchedBimonoidSubOneCommStaircase : (top count : Nat) → top - count - 1 = top - 1 - count
  | _, 0 => rfl
  | top, count + 1 => congrArg Nat.pred (bunchedBimonoidSubOneCommStaircase top count)

private theorem bunchedBimonoidNatAddSubCancelStaircase : (base offset : Nat) → base + offset - offset = base
  | _, 0 => rfl
  | base, offset + 1 =>
      (Nat.succ_sub_succ (base + offset) offset).trans (bunchedBimonoidNatAddSubCancelStaircase base offset)

private theorem bunchedBimonoidNatEqSubOfAddEqStaircase (base offset total : Nat) (h : base + offset = total) :
    base = total - offset := by
  rw [← h]; exact (bunchedBimonoidNatAddSubCancelStaircase base offset).symm

private theorem bunchedBimonoidSuccAddSwapStaircase :
    (value offset : Nat) → (value + 1) + offset = (value + offset) + 1
  | _, 0 => rfl
  | value, offset + 1 => congrArg Nat.succ (bunchedBimonoidSuccAddSwapStaircase value offset)

/-! ## C1.list — the propext-clean list backbone -/

private theorem bunchedBimonoidAppendAssocStaircase {alpha : Type _} :
    (front mid back : List alpha) → (front ++ mid) ++ back = front ++ (mid ++ back)
  | [], _, _ => rfl
  | head :: rest, mid, back => congrArg (head :: ·) (bunchedBimonoidAppendAssocStaircase rest mid back)

private theorem bunchedBimonoidAppendNilStaircase : (list : List Nat) → list ++ [] = list
  | [] => rfl
  | head :: rest => congrArg (head :: ·) (bunchedBimonoidAppendNilStaircase rest)

/-- The descending run's distinguished LAST element is `top - count`. -/
private theorem bunchedBimonoidDescendingPositionsSnocStaircase : (top count : Nat) →
    bunchedBimonoidDescendingPositions top count ++ [top - count]
      = bunchedBimonoidDescendingPositions top (count + 1)
  | _, 0 => rfl
  | top, count + 1 => by
      have idxEq : top - (count + 1) = (top - 1) - count := bunchedBimonoidSubOneCommStaircase top count
      have inner : bunchedBimonoidDescendingPositions (top - 1) count ++ [top - (count + 1)]
          = bunchedBimonoidDescendingPositions (top - 1) (count + 1) := by
        rw [idxEq]; exact bunchedBimonoidDescendingPositionsSnocStaircase (top - 1) count
      show top :: (bunchedBimonoidDescendingPositions (top - 1) count ++ [top - (count + 1)])
         = top :: bunchedBimonoidDescendingPositions (top - 1) (count + 1)
      exact congrArg (top :: ·) inner

/-- `foldl bunchedBimonoidApplyAdjacentSwap` splits over a list concatenation.  Structural on the prefix. -/
private theorem bunchedBimonoidFoldlAppendSwapStaircase : (prefixList suffixList init : List Nat) →
    (prefixList ++ suffixList).foldl bunchedBimonoidApplyAdjacentSwap init
      = suffixList.foldl bunchedBimonoidApplyAdjacentSwap (prefixList.foldl bunchedBimonoidApplyAdjacentSwap init)
  | [], _, _ => rfl
  | head :: rest, suffixList, init =>
      bunchedBimonoidFoldlAppendSwapStaircase rest suffixList (bunchedBimonoidApplyAdjacentSwap init head)

/-- `bunchedBimonoidPermOfWord` splits over concatenation — the append law. -/
theorem bunchedBimonoidPermOfWordAppendSplit (width : Nat) (front back : List Nat) :
    bunchedBimonoidPermOfWord (front ++ back) width
      = back.foldl bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidPermOfWord front width) :=
  bunchedBimonoidFoldlAppendSwapStaircase front back (List.range width)

/-- The snoc fold peels the last swap. -/
private theorem bunchedBimonoidFoldlSwapSnocStaircase : (positions basePerm : List Nat) → (position : Nat) →
    (positions ++ [position]).foldl bunchedBimonoidApplyAdjacentSwap basePerm
      = bunchedBimonoidApplyAdjacentSwap (positions.foldl bunchedBimonoidApplyAdjacentSwap basePerm) position
  | [], _, _ => rfl
  | head :: rest, basePerm, position =>
      bunchedBimonoidFoldlSwapSnocStaircase rest (bunchedBimonoidApplyAdjacentSwap basePerm head) position

/-- ★ **Appending one position applies one adjacent swap to the realized permutation** — the snoc law for
`bunchedBimonoidPermOfWord`. -/
theorem bunchedBimonoidPermOfWordSnoc (width : Nat) (positions : List Nat) (position : Nat) :
    bunchedBimonoidPermOfWord (positions ++ [position]) width
      = bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidPermOfWord positions width) position :=
  bunchedBimonoidFoldlSwapSnocStaircase positions (List.range width) position

/-! ## C1.swap — the four `applyAdjacentSwap` identities (peel / involution / disjoint / braid) -/

private theorem bunchedBimonoidApplyAdjacentSwapConsSuccStaircase :
    (headElement : Nat) → (list : List Nat) → (position : Nat) →
    bunchedBimonoidApplyAdjacentSwap (headElement :: list) (position + 1)
      = headElement :: bunchedBimonoidApplyAdjacentSwap list position
  | _, [], _ => rfl
  | _, _ :: _, _ => rfl

/-- ★ `bunchedBimonoidApplyAdjacentSwap` is an involution — applying the same adjacent swap twice restores the list. -/
theorem bunchedBimonoidApplyAdjacentSwapInvolutive : (perm : List Nat) → (position : Nat) →
    bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidApplyAdjacentSwap perm position) position = perm
  | [], _ => rfl
  | _ :: [], _ => rfl
  | _ :: _ :: _, 0 => rfl
  | first :: second :: rest, position + 1 => by
      rw [bunchedBimonoidApplyAdjacentSwapConsSuccStaircase first (second :: rest) position,
        bunchedBimonoidApplyAdjacentSwapConsSuccStaircase first
          (bunchedBimonoidApplyAdjacentSwap (second :: rest) position) position,
        bunchedBimonoidApplyAdjacentSwapInvolutive (second :: rest) position]

/-- ★★ **Disjoint adjacent swaps COMMUTE** — a swap at `posLow` and a swap at the distant `posLow + gap + 2` apply
in either order.  Structural on `perm` / `posLow`. -/
theorem bunchedBimonoidApplyAdjacentSwapSwapDisjoint :
    (perm : List Nat) → (posLow gap : Nat) →
    bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidApplyAdjacentSwap perm posLow) (posLow + gap + 2)
      = bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidApplyAdjacentSwap perm (posLow + gap + 2)) posLow
  | [], _, _ => rfl
  | _ :: [], _, _ => rfl
  | first :: second :: rest, 0, gap => by
      show second :: bunchedBimonoidApplyAdjacentSwap (first :: rest) (0 + gap + 1)
          = bunchedBimonoidApplyAdjacentSwap
              (first :: bunchedBimonoidApplyAdjacentSwap (second :: rest) (0 + gap + 1)) 0
      rw [bunchedBimonoidApplyAdjacentSwapConsSuccStaircase second rest (0 + gap),
        bunchedBimonoidApplyAdjacentSwapConsSuccStaircase first rest (0 + gap)]
      rfl
  | first :: second :: rest, posLow + 1, gap => by
      show bunchedBimonoidApplyAdjacentSwap
              (first :: bunchedBimonoidApplyAdjacentSwap (second :: rest) posLow) (posLow + 1 + gap + 1 + 1)
          = bunchedBimonoidApplyAdjacentSwap
              (first :: bunchedBimonoidApplyAdjacentSwap (second :: rest) (posLow + 1 + gap + 1)) (posLow + 1)
      rw [bunchedBimonoidApplyAdjacentSwapConsSuccStaircase first
            (bunchedBimonoidApplyAdjacentSwap (second :: rest) posLow) (posLow + 1 + gap + 1),
        bunchedBimonoidApplyAdjacentSwapConsSuccStaircase first
          (bunchedBimonoidApplyAdjacentSwap (second :: rest) (posLow + 1 + gap + 1)) posLow,
        bunchedBimonoidSuccAddSwapStaircase posLow gap]
      exact congrArg (first :: ·) (bunchedBimonoidApplyAdjacentSwapSwapDisjoint (second :: rest) posLow gap)

/-- ★★ **The braid relation on the one-line permutation** (`s_d s_{d+1} s_d = s_{d+1} s_d s_{d+1}`) — for a position
with its full braid window in range (`position + 2 < perm.length`).  Structural on `perm` / `position`. -/
theorem bunchedBimonoidApplyAdjacentSwapBraid :
    (perm : List Nat) → (position : Nat) → position + 2 < perm.length →
    bunchedBimonoidApplyAdjacentSwap
        (bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidApplyAdjacentSwap perm position) (position + 1)) position
      = bunchedBimonoidApplyAdjacentSwap
        (bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidApplyAdjacentSwap perm (position + 1)) position)
          (position + 1)
  | [], position, inRange => absurd inRange (Nat.not_lt_zero (position + 2))
  | _ :: [], position, inRange => absurd inRange (Nat.not_lt.mpr (Nat.le_add_left 1 (position + 1)))
  | _ :: _ :: [], position, inRange => absurd inRange (Nat.not_lt.mpr (Nat.le_add_left 2 position))
  | _ :: _ :: _ :: _, 0, _ => rfl
  | first :: second :: third :: rest, position + 1, inRange => by
      have inRangeTail : position + 2 < (second :: third :: rest).length :=
        Nat.lt_of_succ_lt_succ inRange
      rw [bunchedBimonoidApplyAdjacentSwapConsSuccStaircase first (second :: third :: rest) position,
        bunchedBimonoidApplyAdjacentSwapConsSuccStaircase first
          (bunchedBimonoidApplyAdjacentSwap (second :: third :: rest) position) (position + 1),
        bunchedBimonoidApplyAdjacentSwapConsSuccStaircase first
          (bunchedBimonoidApplyAdjacentSwap
            (bunchedBimonoidApplyAdjacentSwap (second :: third :: rest) position) (position + 1)) position,
        bunchedBimonoidApplyAdjacentSwapConsSuccStaircase first (second :: third :: rest) (position + 1),
        bunchedBimonoidApplyAdjacentSwapConsSuccStaircase first
          (bunchedBimonoidApplyAdjacentSwap (second :: third :: rest) (position + 1)) position,
        bunchedBimonoidApplyAdjacentSwapConsSuccStaircase first
          (bunchedBimonoidApplyAdjacentSwap
            (bunchedBimonoidApplyAdjacentSwap (second :: third :: rest) (position + 1)) position) (position + 1)]
      exact congrArg (first :: ·) (bunchedBimonoidApplyAdjacentSwapBraid (second :: third :: rest) position inRangeTail)

/-- ★ **Distant adjacent swaps commute, in `i + 2 ≤ j` form.** -/
theorem bunchedBimonoidApplyAdjacentSwapCommuteOfLe (perm : List Nat) (low high : Nat) (dist : low + 2 ≤ high) :
    bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidApplyAdjacentSwap perm low) high
      = bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidApplyAdjacentSwap perm high) low := by
  have highEq : low + (high - low - 2) + 2 = high := bunchedBimonoidCommuteHighEqStaircase low high dist
  have shipped := bunchedBimonoidApplyAdjacentSwapSwapDisjoint perm low (high - low - 2)
  rw [highEq] at shipped
  exact shipped

/-! ## C1.run — a swap ABOVE / BELOW a descending run commutes past the whole run fold -/

/-- ★ **A swap ABOVE a descending run commutes past the whole run fold.**  Structural on `count`. -/
theorem bunchedBimonoidSwapCommutesRunAbove (letter : Nat) :
    (runTop count : Nat) → (perm : List Nat) → letter + count + 1 ≤ runTop →
    (bunchedBimonoidDescendingPositions runTop count).foldl bunchedBimonoidApplyAdjacentSwap
        (bunchedBimonoidApplyAdjacentSwap perm letter)
      = bunchedBimonoidApplyAdjacentSwap
          ((bunchedBimonoidDescendingPositions runTop count).foldl bunchedBimonoidApplyAdjacentSwap perm) letter
  | _, 0, _, _ => rfl
  | runTop, count + 1, perm, hLe => by
      have topDistant : letter + 2 ≤ runTop :=
        Nat.le_trans (Nat.add_le_add_left (Nat.le_add_left 2 count) letter) hLe
      show (bunchedBimonoidDescendingPositions (runTop - 1) count).foldl bunchedBimonoidApplyAdjacentSwap
              (bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidApplyAdjacentSwap perm letter) runTop)
          = bunchedBimonoidApplyAdjacentSwap
              ((bunchedBimonoidDescendingPositions (runTop - 1) count).foldl bunchedBimonoidApplyAdjacentSwap
                (bunchedBimonoidApplyAdjacentSwap perm runTop)) letter
      rw [bunchedBimonoidApplyAdjacentSwapCommuteOfLe perm letter runTop topDistant]
      exact bunchedBimonoidSwapCommutesRunAbove letter (runTop - 1) count
        (bunchedBimonoidApplyAdjacentSwap perm runTop)
        (by
          have e : runTop - 1 + 1 = runTop := Nat.succ_pred_eq_of_pos (Nat.lt_of_lt_of_le
            (Nat.lt_of_lt_of_le (Nat.zero_lt_succ letter) (Nat.le_add_right (letter + 1) 1)) topDistant)
          have hStep : letter + count + 1 + 1 ≤ runTop := hLe
          have : letter + count + 1 ≤ runTop - 1 := by
            rw [← e] at hStep; exact Nat.le_of_succ_le_succ hStep
          exact this)

/-- ★ **A swap BELOW a descending run commutes past the whole run fold.**  Structural on `count`. -/
theorem bunchedBimonoidSwapCommutesRunBelow (letter : Nat) :
    (runTop count : Nat) → (perm : List Nat) → runTop + 2 ≤ letter →
    (bunchedBimonoidDescendingPositions runTop count).foldl bunchedBimonoidApplyAdjacentSwap
        (bunchedBimonoidApplyAdjacentSwap perm letter)
      = bunchedBimonoidApplyAdjacentSwap
          ((bunchedBimonoidDescendingPositions runTop count).foldl bunchedBimonoidApplyAdjacentSwap perm) letter
  | _, 0, _, _ => rfl
  | runTop, count + 1, perm, hLe => by
      show (bunchedBimonoidDescendingPositions (runTop - 1) count).foldl bunchedBimonoidApplyAdjacentSwap
              (bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidApplyAdjacentSwap perm letter) runTop)
          = bunchedBimonoidApplyAdjacentSwap
              ((bunchedBimonoidDescendingPositions (runTop - 1) count).foldl bunchedBimonoidApplyAdjacentSwap
                (bunchedBimonoidApplyAdjacentSwap perm runTop)) letter
      rw [(bunchedBimonoidApplyAdjacentSwapCommuteOfLe perm runTop letter hLe).symm]
      exact bunchedBimonoidSwapCommutesRunBelow letter (runTop - 1) count
        (bunchedBimonoidApplyAdjacentSwap perm runTop)
        (Nat.le_trans (Nat.add_le_add_right (Nat.sub_le runTop 1) 2) hLe)

/-- ★★ **The permutation-carry identity** `s_{letter-1} · run = run · s_letter`.  Induction on `runLen` mirroring the
Brauer `carryIntoRun`: STEP peels `s_top` by disjoint commutation; BASE (`letter = top`) braids the pivot and commutes
past the lower sub-run. -/
theorem bunchedBimonoidCarryPerm (letter : Nat) (letterPos : 1 ≤ letter) :
    (top runLen : Nat) → (perm : List Nat) → letter ≤ top → runLen ≤ top + 1 →
    top + 2 ≤ letter + runLen → top + 2 ≤ perm.length →
    (bunchedBimonoidDescendingPositions top runLen).foldl bunchedBimonoidApplyAdjacentSwap
        (bunchedBimonoidApplyAdjacentSwap perm (letter - 1))
      = bunchedBimonoidApplyAdjacentSwap
          ((bunchedBimonoidDescendingPositions top runLen).foldl bunchedBimonoidApplyAdjacentSwap perm) letter
  | top, 0, _, letterLeTop, _, aboveBottom, _ =>
      absurd (Nat.le_trans (Nat.le_trans aboveBottom letterLeTop) (Nat.le_succ top))
        (Nat.not_succ_le_self (top + 1))
  | top, runLen + 1, perm, letterLeTop, runLenLe, aboveBottom, lenOk => by
      rcases Nat.lt_or_ge letter top with ltTop | geTop
      · have topPos : 1 ≤ top := Nat.le_trans letterPos (Nat.le_of_lt ltTop)
        have letterM1Distant : (letter - 1) + 2 ≤ top := by
          rw [show (letter - 1) + 2 = letter + 1 from
            congrArg Nat.succ (bunchedBimonoidPredSuccStaircase letter letterPos)]
          exact ltTop
        show (bunchedBimonoidDescendingPositions (top - 1) runLen).foldl bunchedBimonoidApplyAdjacentSwap
                (bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidApplyAdjacentSwap perm (letter - 1)) top)
            = bunchedBimonoidApplyAdjacentSwap
                ((bunchedBimonoidDescendingPositions (top - 1) runLen).foldl bunchedBimonoidApplyAdjacentSwap
                  (bunchedBimonoidApplyAdjacentSwap perm top)) letter
        rw [bunchedBimonoidApplyAdjacentSwapCommuteOfLe perm (letter - 1) top letterM1Distant]
        exact bunchedBimonoidCarryPerm letter letterPos (top - 1) runLen (bunchedBimonoidApplyAdjacentSwap perm top)
          (bunchedBimonoidNatLePredStaircase letter top ltTop)
          (by rw [bunchedBimonoidPredSuccStaircase top topPos]; exact Nat.le_of_succ_le_succ runLenLe)
          (by
            have e : top - 1 + 2 = top + 1 := congrArg Nat.succ (bunchedBimonoidPredSuccStaircase top topPos)
            rw [e]; exact Nat.le_of_succ_le_succ aboveBottom)
          (by
            rw [bunchedBimonoidApplyAdjacentSwapLength perm top,
              show top - 1 + 2 = top + 1 from congrArg Nat.succ (bunchedBimonoidPredSuccStaircase top topPos)]
            exact Nat.le_trans (Nat.le_succ (top + 1)) lenOk)
      · have eqTop : letter = top := Nat.le_antisymm letterLeTop geTop
        subst eqTop
        have runLenPos : 1 ≤ runLen :=
          bunchedBimonoidNatLeOfAddLeAddLeftStaircase letter 1 runLen (Nat.le_of_succ_le_succ aboveBottom)
        cases runLen with
        | zero => exact absurd runLenPos (Nat.not_succ_le_zero 0)
        | succ lowerLen =>
            have runDecomp : bunchedBimonoidDescendingPositions letter (lowerLen + 1 + 1)
                = letter :: (letter - 1) :: bunchedBimonoidDescendingPositions (letter - 2) lowerLen := rfl
            rw [runDecomp]
            show (bunchedBimonoidDescendingPositions (letter - 2) lowerLen).foldl bunchedBimonoidApplyAdjacentSwap
                    (bunchedBimonoidApplyAdjacentSwap
                      (bunchedBimonoidApplyAdjacentSwap
                        (bunchedBimonoidApplyAdjacentSwap perm (letter - 1)) letter) (letter - 1))
                = bunchedBimonoidApplyAdjacentSwap
                    ((bunchedBimonoidDescendingPositions (letter - 2) lowerLen).foldl bunchedBimonoidApplyAdjacentSwap
                      (bunchedBimonoidApplyAdjacentSwap
                        (bunchedBimonoidApplyAdjacentSwap perm letter) (letter - 1))) letter
            have braidRaw := bunchedBimonoidApplyAdjacentSwapBraid perm (letter - 1)
              (by
                rw [show (letter - 1) + 2 = letter + 1 from
                  congrArg Nat.succ (bunchedBimonoidPredSuccStaircase letter letterPos)]
                exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (letter + 1)) lenOk)
            rw [bunchedBimonoidPredSuccStaircase letter letterPos] at braidRaw
            rw [braidRaw]
            cases lowerLen with
            | zero => rfl
            | succ lowerLen2 =>
                have letterGe2 : 2 ≤ letter :=
                  Nat.le_trans (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le lowerLen2)))
                    (Nat.le_of_succ_le_succ runLenLe)
                have lowerBelow : (letter - 2) + 2 ≤ letter :=
                  Nat.le_of_eq (bunchedBimonoidSubTwoAddTwoStaircase letter letterGe2)
                exact bunchedBimonoidSwapCommutesRunBelow letter (letter - 2) (lowerLen2 + 1)
                  (bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidApplyAdjacentSwap perm letter) (letter - 1))
                  lowerBelow

/-! ## C1.realizesSwap — THE KEYSTONE: each comb-insert step = one adjacent swap -/

/-- ★★ **Each `bunchedBimonoidCombInsertData` step realizes exactly ONE adjacent swap of the permutation.**  The
permutation of the new config word is the old config's permutation with `s_letter` applied on the right.  Four
branches: COMMUTE (disjoint commute past the run), EXTEND (a pure snoc), CANCEL (snoc + involution), CARRY
(`carry_perm`).  The DATA-level soundness heart of `CoxeterWordUnique`. -/
theorem bunchedBimonoidCombInsertDataRealizesSwap (generatorCount : Nat) (genPos : 1 ≤ generatorCount)
    (statePrefix : List Nat) (stateRun : Nat) (stateRunLe : stateRun ≤ generatorCount)
    (letter : Nat) (letterLt : letter < generatorCount) :
    bunchedBimonoidPermOfWord
        ((bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).1
          ++ bunchedBimonoidDescendingPositions (generatorCount - 1)
              (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).2)
        (generatorCount + 1)
      = bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidPermOfWord
          (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) (generatorCount + 1))
          letter := by
  rcases Nat.lt_trichotomy (letter + stateRun) generatorCount with hLt | hEq | hGt
  · rcases Nat.lt_or_ge (letter + stateRun + 1) generatorCount with hCommute | hExtendGe
    · -- COMMUTE
      have condCommute : letter + stateRun + 2 ≤ generatorCount := hCommute
      have dataEq : bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter
          = (statePrefix ++ [letter], stateRun) := by
        show (if letter + stateRun + 2 ≤ generatorCount then (statePrefix ++ [letter], stateRun)
              else if letter + stateRun + 1 = generatorCount then (statePrefix, stateRun + 1)
              else if letter + stateRun = generatorCount then (statePrefix, stateRun - 1)
              else (statePrefix ++ [letter - 1], stateRun)) = (statePrefix ++ [letter], stateRun)
        rw [if_pos condCommute]
      rw [dataEq]
      show bunchedBimonoidPermOfWord
          ((statePrefix ++ [letter]) ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
          (generatorCount + 1)
        = bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidPermOfWord
            (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) (generatorCount + 1))
            letter
      rw [bunchedBimonoidPermOfWordAppendSplit (generatorCount + 1) (statePrefix ++ [letter])
            (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun),
        bunchedBimonoidPermOfWordSnoc (generatorCount + 1) statePrefix letter,
        bunchedBimonoidPermOfWordAppendSplit (generatorCount + 1) statePrefix
          (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)]
      exact bunchedBimonoidSwapCommutesRunAbove letter (generatorCount - 1) stateRun
        (bunchedBimonoidPermOfWord statePrefix (generatorCount + 1))
        (bunchedBimonoidNatLePredStaircase (letter + stateRun + 1) generatorCount condCommute)
    · -- EXTEND
      have hExtend : letter + stateRun + 1 = generatorCount := Nat.le_antisymm hLt hExtendGe
      have notCommute : ¬ (letter + stateRun + 2 ≤ generatorCount) := by
        rw [← hExtend]; exact Nat.not_succ_le_self _
      have dataEq : bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter
          = (statePrefix, stateRun + 1) := by
        show (if letter + stateRun + 2 ≤ generatorCount then (statePrefix ++ [letter], stateRun)
              else if letter + stateRun + 1 = generatorCount then (statePrefix, stateRun + 1)
              else if letter + stateRun = generatorCount then (statePrefix, stateRun - 1)
              else (statePrefix ++ [letter - 1], stateRun)) = (statePrefix, stateRun + 1)
        rw [if_neg notCommute, if_pos hExtend]
      rw [dataEq]
      show bunchedBimonoidPermOfWord
          (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) (stateRun + 1)) (generatorCount + 1)
        = bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidPermOfWord
            (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) (generatorCount + 1))
            letter
      have letterEq : letter = (generatorCount - 1) - stateRun :=
        bunchedBimonoidNatEqSubOfAddEqStaircase letter stateRun (generatorCount - 1)
          (bunchedBimonoidNatEqSubOfAddEqStaircase (letter + stateRun) 1 generatorCount hExtend)
      have runSnoc : bunchedBimonoidDescendingPositions (generatorCount - 1) (stateRun + 1)
          = bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun ++ [letter] := by
        rw [letterEq]; exact (bunchedBimonoidDescendingPositionsSnocStaircase (generatorCount - 1) stateRun).symm
      rw [runSnoc, ← bunchedBimonoidAppendAssocStaircase statePrefix
          (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) [letter],
        bunchedBimonoidPermOfWordSnoc (generatorCount + 1)
          (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) letter]
  · -- CANCEL
    have notCommute : ¬ (letter + stateRun + 2 ≤ generatorCount) := fun h => by
      rw [hEq] at h
      exact Nat.not_succ_le_self generatorCount (Nat.le_trans (Nat.le_succ (generatorCount + 1)) h)
    have notExtend : ¬ (letter + stateRun + 1 = generatorCount) := fun h => by
      rw [hEq] at h
      exact absurd (Nat.le_of_eq h) (Nat.not_succ_le_self generatorCount)
    have dataEq : bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter
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
        show bunchedBimonoidPermOfWord
            (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) c) (generatorCount + 1)
          = bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidPermOfWord
              (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) (c + 1)) (generatorCount + 1))
              letter
        have letterEq : letter = (generatorCount - 1) - c :=
          bunchedBimonoidNatEqSubOfAddEqStaircase letter c (generatorCount - 1)
            (bunchedBimonoidNatEqSubOfAddEqStaircase (letter + c) 1 generatorCount hEq)
        have runSnoc : bunchedBimonoidDescendingPositions (generatorCount - 1) (c + 1)
            = bunchedBimonoidDescendingPositions (generatorCount - 1) c ++ [letter] := by
          rw [letterEq]; exact (bunchedBimonoidDescendingPositionsSnocStaircase (generatorCount - 1) c).symm
        rw [runSnoc, ← bunchedBimonoidAppendAssocStaircase statePrefix
            (bunchedBimonoidDescendingPositions (generatorCount - 1) c) [letter],
          bunchedBimonoidPermOfWordSnoc (generatorCount + 1)
            (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) c) letter,
          bunchedBimonoidApplyAdjacentSwapInvolutive (bunchedBimonoidPermOfWord
            (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) c) (generatorCount + 1)) letter]
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
    have dataEq : bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter
        = (statePrefix ++ [letter - 1], stateRun) := by
      show (if letter + stateRun + 2 ≤ generatorCount then (statePrefix ++ [letter], stateRun)
            else if letter + stateRun + 1 = generatorCount then (statePrefix, stateRun + 1)
            else if letter + stateRun = generatorCount then (statePrefix, stateRun - 1)
            else (statePrefix ++ [letter - 1], stateRun)) = (statePrefix ++ [letter - 1], stateRun)
      rw [if_neg notCommute, if_neg notExtend, if_neg notCancel]
    rw [dataEq]
    show bunchedBimonoidPermOfWord
        ((statePrefix ++ [letter - 1]) ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
        (generatorCount + 1)
      = bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidPermOfWord
          (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) (generatorCount + 1))
          letter
    have letterPos : 1 ≤ letter := by
      have h1 : generatorCount + 1 ≤ letter + generatorCount :=
        Nat.le_trans hGt (Nat.add_le_add_left stateRunLe letter)
      exact bunchedBimonoidNatLeOfAddLeAddLeftStaircase generatorCount 1 letter
        (by rw [Nat.add_comm letter generatorCount] at h1; exact h1)
    rw [bunchedBimonoidPermOfWordAppendSplit (generatorCount + 1) (statePrefix ++ [letter - 1])
          (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun),
      bunchedBimonoidPermOfWordSnoc (generatorCount + 1) statePrefix (letter - 1),
      bunchedBimonoidPermOfWordAppendSplit (generatorCount + 1) statePrefix
        (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)]
    exact bunchedBimonoidCarryPerm letter letterPos (generatorCount - 1) stateRun
      (bunchedBimonoidPermOfWord statePrefix (generatorCount + 1))
      (bunchedBimonoidNatLePredStaircase letter generatorCount letterLt)
      (by rw [bunchedBimonoidPredSuccStaircase generatorCount genPos]; exact stateRunLe)
      (by rw [show (generatorCount - 1) + 2 = generatorCount + 1 from
          congrArg Nat.succ (bunchedBimonoidPredSuccStaircase generatorCount genPos)]; exact hGt)
      (by rw [bunchedBimonoidPermOfWordLength statePrefix (generatorCount + 1)]
          exact Nat.le_of_eq (congrArg Nat.succ (bunchedBimonoidPredSuccStaircase generatorCount genPos)))

/-! ## C1.invariants — the comb step preserves the state invariants (mentionsOnlyBelow + run bound) -/

private theorem bunchedBimonoidBoolAndLeftStaircase :
    (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → leftFlag = true
  | true, _, _ => rfl
  | false, _, conj => Bool.noConfusion conj

private theorem bunchedBimonoidBoolAndRightStaircase :
    (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → rightFlag = true
  | true, _, conj => conj
  | false, _, conj => Bool.noConfusion conj

private theorem bunchedBimonoidNatBleOfLeStaircase : (lower upper : Nat) → lower ≤ upper → Nat.ble lower upper = true
  | 0, _, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | lower + 1, upper + 1, h => bunchedBimonoidNatBleOfLeStaircase lower upper (Nat.le_of_succ_le_succ h)

private theorem bunchedBimonoidNatBltOfLtStaircase (lower upper : Nat) (h : lower < upper) :
    Nat.blt lower upper = true :=
  bunchedBimonoidNatBleOfLeStaircase (lower + 1) upper h

private theorem bunchedBimonoidNatLtOfBltStaircase (lower upper : Nat) (h : Nat.blt lower upper = true) :
    lower < upper := by
  have hble : Nat.ble (lower + 1) upper = true := h
  clear h
  induction lower generalizing upper with
  | zero => cases upper with
    | zero => exact Bool.noConfusion hble
    | succ u => exact Nat.succ_le_succ (Nat.zero_le u)
  | succ l ih => cases upper with
    | zero => exact Bool.noConfusion hble
    | succ u => exact Nat.succ_le_succ (ih u hble)

/-- `bunchedBimonoidMentionsOnlyBelow bound (prefixList ++ [position]) = true` from the prefix certificate and
`Nat.blt position bound = true`.  Structural on the prefix. -/
theorem bunchedBimonoidMentionsOnlyBelowSnoc :
    (bound : Nat) → (prefixList : List Nat) → (position : Nat) →
    bunchedBimonoidMentionsOnlyBelow bound prefixList = true → Nat.blt position bound = true →
    bunchedBimonoidMentionsOnlyBelow bound (prefixList ++ [position]) = true
  | bound, [], position, _, hpos => by
      show (Nat.blt position bound && bunchedBimonoidMentionsOnlyBelow bound []) = true
      rw [hpos]; rfl
  | bound, head :: rest, position, hall, hpos => by
      have hhead : Nat.blt head bound = true := bunchedBimonoidBoolAndLeftStaircase _ _ hall
      have hrest : bunchedBimonoidMentionsOnlyBelow bound rest = true :=
        bunchedBimonoidBoolAndRightStaircase _ _ hall
      show (Nat.blt head bound && bunchedBimonoidMentionsOnlyBelow bound (rest ++ [position])) = true
      rw [hhead, bunchedBimonoidMentionsOnlyBelowSnoc bound rest position hrest hpos]; rfl

/-- ★ **The comb step preserves the state invariants** — from `mentionsOnlyBelow (gc-1) prefix`, `run ≤ gc`, and
`letter < gc`, the new prefix is `mentionsOnlyBelow (gc-1)` and the new run is `≤ gc`.  Four-branch case analysis on
the same trichotomy the realizesSwap uses. -/
theorem bunchedBimonoidCombInsertPreservesInvariants (generatorCount : Nat) (_genPos : 1 ≤ generatorCount)
    (statePrefix : List Nat) (stateRun : Nat)
    (uBelow : bunchedBimonoidMentionsOnlyBelow (generatorCount - 1) statePrefix = true)
    (runLe : stateRun ≤ generatorCount) (letter : Nat) (letterLt : letter < generatorCount) :
    bunchedBimonoidMentionsOnlyBelow (generatorCount - 1)
        (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).1 = true
      ∧ (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).2 ≤ generatorCount := by
  rcases Nat.lt_trichotomy (letter + stateRun) generatorCount with hLt | hEq | hGt
  · rcases Nat.lt_or_ge (letter + stateRun + 1) generatorCount with hCommute | hExtendGe
    · -- COMMUTE: prefix ++ [letter], run unchanged
      have condCommute : letter + stateRun + 2 ≤ generatorCount := hCommute
      have dataEq : bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter
          = (statePrefix ++ [letter], stateRun) := by
        show (if letter + stateRun + 2 ≤ generatorCount then (statePrefix ++ [letter], stateRun)
              else if letter + stateRun + 1 = generatorCount then (statePrefix, stateRun + 1)
              else if letter + stateRun = generatorCount then (statePrefix, stateRun - 1)
              else (statePrefix ++ [letter - 1], stateRun)) = (statePrefix ++ [letter], stateRun)
        rw [if_pos condCommute]
      rw [dataEq]
      have letterPlusTwoLe : letter + 2 ≤ generatorCount :=
        Nat.le_trans (Nat.add_le_add_right (Nat.le_add_right letter stateRun) 2) condCommute
      have letterLtPred : letter < generatorCount - 1 :=
        bunchedBimonoidNatLePredStaircase (letter + 1) generatorCount letterPlusTwoLe
      exact ⟨bunchedBimonoidMentionsOnlyBelowSnoc (generatorCount - 1) statePrefix letter uBelow
        (bunchedBimonoidNatBltOfLtStaircase letter (generatorCount - 1) letterLtPred), runLe⟩
    · -- EXTEND: prefix unchanged, run + 1
      have hExtend : letter + stateRun + 1 = generatorCount := Nat.le_antisymm hLt hExtendGe
      have notCommute : ¬ (letter + stateRun + 2 ≤ generatorCount) := by
        rw [← hExtend]; exact Nat.not_succ_le_self _
      have dataEq : bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter
          = (statePrefix, stateRun + 1) := by
        show (if letter + stateRun + 2 ≤ generatorCount then (statePrefix ++ [letter], stateRun)
              else if letter + stateRun + 1 = generatorCount then (statePrefix, stateRun + 1)
              else if letter + stateRun = generatorCount then (statePrefix, stateRun - 1)
              else (statePrefix ++ [letter - 1], stateRun)) = (statePrefix, stateRun + 1)
        rw [if_neg notCommute, if_pos hExtend]
      rw [dataEq]
      have runSuccLe : stateRun + 1 ≤ generatorCount := by
        rw [← hExtend, Nat.add_assoc letter stateRun 1]
        exact Nat.le_add_left (stateRun + 1) letter
      exact ⟨uBelow, runSuccLe⟩
  · -- CANCEL: prefix unchanged, run - 1
    have notCommute : ¬ (letter + stateRun + 2 ≤ generatorCount) := fun h => by
      rw [hEq] at h
      exact Nat.not_succ_le_self generatorCount (Nat.le_trans (Nat.le_succ (generatorCount + 1)) h)
    have notExtend : ¬ (letter + stateRun + 1 = generatorCount) := fun h => by
      rw [hEq] at h
      exact absurd (Nat.le_of_eq h) (Nat.not_succ_le_self generatorCount)
    have dataEq : bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter
        = (statePrefix, stateRun - 1) := by
      show (if letter + stateRun + 2 ≤ generatorCount then (statePrefix ++ [letter], stateRun)
            else if letter + stateRun + 1 = generatorCount then (statePrefix, stateRun + 1)
            else if letter + stateRun = generatorCount then (statePrefix, stateRun - 1)
            else (statePrefix ++ [letter - 1], stateRun)) = (statePrefix, stateRun - 1)
      rw [if_neg notCommute, if_neg notExtend, if_pos hEq]
    rw [dataEq]
    exact ⟨uBelow, Nat.le_trans (Nat.sub_le stateRun 1) runLe⟩
  · -- CARRY: prefix ++ [letter - 1], run unchanged
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
    have dataEq : bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter
        = (statePrefix ++ [letter - 1], stateRun) := by
      show (if letter + stateRun + 2 ≤ generatorCount then (statePrefix ++ [letter], stateRun)
            else if letter + stateRun + 1 = generatorCount then (statePrefix, stateRun + 1)
            else if letter + stateRun = generatorCount then (statePrefix, stateRun - 1)
            else (statePrefix ++ [letter - 1], stateRun)) = (statePrefix ++ [letter - 1], stateRun)
      rw [if_neg notCommute, if_neg notExtend, if_neg notCancel]
    rw [dataEq]
    have letterPos : 1 ≤ letter := by
      have h1 : generatorCount + 1 ≤ letter + generatorCount :=
        Nat.le_trans hGt (Nat.add_le_add_left runLe letter)
      exact bunchedBimonoidNatLeOfAddLeAddLeftStaircase generatorCount 1 letter
        (by rw [Nat.add_comm letter generatorCount] at h1; exact h1)
    have letterLePred : letter ≤ generatorCount - 1 :=
      bunchedBimonoidNatLePredStaircase letter generatorCount letterLt
    have letterM1LtPred : letter - 1 < generatorCount - 1 := by
      have step : (letter - 1) + 1 ≤ generatorCount - 1 := by
        rw [bunchedBimonoidPredSuccStaircase letter letterPos]; exact letterLePred
      exact step
    exact ⟨bunchedBimonoidMentionsOnlyBelowSnoc (generatorCount - 1) statePrefix (letter - 1) uBelow
      (bunchedBimonoidNatBltOfLtStaircase (letter - 1) (generatorCount - 1) letterM1LtPred), runLe⟩

/-! ## C1.preservesPerm — the DATA comb fold / normal form preserves the through-strand permutation -/

/-- ★★ **The DATA comb fold preserves the permutation, from any state.**  Structural on `rest`, threading the state
invariants via `bunchedBimonoidCombInsertPreservesInvariants` and the per-step swap via
`bunchedBimonoidCombInsertDataRealizesSwap`. -/
theorem bunchedBimonoidCombFoldPreservesPerm (generatorCount : Nat) (genPos : 1 ≤ generatorCount) :
    (rest : List Nat) → (statePrefix : List Nat) → (stateRun : Nat) →
    bunchedBimonoidMentionsOnlyBelow (generatorCount - 1) statePrefix = true → stateRun ≤ generatorCount →
    bunchedBimonoidMentionsOnlyBelow generatorCount rest = true →
    bunchedBimonoidPermOfWord
        ((rest.foldl (bunchedBimonoidCombInsertData generatorCount) (statePrefix, stateRun)).1
          ++ bunchedBimonoidDescendingPositions (generatorCount - 1)
              (rest.foldl (bunchedBimonoidCombInsertData generatorCount) (statePrefix, stateRun)).2)
        (generatorCount + 1)
      = bunchedBimonoidPermOfWord
          ((statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) ++ rest)
          (generatorCount + 1)
  | [], statePrefix, stateRun, _, _, _ => by
      show bunchedBimonoidPermOfWord
          (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) (generatorCount + 1)
        = bunchedBimonoidPermOfWord
            ((statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) ++ [])
            (generatorCount + 1)
      rw [bunchedBimonoidAppendNilStaircase
        (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)]
  | letter :: restTail, statePrefix, stateRun, uBelow, runLe, hRange => by
      have letterLt : letter < generatorCount :=
        bunchedBimonoidNatLtOfBltStaircase letter generatorCount (bunchedBimonoidBoolAndLeftStaircase _ _ hRange)
      obtain ⟨belowMid, runLeMid⟩ :=
        bunchedBimonoidCombInsertPreservesInvariants generatorCount genPos statePrefix stateRun uBelow runLe
          letter letterLt
      have ihEq := bunchedBimonoidCombFoldPreservesPerm generatorCount genPos restTail
        (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).1
        (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).2 belowMid runLeMid
        (bunchedBimonoidBoolAndRightStaircase _ _ hRange)
      have stepEq := bunchedBimonoidCombInsertDataRealizesSwap generatorCount genPos statePrefix stateRun runLe
        letter letterLt
      show bunchedBimonoidPermOfWord
          ((restTail.foldl (bunchedBimonoidCombInsertData generatorCount)
              (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter)).1
            ++ bunchedBimonoidDescendingPositions (generatorCount - 1)
                (restTail.foldl (bunchedBimonoidCombInsertData generatorCount)
                  (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter)).2)
          (generatorCount + 1)
        = bunchedBimonoidPermOfWord
            ((statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
              ++ (letter :: restTail)) (generatorCount + 1)
      rw [ihEq, bunchedBimonoidPermOfWordAppendSplit (generatorCount + 1)
            ((bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).1
              ++ bunchedBimonoidDescendingPositions (generatorCount - 1)
                  (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).2) restTail,
        stepEq]
      exact (bunchedBimonoidPermOfWordAppendSplit (generatorCount + 1)
        (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
        (letter :: restTail)).symm

/-- ★★ **The comb normal form preserves the through-strand permutation** —
`permOfWord (combNormalizeForm gc W) (gc+1) = permOfWord W (gc+1)` for in-range `W`.  The DATA-level soundness leg the
canonicity argument reads the strand pin off (goal-chain item 2's foundation). -/
theorem bunchedBimonoidCombNormalizeFormPreservesPerm (generatorCount : Nat) (genPos : 1 ≤ generatorCount)
    (input : List Nat) (inRange : bunchedBimonoidMentionsOnlyBelow generatorCount input = true) :
    bunchedBimonoidPermOfWord (bunchedBimonoidCombNormalizeForm generatorCount input) (generatorCount + 1)
      = bunchedBimonoidPermOfWord input (generatorCount + 1) := by
  have folded := bunchedBimonoidCombFoldPreservesPerm generatorCount genPos input [] 0 rfl
    (Nat.zero_le generatorCount) inRange
  have startEq : ([] ++ bunchedBimonoidDescendingPositions (generatorCount - 1) 0) ++ input = input := rfl
  rw [startEq] at folded
  exact folded

/-! ## The C1 honesty marker + the r15 residual (the CONV spelling bridge, honestly named) -/

/-- ★★★ **ESTABLISHED (C1) — the pure permutation-preservation leg is SHIPPED and zero-axiom.**  `= true` records
the KEYSTONE `bunchedBimonoidCombInsertDataRealizesSwap` (each comb-insert step applies exactly ONE adjacent swap of
the through-strand permutation, four branches COMMUTE / EXTEND / CANCEL / CARRY, the CARRY branch resting on the
permutation-carry identity `bunchedBimonoidCarryPerm` = braid + disjoint commutation over the descending run), the
state-invariant preservation (`bunchedBimonoidCombInsertPreservesInvariants`), and their fold
`bunchedBimonoidCombFoldPreservesPerm` -> `bunchedBimonoidCombNormalizeFormPreservesPerm` (one comb level preserves
the permutation).  With the pure `applyAdjacentSwap` identities (involution, disjoint commutation, braid) and the two
run-commutation lemmas, all ports of the Brauer `combInsertData_realizesSwap` / `combFold_preservesPerm` over the
byte-identical Omega engine.  This is the DATA-level soundness the recursive-comb canonicity
(`permOfWord w1 = permOfWord w2 -> recComb (W-1) w1 = recComb (W-1) w2`) reads the strand pin off — goal-chain item 2
for `CoxeterWordUnique`.  PURE `List Nat`, ZERO CONV.  Zero-axiom (per-decl `#assert_no_axioms` + independent
`#print axioms` in the twin). -/
def fxBunchedBimonoid_combInsertionRealizesSwapAndPreservesPermShipped : Bool := true

/-- ★ **THE CONV-FOLD SPELLING BRIDGE STAYS WALLED (r15) — the star's `CoxeterWordUnique` middle, no flip.**
`= false` records the exact remaining node: the single-letter CONV insertion `combInsertStepConv` (firing the r9
`bunchedBimonoid{YangBaxter,Involution,DistantSwap}AtPosition` moves through a `permWord`/`sigmaAt` chain) is NOT
built here.  The obstacle is the vcomp-vs-list-append spelling bridge: the r9 moves fire on the FIXED base legs
(`bunchedBimonoidSigmaInvolutionLeftLeg = vcomp addSigmaGen addSigmaGen`, `bunchedBimonoidYangBaxterLeftLeg`), which
are NOT the `sigmaAt`-chain (`vcomp (sigmaAt w k) (sigmaAt w k)`) definitionally — only up to
`whiskerLeftFunctorial` / `whiskerRightFunctorial` distributing the whisker over the inner vcomp — and the fold's
`permWord (A ++ B) w` is a right-folded vcomp TREE, not `vcomp (permWord A w) (permWord B w)` definitionally (needs
the `permWord_append_conv` reshape via `vcompUnitLeft` / `vcompAssoc`).  This round ships the PURE permutation side
(the DATA soundness) only; the CONV fold + the final `coxeterWordUnique` assembly are the r15 headline.  The star
markers (`fxBunchedBimonoid_correctedWellTypedStarStillOpen*`,
`fxBunchedBimonoid_coxeterWordUniqueGatedOnGenericBraid`,
`fxBunchedBimonoid_collisionGeneralStepStillGatedOnBracketMatch`,
`fxBunchedBimonoid_coxeterWordUniqueBubbleSortStillUnbuilt`) keep their names and `= false` values byte-intact
(cross-file, not edited); NO fabricated star flip. -/
def fxBunchedBimonoid_combInsertStepConvGatedOnSpellingBridge : Bool := false

/-- ★ **THE CORRECTED WELL-TYPED STAR STAYS OPEN — no flip (byte-intact, cross-file).**  `= false` records that
`bunchedBimonoidStarStatementAdditiveWellTyped` is STILL NOT proven in r14: no literal hypothesis-free inhabitant is
produced (the star's `vcomp` case needs the walled wide-collision recursion; its equal-matrices middle needs the
walled `CoxeterWordUnique`, whose pure-permutation leg is shipped this round but whose CONV fold is r15).  The
star-owning marker `fxBunchedBimonoid_correctedWellTypedStarStillOpen` (StarAssembly, r7) and every upstream star
marker keep their name and `= false` value byte-intact (cross-file, not edited) — NO fabricated flip. -/
def fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterCanonicalWord : Bool := false

/-- ★★★ **ESTABLISHED — the WP-PROP r14 canonical-word ledger (the honest scoreboard).**  `= true` records the
complete r14 round: C0 the canonical-word DATA engine (the Coxeter–Moser comb + the recursive staircase, truth-probed
+ pinned, `fxBunchedBimonoid_canonicalWordStaircaseEngineShipped`); C1 the pure permutation-preservation leg (the
KEYSTONE `combInsertData_realizesSwap` folded to `combNormalizeForm_preservesPerm`,
`fxBunchedBimonoid_combInsertionRealizesSwapAndPreservesPermShipped`).  Together these ship the pure `List Nat` layer
of `CoxeterWordUnique` — the recursive-comb staircase and its DATA-level soundness.  The CONV-fold spelling bridge
(the single-letter `combInsertStepConv` + the outer fold + the final assembly) is precisely named and DEFERRED to r15
(`fxBunchedBimonoid_combInsertStepConvGatedOnSpellingBridge = false`); the star does NOT flip
(`fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterCanonicalWord = false`), and every upstream star / residual
marker keeps its name and value byte-intact (cross-file, not edited).  Zero-axiom (per-decl `#assert_no_axioms` +
independent `#print axioms` in the twin); STRUCTURAL only.  NO fabricated star flip. -/
def fxBunchedBimonoid_canonicalWordStaircaseRoundFourteenLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega
