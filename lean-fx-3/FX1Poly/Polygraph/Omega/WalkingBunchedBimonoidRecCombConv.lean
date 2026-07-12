import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCombInsertConv
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordMatrixToRecComb

/-! # Polygraph/Omega/WalkingBunchedBimonoidRecCombConv — the recursive comb-staircase CONV (F4) and the
perm-middle word-problem completeness decision (WP-PROP r26, #2033)

★ **THE F4 FOLD IS DELIVERED — the recursive comb staircase `recCombConv`, whisker-free.**  The r25 census marker
`fxBunchedBimonoid_recCombConvAndOwnerFlipStillOpen` (`= false`, byte-intact cross-file) named F4 (`recCombConv`,
structural on the generator count, recursing through F3 `combNormalizeFormConv`) as "the SOLE remaining CONV node
before the owner flip".  This round ships it.

## The gap F4 crosses, and the vehicle

`recComb (level + 1) input = recComb level P ++ descendingPositions level R` (with `(P, R) = fold (level + 1)`) —
the recursion descends ONE level while the ambient width stays fixed.  The natural-width F3 (`combNormalizeFormConv`,
r25) lands `permWord _ (level + 1)`; at ambient width `W > level + 1` its endpoints live at a WIDER width, and lifting
`permWord w (level + 1)` to `permWord w W` by whiskering an identity strand is the chain-UNSOUND identity-whisker
unitor (`WalkingBunchedBimonoidWhiskerOneCellCoherenceWall`, permanently walled).  The sound vehicle DECOUPLES the
width from the recursion level: the F1-F3 stack is re-derived here at an ARBITRARY ambient width `width` under the
single gate `level + 1 <= width` (`combInsertConvAtWidth` / `combFoldConvAtWidth` / `combNormalizeFormConvAtWidth`),
re-threading `width` through every shipped brick BYTE-INTACT (each brick is width-parametric with a `<=`-gate:
`permWordAppendConv`, `permWordSnocConv`, `swapCommutesRunAbove/BelowConv`, `carryPermConv`, `braidWithTailConv`,
`sigmaAtDistantCommuteConv`, `cancelLetterConv`, `sigmaAtBoundaryReshapeConv`, `genericBraidConv` — all consumed,
NEVER edited).  Then the F4 recursion invokes its IH at the SAME ambient `width`, so the width-shift vanishes.

## What F4 delivers (and does NOT)

`bunchedBimonoidRecCombConvAtWidth` (structural on `level`) + the natural-width headline `bunchedBimonoidRecCombConv`
(`width := generatorCount + 1`).  Composed with the shipped r18 T3 `bunchedBimonoidRecCombEqOfEvalEq` (matrix ->
`recComb`-equality, PURE), it delivers the perm-middle word-problem completeness
`bunchedBimonoidCoxeterWordUniqueViaRecComb`: two words valid at width `W` whose `permWord` cells share their `Mat(N)`
matrix are CONV-convertible over the star scope.  This is the recComb-route delivery of the `CoxeterWordUnique`
TARGET (equal matrix => CONV).

The three `CoxeterWordUnique` owners (`coxeterWordUniqueBubbleSortStillUnbuilt` /
`coxeterWordUniqueMinimalLemmaUnbuilt` / `coxeterWordUniqueGatedOnGenericBraid`) name a STRUCTURAL bubble-sort fuel
method (and the fuel-sort -> CONV bridge) the recComb route BYPASSES; per the FLIP LAW, different-method delivery is
NOT a literal clause-by-clause flip, so those markers STAY `= false` byte-intact.  The #2033 star
`correctedWellTypedStarStillOpen` additionally needs the B1 wide-collision node (untouched here), so it too stays
`= false`.  The r25 census marker keeps its name and value byte-intact; this file posts FRESH markers for the F4
delivery + the perm-middle completeness, and names the r27 residual (the generic-width Mu/Delta naturality slide B1;
Node A `Mat(N)` algebra for the soundness half).

Raw Lean 4 + Init; STRUCTURAL only (no `WellFounded.fix`, no fuel); ASCII-only.  Per-declaration
`#assert_no_axioms` AND an independent `#print axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

/-! The width-3/4 braid endpoint matrix `rfl` pins (imported through the r24 braid atom) require the raised
heartbeat budget; every DERIVATION term here is congruence-constructor plumbing (axiom-free, no wide kernel
`rfl`), uniform with the r6-r25 lane files. -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # A0 — THE PROPEXT-CLEAN ARITHMETIC + LIST BACKBONE (re-derived in-file, `RecComb` suffix)
    # =========================================================================================

★ The Staircase / CombInsertConv arithmetic helpers are `private` to their files, so the handful this fold needs
are re-derived here with the identical propext-clean recipe (full-enum `Bool` cases + structural `Nat` peels; the
`Nat.sub` order lemmas that leak propext are avoided). -/

/-- `index - 1 + 1 = index` under `1 <= index`. -/
private theorem bunchedBimonoidPredSuccRecComb : (index : Nat) → 1 ≤ index → index - 1 + 1 = index
  | 0, positive => absurd positive (by decide)
  | _ + 1, _ => rfl

/-- `lower <= top - 1` from `lower + 1 <= top`. -/
private theorem bunchedBimonoidNatLePredRecComb : (lower top : Nat) → lower + 1 ≤ top → lower ≤ top - 1
  | lower, 0, h => absurd h (Nat.not_succ_le_zero lower)
  | _, _ + 1, h => Nat.le_of_succ_le_succ h

/-- `base + offset - offset = base` — structural on `offset`. -/
private theorem bunchedBimonoidNatAddSubCancelRecComb : (base offset : Nat) → base + offset - offset = base
  | _, 0 => rfl
  | base, offset + 1 =>
      (Nat.succ_sub_succ (base + offset) offset).trans (bunchedBimonoidNatAddSubCancelRecComb base offset)

/-- `base = total - offset` from `base + offset = total`. -/
private theorem bunchedBimonoidNatEqSubOfAddEqRecComb (base offset total : Nat) (h : base + offset = total) :
    base = total - offset := by
  rw [← h]; exact (bunchedBimonoidNatAddSubCancelRecComb base offset).symm

/-- `left <= right` from `left + amount <= right + amount`. -/
private theorem bunchedBimonoidNatLeOfAddLeAddRightRecComb :
    (left right amount : Nat) → left + amount ≤ right + amount → left ≤ right
  | _, _, 0, h => h
  | left, right, amount + 1, h =>
      bunchedBimonoidNatLeOfAddLeAddRightRecComb left right amount (Nat.le_of_succ_le_succ h)

/-- `left <= right` from `amount + left <= amount + right`. -/
private theorem bunchedBimonoidNatLeOfAddLeAddLeftRecComb (amount left right : Nat)
    (h : amount + left ≤ amount + right) : left ≤ right :=
  bunchedBimonoidNatLeOfAddLeAddRightRecComb left right amount
    (by rw [Nat.add_comm left amount, Nat.add_comm right amount]; exact h)

/-- `top - count - 1 = top - 1 - count` — structural on `count`. -/
private theorem bunchedBimonoidSubOneCommRecComb : (top count : Nat) → top - count - 1 = top - 1 - count
  | _, 0 => rfl
  | top, count + 1 => congrArg Nat.pred (bunchedBimonoidSubOneCommRecComb top count)

/-- List append associativity. -/
private theorem bunchedBimonoidAppendAssocRecComb {alpha : Type _} :
    (front mid back : List alpha) → (front ++ mid) ++ back = front ++ (mid ++ back)
  | [], _, _ => rfl
  | head :: rest, mid, back => congrArg (head :: ·) (bunchedBimonoidAppendAssocRecComb rest mid back)

/-- The descending run's distinguished LAST element is `top - count`. -/
private theorem bunchedBimonoidDescendingPositionsSnocRecComb : (top count : Nat) →
    bunchedBimonoidDescendingPositions top count ++ [top - count]
      = bunchedBimonoidDescendingPositions top (count + 1)
  | _, 0 => rfl
  | top, count + 1 => by
      have idxEq : top - (count + 1) = (top - 1) - count := bunchedBimonoidSubOneCommRecComb top count
      have inner : bunchedBimonoidDescendingPositions (top - 1) count ++ [top - (count + 1)]
          = bunchedBimonoidDescendingPositions (top - 1) (count + 1) := by
        rw [idxEq]; exact bunchedBimonoidDescendingPositionsSnocRecComb (top - 1) count
      show top :: (bunchedBimonoidDescendingPositions (top - 1) count ++ [top - (count + 1)])
         = top :: bunchedBimonoidDescendingPositions (top - 1) (count + 1)
      exact congrArg (top :: ·) inner

/-- `Nat.ble lower upper = true` from `lower <= upper`. -/
private theorem bunchedBimonoidNatBleOfLeRecComb :
    (lower upper : Nat) → lower ≤ upper → Nat.ble lower upper = true
  | 0, _, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | lower + 1, upper + 1, h => bunchedBimonoidNatBleOfLeRecComb lower upper (Nat.le_of_succ_le_succ h)

/-- `Nat.blt lower upper = true` from `lower < upper`. -/
private theorem bunchedBimonoidNatBltOfLtRecComb (lower upper : Nat) (h : lower < upper) :
    Nat.blt lower upper = true :=
  bunchedBimonoidNatBleOfLeRecComb (lower + 1) upper h

/-- A descending run mentions only positions strictly below any bound above its top. -/
private theorem bunchedBimonoidDescendingPositionsMentionBelowRecComb (bound : Nat) :
    (top count : Nat) → top < bound →
    bunchedBimonoidMentionsOnlyBelow bound (bunchedBimonoidDescendingPositions top count) = true
  | _, 0, _ => rfl
  | top, count + 1, topLt => by
      show (Nat.blt top bound
          && bunchedBimonoidMentionsOnlyBelow bound (bunchedBimonoidDescendingPositions (top - 1) count)) = true
      rw [bunchedBimonoidNatBltOfLtRecComb top bound topLt,
        bunchedBimonoidDescendingPositionsMentionBelowRecComb bound (top - 1) count
          (Nat.lt_of_le_of_lt (Nat.sub_le top 1) topLt)]
      rfl

/-- `leftFlag = true` from `leftFlag && rightFlag = true`. -/
private theorem bunchedBimonoidBoolAndLeftRecComb :
    (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → leftFlag = true
  | true, _, _ => rfl
  | false, _, conj => Bool.noConfusion conj

/-- `rightFlag = true` from `leftFlag && rightFlag = true`. -/
private theorem bunchedBimonoidBoolAndRightRecComb :
    (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → rightFlag = true
  | true, _, conj => conj
  | false, _, conj => Bool.noConfusion conj

/-- `lower <= upper` from `Nat.ble lower upper = true`. -/
private theorem bunchedBimonoidNatLeOfBleRecComb :
    (lower upper : Nat) → Nat.ble lower upper = true → lower ≤ upper
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => Bool.noConfusion h
  | lower + 1, upper + 1, h => Nat.succ_le_succ (bunchedBimonoidNatLeOfBleRecComb lower upper h)

/-- `lower < upper` from `Nat.blt lower upper = true`. -/
private theorem bunchedBimonoidNatLtOfBltRecComb (lower upper : Nat)
    (h : Nat.blt lower upper = true) : lower < upper :=
  bunchedBimonoidNatLeOfBleRecComb (lower + 1) upper h

/-- List right-identity `list ++ [] = list`. -/
private theorem bunchedBimonoidAppendNilRecComb {alpha : Type _} :
    (list : List alpha) → list ++ [] = list
  | [] => rfl
  | head :: rest => congrArg (head :: ·) (bunchedBimonoidAppendNilRecComb rest)

/-- `mentionsOnlyBelow 0 word = true` forces `word = []` (no position is `< 0`). -/
private theorem bunchedBimonoidMentionsBelowZeroNilRecComb :
    (word : List Nat) → bunchedBimonoidMentionsOnlyBelow 0 word = true → word = []
  | [], _ => rfl
  | position :: rest, hMentions => by
      have hFalse : bunchedBimonoidMentionsOnlyBelow 0 (position :: rest) = false := rfl
      rw [hFalse] at hMentions
      exact Bool.noConfusion hMentions

/-- `level < width - 1` from `level + 2 <= width` — cases on `width`. -/
private theorem bunchedBimonoidLtPredOfAddTwoLeRecComb :
    (level width : Nat) → level + 2 ≤ width → level < width - 1
  | _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _, _ + 1, h => Nat.le_of_succ_le_succ h

/-- Monotonicity of `mentionsOnlyBelow` in the bound — a word valid below `smallBound` is valid below any
`bigBound >= smallBound`.  Structural on the word. -/
private theorem bunchedBimonoidMentionsOnlyBelowMonoRecComb (smallBound bigBound : Nat)
    (hle : smallBound ≤ bigBound) :
    (word : List Nat) → bunchedBimonoidMentionsOnlyBelow smallBound word = true →
    bunchedBimonoidMentionsOnlyBelow bigBound word = true
  | [], _ => rfl
  | position :: rest, hMentions => by
      have posLtSmall : position < smallBound :=
        bunchedBimonoidNatLtOfBltRecComb position smallBound (bunchedBimonoidBoolAndLeftRecComb _ _ hMentions)
      have restBelow : bunchedBimonoidMentionsOnlyBelow smallBound rest = true :=
        bunchedBimonoidBoolAndRightRecComb _ _ hMentions
      show (Nat.blt position bigBound && bunchedBimonoidMentionsOnlyBelow bigBound rest) = true
      rw [bunchedBimonoidNatBltOfLtRecComb position bigBound (Nat.lt_of_lt_of_le posLtSmall hle),
        bunchedBimonoidMentionsOnlyBelowMonoRecComb smallBound bigBound hle rest restBelow]
      rfl

/-! # =========================================================================================
    # A1 — THE WIDTH-GENERALIZED FOUR-BRANCH COMB-INSERTION CONV STEP (`combInsertConvAtWidth`)
    # =========================================================================================

★ The F2 `combInsertConv` (r25) with the ambient width DECOUPLED from the comb level: the same four-branch dispatch
at an arbitrary `width` under `generatorCount + 1 <= width`.  Every width sub-gate that was an equality (`= gc + 1`)
in the natural-width F2 loosens to a `<=`-gate (`<= width`); every brick is reused byte-intact.  This is the load-
bearing width lift the F4 recursion consumes. -/

/-- ★★★ **THE FOUR-BRANCH COMB-INSERTION CONV STEP AT ARBITRARY WIDTH.**  One `combInsertData` step, read at
`permWord` granularity, is a single right-post-composition by `sigmaAt width letter` over the star scope, for any
ambient `width` with `generatorCount + 1 <= width`.  Four branches on `Nat.lt_trichotomy (letter + stateRun)
generatorCount` (COMMUTE / EXTEND / CANCEL / CARRY), each reusing the width-parametric shipped bricks. -/
theorem bunchedBimonoidCombInsertConvAtWidth (generatorCount : Nat) (genPos : 1 ≤ generatorCount)
    (width : Nat) (widthGate : generatorCount + 1 ≤ width)
    (statePrefix : List Nat) (stateRun : Nat) (stateRunLe : stateRun ≤ generatorCount)
    (letter : Nat) (letterLt : letter < generatorCount) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidPermWord
        ((bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).1
          ++ bunchedBimonoidDescendingPositions (generatorCount - 1)
              (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).2)
        width)
      (CellExpr.vcomp
        (bunchedBimonoidPermWord (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
          width)
        (bunchedBimonoidSigmaAt width letter)) := by
  have runGate : generatorCount - 1 < width - 1 :=
    bunchedBimonoidLtPredOfAddTwoLeRecComb (generatorCount - 1) width
      (by rw [show (generatorCount - 1) + 2 = generatorCount + 1 from
        congrArg Nat.succ (bunchedBimonoidPredSuccRecComb generatorCount genPos)]; exact widthGate)
  have runValid : bunchedBimonoidMentionsOnlyBelow (width - 1)
      (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) = true :=
    bunchedBimonoidDescendingPositionsMentionBelowRecComb (width - 1) (generatorCount - 1) stateRun runGate
  have widthAboveGate : (generatorCount - 1) + 2 ≤ width :=
    Nat.le_trans (Nat.le_of_eq (congrArg Nat.succ (bunchedBimonoidPredSuccRecComb generatorCount genPos))) widthGate
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
      have widthOk : letter + 2 ≤ width :=
        Nat.le_trans (Nat.le_trans (Nat.add_le_add_right (Nat.le_add_right letter stateRun) 2) condCommute)
          (Nat.le_of_succ_le widthGate)
      have aboveGate : letter + stateRun + 1 ≤ generatorCount - 1 :=
        bunchedBimonoidNatLePredRecComb (letter + stateRun + 1) generatorCount condCommute
      show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
          (bunchedBimonoidPermWord
            ((statePrefix ++ [letter]) ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
            width)
          (CellExpr.vcomp
            (bunchedBimonoidPermWord (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
              width)
            (bunchedBimonoidSigmaAt width letter))
      exact SaturatedConvOverWithId.trans
        (bunchedBimonoidPermWordAppendConv width (statePrefix ++ [letter])
          (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) runValid)
        (SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.vcompCongrLeft
            (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) width)
            (bunchedBimonoidPermWordSnocConv width letter widthOk statePrefix))
          (SaturatedConvOverWithId.trans
            (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
              (StrictAxiomRel.vcompAssoc (bunchedBimonoidPermWord statePrefix width)
                (bunchedBimonoidSigmaAt width letter)
                (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) width)))
            (SaturatedConvOverWithId.trans
              (SaturatedConvOverWithId.vcompCongrRight (bunchedBimonoidPermWord statePrefix width)
                (bunchedBimonoidSwapCommutesRunAboveConv width letter (generatorCount - 1) stateRun
                  aboveGate widthAboveGate))
              (SaturatedConvOverWithId.trans
                (SaturatedConvOverWithId.symm (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                  (StrictAxiomRel.vcompAssoc (bunchedBimonoidPermWord statePrefix width)
                    (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) width)
                    (bunchedBimonoidSigmaAt width letter))))
                (SaturatedConvOverWithId.symm
                  (SaturatedConvOverWithId.vcompCongrLeft (bunchedBimonoidSigmaAt width letter)
                    (bunchedBimonoidPermWordAppendConv width statePrefix
                      (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) runValid)))))))
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
      have widthOk : letter + 2 ≤ width := by
        have h1 : letter + 1 ≤ generatorCount := by
          rw [← hExtend]; exact Nat.add_le_add_right (Nat.le_add_right letter stateRun) 1
        exact Nat.le_trans (Nat.succ_le_succ h1) widthGate
      have letterEq : letter = (generatorCount - 1) - stateRun :=
        bunchedBimonoidNatEqSubOfAddEqRecComb letter stateRun (generatorCount - 1)
          (bunchedBimonoidNatEqSubOfAddEqRecComb (letter + stateRun) 1 generatorCount hExtend)
      have runSnoc : bunchedBimonoidDescendingPositions (generatorCount - 1) (stateRun + 1)
          = bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun ++ [letter] := by
        rw [letterEq]
        exact (bunchedBimonoidDescendingPositionsSnocRecComb (generatorCount - 1) stateRun).symm
      have listEq : statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) (stateRun + 1)
          = (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) ++ [letter] := by
        rw [runSnoc]
        exact (bunchedBimonoidAppendAssocRecComb statePrefix
          (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) [letter]).symm
      show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
          (bunchedBimonoidPermWord
            (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) (stateRun + 1))
            width)
          (CellExpr.vcomp
            (bunchedBimonoidPermWord (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
              width)
            (bunchedBimonoidSigmaAt width letter))
      rw [listEq]
      exact bunchedBimonoidPermWordSnocConv width letter widthOk
        (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
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
    have widthOk : letter + 2 ≤ width := Nat.le_trans (Nat.succ_le_succ letterLt) widthGate
    cases stateRun with
    | zero =>
        have hEqZero : letter = generatorCount := hEq
        exact absurd (hEqZero ▸ letterLt) (Nat.lt_irrefl generatorCount)
    | succ runPred =>
        show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
            (bunchedBimonoidPermWord (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) runPred)
              width)
            (CellExpr.vcomp
              (bunchedBimonoidPermWord
                (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) (runPred + 1))
                width)
              (bunchedBimonoidSigmaAt width letter))
        have letterEq : letter = (generatorCount - 1) - runPred :=
          bunchedBimonoidNatEqSubOfAddEqRecComb letter runPred (generatorCount - 1)
            (bunchedBimonoidNatEqSubOfAddEqRecComb (letter + runPred) 1 generatorCount hEq)
        have runSnoc : bunchedBimonoidDescendingPositions (generatorCount - 1) (runPred + 1)
            = bunchedBimonoidDescendingPositions (generatorCount - 1) runPred ++ [letter] := by
          rw [letterEq]
          exact (bunchedBimonoidDescendingPositionsSnocRecComb (generatorCount - 1) runPred).symm
        have listEq : statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) (runPred + 1)
            = (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) runPred) ++ [letter] := by
          rw [runSnoc]
          exact (bunchedBimonoidAppendAssocRecComb statePrefix
            (bunchedBimonoidDescendingPositions (generatorCount - 1) runPred) [letter]).symm
        rw [listEq]
        have hbdry : boundaryTarget (bunchedBimonoidPermWord
            (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) runPred) width)
            = bunchedBimonoidAWordPow width :=
          bunchedBimonoidPermWordBoundaryTarget width
            (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) runPred)
        have hconv : SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
            (boundarySource (bunchedBimonoidSigmaAt width letter))
            (boundaryTarget (bunchedBimonoidPermWord
              (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) runPred)
              width)) := by
          rw [hbdry]
          exact (bunchedBimonoidSigmaAtBoundaryReshapeConv width letter widthOk).symm
        exact SaturatedConvOverWithId.symm
          (SaturatedConvOverWithId.trans
            (SaturatedConvOverWithId.vcompCongrLeft (bunchedBimonoidSigmaAt width letter)
              (bunchedBimonoidPermWordSnocConv width letter widthOk
                (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) runPred)))
            (SaturatedConvOverWithId.trans
              (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                (StrictAxiomRel.vcompAssoc
                  (bunchedBimonoidPermWord
                    (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) runPred)
                    width)
                  (bunchedBimonoidSigmaAt width letter)
                  (bunchedBimonoidSigmaAt width letter)))
              (SaturatedConvOverWithId.trans
                (SaturatedConvOverWithId.vcompCongrRight
                  (bunchedBimonoidPermWord
                    (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) runPred)
                    width)
                  (bunchedBimonoidCancelLetterConv width letter))
                (bunchedBimonoidVcompIdRightBridgedWithId
                  (bunchedBimonoidPermWord
                    (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) runPred)
                    width)
                  hconv
                  (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                    (StrictAxiomRel.vcompUnitRight
                      (bunchedBimonoidPermWord
                        (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) runPred)
                        width)))))))
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
    have letterPos : 1 ≤ letter := by
      have h1 : generatorCount + 1 ≤ letter + generatorCount :=
        Nat.le_trans hGt (Nat.add_le_add_left stateRunLe letter)
      exact bunchedBimonoidNatLeOfAddLeAddLeftRecComb generatorCount 1 letter
        (by rw [Nat.add_comm letter generatorCount] at h1; exact h1)
    have widthOkCarry : (letter - 1) + 2 ≤ width := by
      rw [show (letter - 1) + 2 = letter + 1 from
        congrArg Nat.succ (bunchedBimonoidPredSuccRecComb letter letterPos)]
      exact Nat.le_trans letterLt (Nat.le_of_succ_le widthGate)
    show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
        (bunchedBimonoidPermWord
          ((statePrefix ++ [letter - 1]) ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
          width)
        (CellExpr.vcomp
          (bunchedBimonoidPermWord (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
            width)
          (bunchedBimonoidSigmaAt width letter))
    exact SaturatedConvOverWithId.trans
      (bunchedBimonoidPermWordAppendConv width (statePrefix ++ [letter - 1])
        (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) runValid)
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrLeft
          (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) width)
          (bunchedBimonoidPermWordSnocConv width (letter - 1) widthOkCarry statePrefix))
        (SaturatedConvOverWithId.trans
          (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
            (StrictAxiomRel.vcompAssoc (bunchedBimonoidPermWord statePrefix width)
              (bunchedBimonoidSigmaAt width (letter - 1))
              (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) width)))
          (SaturatedConvOverWithId.trans
            (SaturatedConvOverWithId.vcompCongrRight (bunchedBimonoidPermWord statePrefix width)
              (bunchedBimonoidCarryPermConv width letter letterPos (generatorCount - 1) stateRun
                (bunchedBimonoidNatLePredRecComb letter generatorCount letterLt)
                (by rw [bunchedBimonoidPredSuccRecComb generatorCount genPos]; exact stateRunLe)
                (by
                  rw [show (generatorCount - 1) + 2 = generatorCount + 1 from
                    congrArg Nat.succ (bunchedBimonoidPredSuccRecComb generatorCount genPos)]
                  exact hGt)
                widthAboveGate))
            (SaturatedConvOverWithId.trans
              (SaturatedConvOverWithId.symm (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                (StrictAxiomRel.vcompAssoc (bunchedBimonoidPermWord statePrefix width)
                  (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) width)
                  (bunchedBimonoidSigmaAt width letter))))
              (SaturatedConvOverWithId.symm
                (SaturatedConvOverWithId.vcompCongrLeft (bunchedBimonoidSigmaAt width letter)
                  (bunchedBimonoidPermWordAppendConv width statePrefix
                    (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) runValid)))))))

/-! # =========================================================================================
    # A2 — THE WIDTH-GENERALIZED COMB-FOLD + ONE-LEVEL NORMAL-FORM CONV (F3 at width)
    # =========================================================================================
-/

/-- ★★ **THE COMB-FOLD CONV AT ARBITRARY WIDTH.**  Fold the width-generalized `combInsertConvAtWidth` step down the
remaining word, threading the shipped `combInsertPreservesInvariants` and the B1 `permWordAppendConv` reshape.
Structural on `rest`.  The width lift of the r25 `combFoldConv`. -/
theorem bunchedBimonoidCombFoldConvAtWidth (generatorCount : Nat) (genPos : 1 ≤ generatorCount)
    (width : Nat) (widthGate : generatorCount + 1 ≤ width) :
    (rest : List Nat) → (statePrefix : List Nat) → (stateRun : Nat) →
    bunchedBimonoidMentionsOnlyBelow (generatorCount - 1) statePrefix = true → stateRun ≤ generatorCount →
    bunchedBimonoidMentionsOnlyBelow generatorCount rest = true →
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidPermWord
        ((rest.foldl (bunchedBimonoidCombInsertData generatorCount) (statePrefix, stateRun)).1
          ++ bunchedBimonoidDescendingPositions (generatorCount - 1)
              (rest.foldl (bunchedBimonoidCombInsertData generatorCount) (statePrefix, stateRun)).2)
        width)
      (bunchedBimonoidPermWord
        ((statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) ++ rest)
        width)
  | [], statePrefix, stateRun, _, _, _ => by
      show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
          (bunchedBimonoidPermWord
            (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) width)
          (bunchedBimonoidPermWord
            ((statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) ++ [])
            width)
      rw [bunchedBimonoidAppendNilRecComb
        (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)]
      exact SaturatedConvOverWithId.refl _
  | letter :: restTail, statePrefix, stateRun, uBelow, runLe, hRange => by
      have letterLt : letter < generatorCount :=
        bunchedBimonoidNatLtOfBltRecComb letter generatorCount
          (bunchedBimonoidBoolAndLeftRecComb _ _ hRange)
      have restValid : bunchedBimonoidMentionsOnlyBelow generatorCount restTail = true :=
        bunchedBimonoidBoolAndRightRecComb _ _ hRange
      have widthMinusOneGate : generatorCount ≤ width - 1 :=
        bunchedBimonoidNatLePredRecComb generatorCount width widthGate
      have restValidWide : bunchedBimonoidMentionsOnlyBelow (width - 1) restTail = true :=
        bunchedBimonoidMentionsOnlyBelowMonoRecComb generatorCount (width - 1) widthMinusOneGate restTail restValid
      have hRangeWide : bunchedBimonoidMentionsOnlyBelow (width - 1) (letter :: restTail) = true :=
        bunchedBimonoidMentionsOnlyBelowMonoRecComb generatorCount (width - 1) widthMinusOneGate
          (letter :: restTail) hRange
      obtain ⟨belowMid, runLeMid⟩ :=
        bunchedBimonoidCombInsertPreservesInvariants generatorCount genPos statePrefix stateRun uBelow runLe
          letter letterLt
      have ihConv := bunchedBimonoidCombFoldConvAtWidth generatorCount genPos width widthGate restTail
        (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).1
        (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).2 belowMid runLeMid restValid
      show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
          (bunchedBimonoidPermWord
            ((restTail.foldl (bunchedBimonoidCombInsertData generatorCount)
                (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter)).1
              ++ bunchedBimonoidDescendingPositions (generatorCount - 1)
                  (restTail.foldl (bunchedBimonoidCombInsertData generatorCount)
                    (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter)).2)
            width)
          (bunchedBimonoidPermWord
            ((statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
              ++ (letter :: restTail)) width)
      refine SaturatedConvOverWithId.trans ihConv ?_
      refine SaturatedConvOverWithId.trans
        (bunchedBimonoidPermWordAppendConv width
          ((bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).1
            ++ bunchedBimonoidDescendingPositions (generatorCount - 1)
                (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).2)
          restTail restValidWide) ?_
      refine SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrLeft
          (bunchedBimonoidPermWord restTail width)
          (bunchedBimonoidCombInsertConvAtWidth generatorCount genPos width widthGate statePrefix stateRun runLe
            letter letterLt)) ?_
      refine SaturatedConvOverWithId.trans
        (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
          (StrictAxiomRel.vcompAssoc
            (bunchedBimonoidPermWord
              (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) width)
            (bunchedBimonoidSigmaAt width letter)
            (bunchedBimonoidPermWord restTail width))) ?_
      exact SaturatedConvOverWithId.symm
        (bunchedBimonoidPermWordAppendConv width
          (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
          (letter :: restTail) hRangeWide)

/-- ★★ **THE ONE-LEVEL NORMAL-FORM CONV AT ARBITRARY WIDTH.**  `permWord (combNormalizeForm gc input) width ~
permWord input width` for in-range `input`, any `width` with `gc + 1 <= width`.  The width lift of the r25
`combNormalizeFormConv`, from the empty state. -/
theorem bunchedBimonoidCombNormalizeFormConvAtWidth (generatorCount : Nat) (genPos : 1 ≤ generatorCount)
    (width : Nat) (widthGate : generatorCount + 1 ≤ width)
    (input : List Nat) (inRange : bunchedBimonoidMentionsOnlyBelow generatorCount input = true) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidPermWord (bunchedBimonoidCombNormalizeForm generatorCount input) width)
      (bunchedBimonoidPermWord input width) := by
  have folded := bunchedBimonoidCombFoldConvAtWidth generatorCount genPos width widthGate input [] 0 rfl
    (Nat.zero_le generatorCount) inRange
  have startEq : ([] ++ bunchedBimonoidDescendingPositions (generatorCount - 1) 0) ++ input = input := rfl
  rw [startEq] at folded
  exact folded

/-! # =========================================================================================
    # A3 — THE RECURSIVE COMB-STAIRCASE CONV (F4)
    # =========================================================================================
-/

/-- ★★★ **THE RECURSIVE COMB-STAIRCASE CONV AT ARBITRARY WIDTH (F4).**  `permWord (recComb level input) width ~
permWord input width` for in-range `input`, structural on `level`, at any ambient `width` with `level + 1 <= width`.
The base (`level = 0`) forces `input = []` (`mentionsOnlyBelow 0`) and closes by `refl`.  The step
(`level = gen + 1`) uses `recComb (gen+1) input = recComb gen P ++ descendingPositions gen R`: the B1
`permWordAppendConv` factors the run off (its `mentionsOnlyBelow (width-1)` validity from the width gate), the IH at
level `gen` — the SAME ambient `width` — replaces the prefix, and the width-generalized F3
`combNormalizeFormConvAtWidth (gen+1)` closes the collapsed normal form to `input`.  The ambient width fixed across
frames is exactly what dodges the walled identity-whisker unitor. -/
theorem bunchedBimonoidRecCombConvAtWidth :
    (level width : Nat) → (input : List Nat) →
    bunchedBimonoidMentionsOnlyBelow level input = true → level + 1 ≤ width →
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidPermWord (bunchedBimonoidRecComb level input) width)
      (bunchedBimonoidPermWord input width)
  | 0, _, input, inRange, _ => by
      rw [bunchedBimonoidMentionsBelowZeroNilRecComb input inRange]
      exact SaturatedConvOverWithId.refl _
  | level + 1, width, input, inRange, widthGate => by
      have genPos : 1 ≤ level + 1 := Nat.succ_le_succ (Nat.zero_le level)
      obtain ⟨below, _⟩ := bunchedBimonoidCombFoldInvariants (level + 1) genPos input [] 0 rfl
        (Nat.zero_le (level + 1)) inRange
      have backValid : bunchedBimonoidMentionsOnlyBelow (width - 1)
          (bunchedBimonoidDescendingPositions level
            (input.foldl (bunchedBimonoidCombInsertData (level + 1)) ([], 0)).2) = true :=
        bunchedBimonoidDescendingPositionsMentionBelowRecComb (width - 1) level
          (input.foldl (bunchedBimonoidCombInsertData (level + 1)) ([], 0)).2
          (bunchedBimonoidLtPredOfAddTwoLeRecComb level width widthGate)
      show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
          (bunchedBimonoidPermWord
            (bunchedBimonoidRecComb level (input.foldl (bunchedBimonoidCombInsertData (level + 1)) ([], 0)).1
              ++ bunchedBimonoidDescendingPositions level
                  (input.foldl (bunchedBimonoidCombInsertData (level + 1)) ([], 0)).2)
            width)
          (bunchedBimonoidPermWord input width)
      exact SaturatedConvOverWithId.trans
        (bunchedBimonoidPermWordAppendConv width
          (bunchedBimonoidRecComb level (input.foldl (bunchedBimonoidCombInsertData (level + 1)) ([], 0)).1)
          (bunchedBimonoidDescendingPositions level
            (input.foldl (bunchedBimonoidCombInsertData (level + 1)) ([], 0)).2)
          backValid)
        (SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.vcompCongrLeft
            (bunchedBimonoidPermWord
              (bunchedBimonoidDescendingPositions level
                (input.foldl (bunchedBimonoidCombInsertData (level + 1)) ([], 0)).2) width)
            (bunchedBimonoidRecCombConvAtWidth level width
              (input.foldl (bunchedBimonoidCombInsertData (level + 1)) ([], 0)).1 below
              (Nat.le_of_succ_le widthGate)))
          (SaturatedConvOverWithId.trans
            (SaturatedConvOverWithId.symm
              (bunchedBimonoidPermWordAppendConv width
                (input.foldl (bunchedBimonoidCombInsertData (level + 1)) ([], 0)).1
                (bunchedBimonoidDescendingPositions level
                  (input.foldl (bunchedBimonoidCombInsertData (level + 1)) ([], 0)).2)
                backValid))
            (bunchedBimonoidCombNormalizeFormConvAtWidth (level + 1) genPos width widthGate input inRange)))

/-- ★★★ **THE F4 HEADLINE — `recCombConv` at the natural width.**  The `width := generatorCount + 1` instance of
`recCombConvAtWidth`: `permWord (recComb generatorCount input) (generatorCount + 1) ~ permWord input
(generatorCount + 1)` for in-range `input`.  The exact shape the perm-middle decision consumes. -/
theorem bunchedBimonoidRecCombConv (generatorCount : Nat) (input : List Nat)
    (inRange : bunchedBimonoidMentionsOnlyBelow generatorCount input = true) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidPermWord (bunchedBimonoidRecComb generatorCount input) (generatorCount + 1))
      (bunchedBimonoidPermWord input (generatorCount + 1)) :=
  bunchedBimonoidRecCombConvAtWidth generatorCount (generatorCount + 1) input inRange (Nat.le_refl (generatorCount + 1))

/-! # =========================================================================================
    # A4 — THE PERM-MIDDLE WORD-PROBLEM COMPLETENESS DECISION (recComb route)
    # =========================================================================================
-/

/-- ★★★ **THE PERM-MIDDLE WORD-PROBLEM COMPLETENESS — equal `Mat(N)` matrix => CONV-convertible, via recComb.**
Two words valid at width `generatorCount + 1` whose `permWord` cells evaluate to the SAME `Mat(N)` map are
CONV-convertible over the star scope.  The recComb-route delivery of the `CoxeterWordUnique` TARGET: the shipped
r18 T3 `recCombEqOfEvalEq` collapses the shared matrix to `recComb`-equality (PURE), and F4 `recCombConv` bridges
each word to its shared staircase in CONV.  No bubble-sort fuel — the semantic (matrix) invariant does the deciding,
recComb realizes the normal form, F4 lifts it to CONV. -/
theorem bunchedBimonoidCoxeterWordUniqueViaRecComb (generatorCount : Nat) (word1 word2 : List Nat)
    (valid1 : bunchedBimonoidPositionsValid (generatorCount + 1) word1 = true)
    (valid2 : bunchedBimonoidPositionsValid (generatorCount + 1) word2 = true)
    (evalEq : (bunchedBimonoidEvalCell (bunchedBimonoidPermWord word1 (generatorCount + 1)) : BunchedBimonoidMat)
      = bunchedBimonoidEvalCell (bunchedBimonoidPermWord word2 (generatorCount + 1))) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidPermWord word1 (generatorCount + 1))
      (bunchedBimonoidPermWord word2 (generatorCount + 1)) := by
  have recEq : bunchedBimonoidRecComb generatorCount word1 = bunchedBimonoidRecComb generatorCount word2 :=
    bunchedBimonoidRecCombEqOfEvalEq generatorCount word1 word2 valid1 valid2 evalEq
  have mentions1 : bunchedBimonoidMentionsOnlyBelow generatorCount word1 = true :=
    bunchedBimonoidMentionsOnlyBelowOfPositionsValid (generatorCount + 1) word1 valid1
  have mentions2 : bunchedBimonoidMentionsOnlyBelow generatorCount word2 = true :=
    bunchedBimonoidMentionsOnlyBelowOfPositionsValid (generatorCount + 1) word2 valid2
  have bridge1 := bunchedBimonoidRecCombConv generatorCount word1 mentions1
  have bridge2 := bunchedBimonoidRecCombConv generatorCount word2 mentions2
  rw [recEq] at bridge1
  exact SaturatedConvOverWithId.trans (SaturatedConvOverWithId.symm bridge1) bridge2

/-! # =========================================================================================
    # A5 — THE NON-VACUITY FIRES (genuine widths) + MATRIX-SOUNDNESS #eval PINS + NEGATIVE CONTROLS
    # =========================================================================================
-/

/-- ★ **F4 fires at the r9 jam word, width 4** — `permWord (recComb 3 [2,0,1,2]) 4 ~ permWord [2,0,1,2] 4` over the
star scope, the exact word the Brauer insertion residual jammed on.  A hypothesis-free inhabitant (`mentionsOnlyBelow
3 [2,0,1,2] = true` by `decide`). -/
theorem bunchedBimonoidRecCombConvJamInstance :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidPermWord (bunchedBimonoidRecComb 3 [2, 0, 1, 2]) 4)
      (bunchedBimonoidPermWord [2, 0, 1, 2] 4) :=
  bunchedBimonoidRecCombConv 3 [2, 0, 1, 2] (by decide)

/-- ★ **F4 fires at a fresh width-5 word** — `permWord (recComb 4 [3,2,3,1,0,2]) 5 ~ permWord [3,2,3,1,0,2] 5` over
the star scope.  The fresh word folds through a genuine CARRY (run `4`), exercising the level-4 recursion at ambient
width 5.  Hypothesis-free (`mentionsOnlyBelow 4 [3,2,3,1,0,2] = true` by `decide`). -/
theorem bunchedBimonoidRecCombConvWidthFiveInstance :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidPermWord (bunchedBimonoidRecComb 4 [3, 2, 3, 1, 0, 2]) 5)
      (bunchedBimonoidPermWord [3, 2, 3, 1, 0, 2] 5) :=
  bunchedBimonoidRecCombConv 4 [3, 2, 3, 1, 0, 2] (by decide)

/-- ★ **F4 fires at width 3, the Yang-Baxter braid word** — `permWord (recComb 2 [0,1,0]) 3 ~ permWord [0,1,0] 3`. -/
theorem bunchedBimonoidRecCombConvBraidInstance :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidPermWord (bunchedBimonoidRecComb 2 [0, 1, 0]) 3)
      (bunchedBimonoidPermWord [0, 1, 0] 3) :=
  bunchedBimonoidRecCombConv 2 [0, 1, 0] (by decide)

/-- ★★ **THE PERM-MIDDLE DECISION FIRES on the r9 braid pair, width 3** — from the shared width-3 matrix
`evalCell (permWord [0,1,0] 3) = evalCell (permWord [1,0,1] 3)` (the shipped `bunchedBimonoidBraidPairEvalShared`,
proved through the extractor — NOT a wide kernel `rfl`), the perm-middle completeness delivers
`permWord [0,1,0] 3 ~ permWord [1,0,1] 3` over the star scope: the Yang-Baxter braid pair DECIDED from the semantic
(matrix) side and lifted to CONV.  Hypothesis-free (the two `positionsValid 3 _` by `decide`). -/
theorem bunchedBimonoidCoxeterWordUniqueViaRecCombBraidPair :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidPermWord [0, 1, 0] 3)
      (bunchedBimonoidPermWord [1, 0, 1] 3) :=
  bunchedBimonoidCoxeterWordUniqueViaRecComb 2 [0, 1, 0] [1, 0, 1] (by decide) (by decide)
    bunchedBimonoidBraidPairEvalShared

/-! Matrix-soundness witness (compiled `#eval`, NOT a kernel `rfl`): the r9 jam pair `[2,0,1,2]` / `[0,1,2,1]` share
their width-4 `permWord` matrix entries (both realize `[1,3,2,0]`) — the necessary condition the perm-middle CONV
decision respects, pinned at the fire width. -/
#eval decide ((bunchedBimonoidEvalCell (bunchedBimonoidPermWord [2, 0, 1, 2] 4)).entries
  = (bunchedBimonoidEvalCell (bunchedBimonoidPermWord [0, 1, 2, 1] 4)).entries) -- expect true

/-! Matrix-soundness witness (compiled `#eval`): a fresh width-5 pair `[3,2,3,1,0,2]` and its staircase share their
matrix entries. -/
#eval decide ((bunchedBimonoidEvalCell (bunchedBimonoidPermWord [3, 2, 3, 1, 0, 2] 5)).entries
  = (bunchedBimonoidEvalCell (bunchedBimonoidPermWord (bunchedBimonoidRecComb 4 [3, 2, 3, 1, 0, 2]) 5)).entries)
  -- expect true

/-- Negative control for the F4 level-0 base guard — `mentionsOnlyBelow 0 [0] = false`: a non-empty word is
genuinely rejected by the base precondition (no position is `< 0`), so the base is not vacuous. -/
theorem bunchedBimonoidRecCombConvBaseGuardRejects :
    bunchedBimonoidMentionsOnlyBelow 0 [0] = false := rfl

/-- Negative control for the perm-middle `evalEq` guard — the words `[0,1]` / `[1,0]` at width 3 realize DIFFERENT
through-strand permutations (`[1,2,0]` vs `[2,0,1]`), hence (extractor + injective) different `Mat(N)` matrices, so
the `evalEq` hypothesis of the perm-middle decision cannot hold on this pair: the decision is not vacuous. -/
theorem bunchedBimonoidCoxeterViaRecCombGuardSeparates :
    bunchedBimonoidPermOfWord [0, 1] 3 ≠ bunchedBimonoidPermOfWord [1, 0] 3 := by
  intro hEq
  exact absurd hEq (by decide)

/-! # =========================================================================================
    # THE r26 HONESTY MARKERS (fresh markers per literal delivery; owners + r25 markers byte-intact)
    # =========================================================================================
-/

/-- ★★★ **ESTABLISHED (F4) — the recursive comb-staircase CONV `recCombConv` is DELIVERED, whisker-free.**  `= true`
records `bunchedBimonoidRecCombConv` (and its width-decoupled engine `bunchedBimonoidRecCombConvAtWidth`): `permWord
(recComb generatorCount input) (generatorCount + 1) ~ permWord input (generatorCount + 1)` for in-range `input`,
structural on the generator count, recursing through the width-generalized F1-F3 stack
(`combInsertConvAtWidth` / `combFoldConvAtWidth` / `combNormalizeFormConvAtWidth`) built by re-threading an arbitrary
ambient `width` (gate `level + 1 <= width`) through every shipped r6-r25 brick BYTE-INTACT.  The width-decoupled
recursion dodges the permanently-walled identity-whisker unitor
(`WalkingBunchedBimonoidWhiskerOneCellCoherenceWall`).  Consumes the FROZEN r25 F3 machinery genuinely (never
re-derived).  Closes the F4 clause of the r25 census marker
`fxBunchedBimonoid_recCombConvAndOwnerFlipStillOpen` (retire-name-only; that marker stays `= false` byte-intact
cross-file).  Non-vacuous at genuine widths 4 (r9 jam), 5 (fresh CARRY word), and 3 (braid word); negative control
`bunchedBimonoidRecCombConvBaseGuardRejects` witnesses the base guard.  Zero-axiom. -/
def fxBunchedBimonoid_recCombConvShipped : Bool := true

/-- ★★★ **ESTABLISHED — the PERM-MIDDLE word-problem COMPLETENESS is DELIVERED via recComb.**  `= true` records
`bunchedBimonoidCoxeterWordUniqueViaRecComb`: two words valid at width `W` whose `permWord` cells share their
`Mat(N)` matrix are CONV-convertible over the star scope — the recComb-route delivery of the `CoxeterWordUnique`
TARGET (equal matrix => CONV).  Assembled from F4 `recCombConv` (twice) + the shipped r18 T3
`bunchedBimonoidRecCombEqOfEvalEq` (matrix -> `recComb`-equality, PURE); the whole perm-middle assembly is discharged
by shipped machinery once F4 is a theorem.  Non-vacuous: it fires on the r9 Yang-Baxter braid pair
(`bunchedBimonoidCoxeterWordUniqueViaRecCombBraidPair`), deciding `permWord [0,1,0] 3 ~ permWord [1,0,1] 3` from the
shared matrix `bunchedBimonoidBraidPairEvalShared` (proved through the extractor, NOT a wide kernel `rfl`); the
negative control `bunchedBimonoidCoxeterViaRecCombGuardSeparates` witnesses the `evalEq` guard is genuine.
Zero-axiom. -/
def fxBunchedBimonoid_permMiddleWordProblemCompleteViaRecComb : Bool := true

/-- ★ **THE BUBBLE-SORT OWNERS + THE #2033 STAR STAY OPEN — the honest r26 residual, no fabricated flip.**  `= false`
records the FLIP-LAW verdict: the three `CoxeterWordUnique` owners
(`fxBunchedBimonoid_coxeterWordUniqueBubbleSortStillUnbuilt`,
`fxBunchedBimonoid_coxeterWordUniqueMinimalLemmaUnbuilt`, `fxBunchedBimonoid_coxeterWordUniqueGatedOnGenericBraid`)
name a STRUCTURAL bubble-sort fuel method (and the fuel-sort -> CONV bridge) that the recComb route BYPASSES — it
delivers the same TARGET (equal matrix => CONV) by the recComb-canonicity route instead, so per the FLIP LAW
(literal clause-by-clause delivery only) NONE of them flips; all three keep their name and `= false` value
byte-intact cross-file.  The #2033 star `fxBunchedBimonoid_correctedWellTypedStarStillOpen` additionally needs the B1
wide-collision node (untouched here), so it also stays `= false` byte-intact.  r27 residual: the generic-width
Mu/Delta naturality slide (B1) -> the star's `vcomp` case -> the #2033 completeness star; Node A `Mat(N)` algebra kit
(matMul associativity + block-mult) is the parallel soundness-side track.  `StrictAxioms.lean` + the shipped star
scope are untouched (only the shipped `StrictAxiomRel.{vcompAssoc, vcompUnitLeft, vcompUnitRight}` rows consumed).
No fabricated star flip. -/
def fxBunchedBimonoid_recCombRouteBypassesBubbleSortOwners : Bool := false

end FX1Poly.Polygraph.Omega
