import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidGenericBraidConv
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordAppendReshape
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordStaircase

/-! # Polygraph/Omega/WalkingBunchedBimonoidCombInsertConv — the four-branch comb-insertion CONV step
`combInsertConv` (F2), the CONV mirror of the r14 DATA keystone `combInsertData_realizesSwap`, over the SHIPPED
star scope (WP-PROP r25)

★ **THE COMB-INSERTION CONV STEP IS DELIVERED — the CARRY case UNBLOCKED by the r24 braid atom.**  The r23
census marker `fxBunchedBimonoid_combFoldsBraidWalledDownstreamOfCarry` (`= false`, byte-intact cross-file) named
`combInsertConv` (F2), `combNormalizeFormConv` (F3) and `recCombConv` (F4) as "braid-walled at the CARRY case of
`combInsertData`".  That wall fell in r24: the generic-width adjacent-braid CONV atom
`bunchedBimonoidGenericBraidConv` shipped (derived term-mode from the axiomatic width-3 Yang-Baxter hexagon row,
NO wide kernel `rfl`).  With it, the CARRY branch's permutation-carry `carryPermConv` assembles, and all four
branches of `combInsertConv` land.

The r24 audit comment ("combInsertConv also needs the r15 append-reshape part (b), NOT delivered here") is STALE:
part (b) shipped in r16 as `bunchedBimonoidPermWordAppendConv` (B1,
`WalkingBunchedBimonoidCanonicalWordAppendReshape`).  This round consumes B1 (never re-derives it) and the shipped
r24 braid atom (consumed, never re-derived), and ships the ONE genuinely-new run-level atom `carryPermConv` plus
the four-branch `combInsertConv`.

## The pieces (mirroring the r14 pure `combInsertData_realizesSwap`)

  * **`permWordSnocConv`** — the snoc law `permWord (positions ++ [pos]) w ~ vcomp (permWord positions w)
    (sigmaAt w pos)`, structural on `positions` (no validity threading; only `pos + 2 <= w` at the base, absorbed
    by the shipped P1 trailing-id / leading-id units).  The CONV mirror of the pure `permOfWordSnoc`.
  * **`permWordBoundaryTarget`** — `boundaryTarget (permWord positions w) = aWordPow w`, structural (used by the
    CANCEL branch's trailing-identity absorption).
  * **`braidWithTailConv`** — the r24 braid atom `bunchedBimonoidGenericBraidConv` with a common trailing tail,
    right-nested (the four `vcompAssoc` regroupings that thread the LEFT-associated braid into the RIGHT-fold
    `permWord`).  Fires the CARRY base.
  * **`carryPermConv`** — the CONV mirror of the pure `bunchedBimonoidCarryPerm`.  Structural on the run length:
    STEP (`letter < top`) is the `swapCommutesRun*Conv` associativity dance with the shipped P2
    `sigmaAtDistantCommuteConv` on the head pair and the IH on the tail; BASE (`letter = top`) fires
    `braidWithTailConv` (the pivot braid) then the shipped F1 `swapCommutesRunBelowConv` past the lower sub-run
    (or the P1 unit commutation when the sub-run is empty).
  * **`combInsertConv`** — the four-case dispatch on `Nat.lt_trichotomy (letter + stateRun) generatorCount`:
    COMMUTE (B1 + snoc + P3 `swapCommutesRunAboveConv`), EXTEND (a snoc reshape via `descendingPositionsSnoc`),
    CANCEL (snoc + S2 `cancelLetterConv` `s_k s_k ~ id` + the trailing-id absorb), CARRY (B1 + snoc +
    `carryPermConv`).

The math is entirely standard (Björner–Brenti Strong Exchange Condition + the Lehmer-code decreasing-run normal
form; the CARRY is the Matsumoto/Tits braid move).  No Lean/Coq/Isabelle insertion-sort-on-Coxeter-words
correctness proof is known, so this kernel-checked four-branch CONV step is first-of-kind.

## The honest scope (NO star flip)

`combInsertConv` (F2) lands; `combNormalizeFormConv` (F3, the fold) and `recCombConv` (F4, the level recursion)
plus the `CoxeterUniqueness` owner flip remain (named at the foot).  The four star owners (StarAssembly /
RiffleAssembly / CollisionCanonForm / CoxeterUniqueness) stay `= false` byte-intact; `StrictAxioms.lean` + the
shipped `bunchedBimonoidStarCongruenceScope` are untouched (only the shipped `StrictAxiomRel.{vcompAssoc,
vcompUnitLeft, vcompUnitRight}` rows are consumed through `bunchedBimonoidStrictAxiomEmbedsIntoStarScope`).  The
r23 census marker `fxBunchedBimonoid_combFoldsBraidWalledDownstreamOfCarry` and the r24 braid marker stay `= false`
/ `= true` byte-intact; this file posts FRESH markers for the F2 delivery.

Raw Lean 4 + Init; STRUCTURAL only (no `WellFounded.fix`, no fuel); ASCII-only.  Per-declaration
`#assert_no_axioms` AND independent `#print axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

/-! The width-3/4 braid endpoint matrix `rfl` pins (imported through the r24 braid atom) require the raised
heartbeat budget; every DERIVATION term here is congruence-constructor plumbing (axiom-free, no wide kernel
`rfl`), uniform with the r6-r24 lane files. -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # A0 — THE PROPEXT-CLEAN ARITHMETIC + LIST BACKBONE (the Staircase / r22 privates, re-derived in-file)
    # =========================================================================================

★ The Staircase / ConvFold / PermWordDistantCommuteConv arithmetic helpers are `private` to their files, so the
handful this step needs are re-derived here with the identical propext-clean recipe (full-enum `Bool` cases +
structural `Nat.succ_sub_succ` / `Nat.le_of_succ_le_succ` peels; the `Nat.sub` order lemmas that leak propext are
avoided). -/

/-- `index - 1 + 1 = index` under `1 <= index` — full-enum (`0` absurd, successor `rfl`). -/
private theorem bunchedBimonoidPredSuccCombInsert : (index : Nat) → 1 ≤ index → index - 1 + 1 = index
  | 0, positive => absurd positive (by decide)
  | _ + 1, _ => rfl

/-- `lower <= top - 1` from `lower + 1 <= top` — cases on `top` (`0` absurd, successor `le_of_succ_le_succ`). -/
private theorem bunchedBimonoidNatLePredCombInsert : (lower top : Nat) → lower + 1 ≤ top → lower ≤ top - 1
  | lower, 0, h => absurd h (Nat.not_succ_le_zero lower)
  | _, _ + 1, h => Nat.le_of_succ_le_succ h

/-- `value - 2 + 2 = value` under `2 <= value` — full-enum on `value`. -/
private theorem bunchedBimonoidSubTwoAddTwoCombInsert : (value : Nat) → 2 ≤ value → value - 2 + 2 = value
  | 0, twoLe => absurd twoLe (by decide)
  | 1, twoLe => absurd twoLe (by decide)
  | _ + 2, _ => rfl

/-- `base + offset - offset = base` — structural on `offset`. -/
private theorem bunchedBimonoidNatAddSubCancelCombInsert : (base offset : Nat) → base + offset - offset = base
  | _, 0 => rfl
  | base, offset + 1 =>
      (Nat.succ_sub_succ (base + offset) offset).trans (bunchedBimonoidNatAddSubCancelCombInsert base offset)

/-- `base = total - offset` from `base + offset = total`. -/
private theorem bunchedBimonoidNatEqSubOfAddEqCombInsert (base offset total : Nat) (h : base + offset = total) :
    base = total - offset := by
  rw [← h]; exact (bunchedBimonoidNatAddSubCancelCombInsert base offset).symm

/-- `left <= right` from `left + amount <= right + amount` — structural on `amount`. -/
private theorem bunchedBimonoidNatLeOfAddLeAddRightCombInsert :
    (left right amount : Nat) → left + amount ≤ right + amount → left ≤ right
  | _, _, 0, h => h
  | left, right, amount + 1, h =>
      bunchedBimonoidNatLeOfAddLeAddRightCombInsert left right amount (Nat.le_of_succ_le_succ h)

/-- `left <= right` from `amount + left <= amount + right`. -/
private theorem bunchedBimonoidNatLeOfAddLeAddLeftCombInsert (amount left right : Nat)
    (h : amount + left ≤ amount + right) : left ≤ right :=
  bunchedBimonoidNatLeOfAddLeAddRightCombInsert left right amount
    (by rw [Nat.add_comm left amount, Nat.add_comm right amount]; exact h)

/-- `top - count - 1 = top - 1 - count` — structural on `count` via `congrArg Nat.pred`. -/
private theorem bunchedBimonoidSubOneCommCombInsert : (top count : Nat) → top - count - 1 = top - 1 - count
  | _, 0 => rfl
  | top, count + 1 => congrArg Nat.pred (bunchedBimonoidSubOneCommCombInsert top count)

/-- List append associativity `(front ++ mid) ++ back = front ++ (mid ++ back)` — structural on `front`. -/
private theorem bunchedBimonoidAppendAssocCombInsert {alpha : Type _} :
    (front mid back : List alpha) → (front ++ mid) ++ back = front ++ (mid ++ back)
  | [], _, _ => rfl
  | head :: rest, mid, back => congrArg (head :: ·) (bunchedBimonoidAppendAssocCombInsert rest mid back)

/-- The descending run's distinguished LAST element is `top - count`:
`descendingPositions top count ++ [top - count] = descendingPositions top (count + 1)`. -/
private theorem bunchedBimonoidDescendingPositionsSnocCombInsert : (top count : Nat) →
    bunchedBimonoidDescendingPositions top count ++ [top - count]
      = bunchedBimonoidDescendingPositions top (count + 1)
  | _, 0 => rfl
  | top, count + 1 => by
      have idxEq : top - (count + 1) = (top - 1) - count := bunchedBimonoidSubOneCommCombInsert top count
      have inner : bunchedBimonoidDescendingPositions (top - 1) count ++ [top - (count + 1)]
          = bunchedBimonoidDescendingPositions (top - 1) (count + 1) := by
        rw [idxEq]; exact bunchedBimonoidDescendingPositionsSnocCombInsert (top - 1) count
      show top :: (bunchedBimonoidDescendingPositions (top - 1) count ++ [top - (count + 1)])
         = top :: bunchedBimonoidDescendingPositions (top - 1) (count + 1)
      exact congrArg (top :: ·) inner

/-- `Nat.ble lower upper = true` from `lower <= upper` — structural on both. -/
private theorem bunchedBimonoidNatBleOfLeCombInsert :
    (lower upper : Nat) → lower ≤ upper → Nat.ble lower upper = true
  | 0, _, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | lower + 1, upper + 1, h => bunchedBimonoidNatBleOfLeCombInsert lower upper (Nat.le_of_succ_le_succ h)

/-- `Nat.blt lower upper = true` from `lower < upper` (`Nat.blt lower upper` is `Nat.ble (lower + 1) upper`). -/
private theorem bunchedBimonoidNatBltOfLtCombInsert (lower upper : Nat) (h : lower < upper) :
    Nat.blt lower upper = true :=
  bunchedBimonoidNatBleOfLeCombInsert (lower + 1) upper h

/-- A descending run mentions only positions strictly below any bound above its top:
`mentionsOnlyBelow bound (descendingPositions top count) = true` when `top < bound`.  Structural on `count`. -/
private theorem bunchedBimonoidDescendingPositionsMentionBelowCombInsert (bound : Nat) :
    (top count : Nat) → top < bound →
    bunchedBimonoidMentionsOnlyBelow bound (bunchedBimonoidDescendingPositions top count) = true
  | _, 0, _ => rfl
  | top, count + 1, topLt => by
      show (Nat.blt top bound
          && bunchedBimonoidMentionsOnlyBelow bound (bunchedBimonoidDescendingPositions (top - 1) count)) = true
      rw [bunchedBimonoidNatBltOfLtCombInsert top bound topLt,
        bunchedBimonoidDescendingPositionsMentionBelowCombInsert bound (top - 1) count
          (Nat.lt_of_le_of_lt (Nat.sub_le top 1) topLt)]
      rfl

/-! # =========================================================================================
    # A1 — THE snoc CONV + THE permWord TARGET-BOUNDARY (the letter-append plumbing)
    # =========================================================================================
-/

/-- ★★ **THE snoc CONV — `permWord (positions ++ [pos]) w ~ vcomp (permWord positions w) (sigmaAt w pos)`.**
The CONV mirror of the r14 pure `bunchedBimonoidPermOfWordSnoc`.  Structural on `positions`; the base
(`positions = []`, the word `id (aWordPow w)`) is the P3/F1 unit dance — the shipped P1 trailing-id absorber on
the left, `symm` of `vcompIdLeft_bridgedWithId` (fed by S4) on the right — gated on `pos + 2 <= w`.  The cons
case threads the IH under `vcompCongrRight` and `symm vcompAssoc`.  No `mentionsOnlyBelow` validity is threaded
(only the base's width gate). -/
theorem bunchedBimonoidPermWordSnocConv (wordWidth position : Nat) (posValid : position + 2 ≤ wordWidth) :
    (positions : List Nat) →
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidPermWord (positions ++ [position]) wordWidth)
      (CellExpr.vcomp (bunchedBimonoidPermWord positions wordWidth) (bunchedBimonoidSigmaAt wordWidth position))
  | [] =>
      SaturatedConvOverWithId.trans
        (bunchedBimonoidSigmaAtTrailingIdAbsorbConv wordWidth position posValid)
        (SaturatedConvOverWithId.symm
          (vcompIdLeft_bridgedWithId (bunchedBimonoidSigmaAt wordWidth position)
            (bunchedBimonoidSigmaAtBoundaryReshapeConv wordWidth position posValid)
            (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
              (StrictAxiomRel.vcompUnitLeft (bunchedBimonoidSigmaAt wordWidth position)))))
  | headPosition :: restPositions =>
      SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrRight (bunchedBimonoidSigmaAt wordWidth headPosition)
          (bunchedBimonoidPermWordSnocConv wordWidth position posValid restPositions))
        (SaturatedConvOverWithId.symm
          (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
            (StrictAxiomRel.vcompAssoc (bunchedBimonoidSigmaAt wordWidth headPosition)
              (bunchedBimonoidPermWord restPositions wordWidth)
              (bunchedBimonoidSigmaAt wordWidth position))))

/-- ★ **`boundaryTarget (permWord positions w) = aWordPow w`** — every reduced word ends on the flat width-`w`
word.  Structural on `positions` (`[]` reads `boundaryTarget (id (aWordPow w))`; cons peels through
`boundaryTarget (vcomp _ tail) = boundaryTarget tail`).  Used by the CANCEL branch's trailing-id absorb. -/
theorem bunchedBimonoidPermWordBoundaryTarget (wordWidth : Nat) :
    (positions : List Nat) →
    boundaryTarget (bunchedBimonoidPermWord positions wordWidth) = bunchedBimonoidAWordPow wordWidth
  | [] => rfl
  | _ :: restPositions => bunchedBimonoidPermWordBoundaryTarget wordWidth restPositions

/-! # =========================================================================================
    # A2 — THE BRAID-WITH-TAIL CONV (the r24 braid atom regrouped for the RIGHT-fold permWord)
    # =========================================================================================
-/

/-- ★★ **THE BRAID WITH A COMMON TRAILING TAIL (right-nested).**  The r24 generic-width adjacent braid
`bunchedBimonoidGenericBraidConv` is LEFT-associated `(s_i ; s_{i+1}) ; s_i ~ (s_{i+1} ; s_i) ; s_{i+1}`, but
`permWord` is a RIGHT fold.  This lemma regroups (four `StrictAxiomRel.vcompAssoc` firings) so the braid fires on
a right-nested triple with a common tail:

  `s_i ; (s_{i+1} ; (s_i ; tail)) ~ s_{i+1} ; (s_i ; (s_{i+1} ; tail))`   (`i + 2 < w`).

The CARRY base of `carryPermConv` fires exactly this. -/
theorem bunchedBimonoidBraidWithTailConv (wordWidth positionK : Nat) (inRange : positionK + 2 < wordWidth)
    (tail : CellExpr bunchedBimonoidOmegaComputad 2) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth positionK)
        (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth (positionK + 1))
          (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth positionK) tail)))
      (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth (positionK + 1))
        (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth positionK)
          (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth (positionK + 1)) tail))) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.symm (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
      (StrictAxiomRel.vcompAssoc (bunchedBimonoidSigmaAt wordWidth positionK)
        (bunchedBimonoidSigmaAt wordWidth (positionK + 1))
        (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth positionK) tail))))
    (SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.symm (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
        (StrictAxiomRel.vcompAssoc
          (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth positionK)
            (bunchedBimonoidSigmaAt wordWidth (positionK + 1)))
          (bunchedBimonoidSigmaAt wordWidth positionK) tail)))
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrLeft tail
          (bunchedBimonoidGenericBraidConv wordWidth positionK inRange))
        (SaturatedConvOverWithId.trans
          (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
            (StrictAxiomRel.vcompAssoc
              (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth (positionK + 1))
                (bunchedBimonoidSigmaAt wordWidth positionK))
              (bunchedBimonoidSigmaAt wordWidth (positionK + 1)) tail))
          (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
            (StrictAxiomRel.vcompAssoc (bunchedBimonoidSigmaAt wordWidth (positionK + 1))
              (bunchedBimonoidSigmaAt wordWidth positionK)
              (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth (positionK + 1)) tail))))))

/-! # =========================================================================================
    # A3 — THE PERMUTATION-CARRY CONV (`carryPermConv`, the CARRY-branch run-level atom)
    # =========================================================================================
-/

/-- ★★★ **THE PERMUTATION-CARRY CONV (the ONE genuinely-new atom).**  The CONV mirror of the r14 pure
`bunchedBimonoidCarryPerm`: `s_{letter-1}` commutes past a whole descending run `descendingPositions top runLength`
into `run ; s_letter`, over the star scope.  Structural on `runLength` (mirroring the pure `carryPerm`):

  * STEP (`letter < top`): peel the run-top `s_top` — commute `s_{letter-1}` past it by the shipped P2
    `bunchedBimonoidSigmaAtDistantCommuteConv` at gate `(letter-1)+2 <= top`, then recurse on `top - 1`
    (the `swapCommutesRun*Conv` associativity dance).
  * BASE (`letter = top`): the run decomposes `letter :: (letter-1) :: sub-run`; the three leading letters
    `s_{letter-1} ; s_letter ; s_{letter-1}` fire the r24 braid via `bunchedBimonoidBraidWithTailConv`, then
    `s_letter` commutes past the lower sub-run by the shipped F1 `bunchedBimonoidSwapCommutesRunBelowConv` (or,
    when the sub-run is empty, the P1 unit commutation).

Gated on `letter <= top`, `runLength <= top + 1`, `top + 2 <= letter + runLength` and `top + 2 <= wordWidth`
(the CONV width gate replacing the pure `carryPerm`'s `perm.length` gate). -/
theorem bunchedBimonoidCarryPermConv (wordWidth letter : Nat) (letterPos : 1 ≤ letter) :
    (top runLength : Nat) → letter ≤ top → runLength ≤ top + 1 → top + 2 ≤ letter + runLength →
      top + 2 ≤ wordWidth →
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth (letter - 1))
        (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions top runLength) wordWidth))
      (CellExpr.vcomp (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions top runLength) wordWidth)
        (bunchedBimonoidSigmaAt wordWidth letter))
  | top, 0, letterLeTop, _, aboveBottom, _ =>
      absurd (Nat.le_trans (Nat.le_succ (top + 1)) (Nat.le_trans aboveBottom letterLeTop))
        (Nat.not_succ_le_self top)
  | top, runLength + 1, letterLeTop, runLenLe, aboveBottom, widthOk => by
      rcases Nat.lt_or_ge letter top with ltTop | geTop
      · -- STEP: letter < top
        have topPos : 1 ≤ top := Nat.le_trans letterPos (Nat.le_of_lt ltTop)
        have letterM1Distant : (letter - 1) + 2 ≤ top := by
          rw [show (letter - 1) + 2 = letter + 1 from
            congrArg Nat.succ (bunchedBimonoidPredSuccCombInsert letter letterPos)]
          exact ltTop
        show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
            (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth (letter - 1))
              (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth top)
                (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (top - 1) runLength) wordWidth)))
            (CellExpr.vcomp
              (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth top)
                (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (top - 1) runLength) wordWidth))
              (bunchedBimonoidSigmaAt wordWidth letter))
        refine SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.symm (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
            (StrictAxiomRel.vcompAssoc (bunchedBimonoidSigmaAt wordWidth (letter - 1))
              (bunchedBimonoidSigmaAt wordWidth top)
              (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (top - 1) runLength) wordWidth)))) ?_
        refine SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.vcompCongrLeft
            (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (top - 1) runLength) wordWidth)
            (bunchedBimonoidSigmaAtDistantCommuteConv wordWidth (letter - 1) top letterM1Distant widthOk)) ?_
        refine SaturatedConvOverWithId.trans
          (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
            (StrictAxiomRel.vcompAssoc (bunchedBimonoidSigmaAt wordWidth top)
              (bunchedBimonoidSigmaAt wordWidth (letter - 1))
              (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (top - 1) runLength) wordWidth))) ?_
        refine SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.vcompCongrRight (bunchedBimonoidSigmaAt wordWidth top)
            (bunchedBimonoidCarryPermConv wordWidth letter letterPos (top - 1) runLength
              (bunchedBimonoidNatLePredCombInsert letter top ltTop)
              (by rw [bunchedBimonoidPredSuccCombInsert top topPos]; exact Nat.le_of_succ_le_succ runLenLe)
              (by
                rw [show (top - 1) + 2 = top + 1 from
                  congrArg Nat.succ (bunchedBimonoidPredSuccCombInsert top topPos)]
                exact Nat.le_of_succ_le_succ aboveBottom)
              (by
                rw [show (top - 1) + 2 = top + 1 from
                  congrArg Nat.succ (bunchedBimonoidPredSuccCombInsert top topPos)]
                exact Nat.le_of_succ_le widthOk))) ?_
        exact SaturatedConvOverWithId.symm (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
          (StrictAxiomRel.vcompAssoc (bunchedBimonoidSigmaAt wordWidth top)
            (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (top - 1) runLength) wordWidth)
            (bunchedBimonoidSigmaAt wordWidth letter)))
      · -- BASE: letter = top
        have eqTop : letter = top := Nat.le_antisymm letterLeTop geTop
        subst eqTop
        have runLenPos : 1 ≤ runLength :=
          bunchedBimonoidNatLeOfAddLeAddLeftCombInsert letter 1 runLength (Nat.le_of_succ_le_succ aboveBottom)
        cases runLength with
        | zero => exact absurd runLenPos (Nat.not_succ_le_zero 0)
        | succ lowerLen =>
            show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
                (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth (letter - 1))
                  (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth letter)
                    (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth (letter - 1))
                      (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (letter - 2) lowerLen)
                        wordWidth))))
                (CellExpr.vcomp
                  (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth letter)
                    (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth (letter - 1))
                      (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (letter - 2) lowerLen)
                        wordWidth)))
                  (bunchedBimonoidSigmaAt wordWidth letter))
            have hps : letter - 1 + 1 = letter := bunchedBimonoidPredSuccCombInsert letter letterPos
            have braidGate : (letter - 1) + 2 < wordWidth := by
              rw [show (letter - 1) + 2 = letter + 1 from congrArg Nat.succ hps]; exact widthOk
            have braid := bunchedBimonoidBraidWithTailConv wordWidth (letter - 1) braidGate
              (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (letter - 2) lowerLen) wordWidth)
            rw [hps] at braid
            have comm : SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
                (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth letter)
                  (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (letter - 2) lowerLen) wordWidth))
                (CellExpr.vcomp
                  (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (letter - 2) lowerLen) wordWidth)
                  (bunchedBimonoidSigmaAt wordWidth letter)) := by
              cases lowerLen with
              | zero =>
                  show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
                      (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth letter)
                        (CellExpr.id (bunchedBimonoidAWordPow wordWidth)))
                      (CellExpr.vcomp (CellExpr.id (bunchedBimonoidAWordPow wordWidth))
                        (bunchedBimonoidSigmaAt wordWidth letter))
                  exact SaturatedConvOverWithId.trans
                    (bunchedBimonoidSigmaAtTrailingIdAbsorbConv wordWidth letter widthOk)
                    (SaturatedConvOverWithId.symm
                      (vcompIdLeft_bridgedWithId (bunchedBimonoidSigmaAt wordWidth letter)
                        (bunchedBimonoidSigmaAtBoundaryReshapeConv wordWidth letter widthOk)
                        (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                          (StrictAxiomRel.vcompUnitLeft (bunchedBimonoidSigmaAt wordWidth letter)))))
              | succ lowerLenTwo =>
                  have letterGe2 : 2 ≤ letter :=
                    Nat.le_trans (Nat.le_add_left 2 lowerLenTwo) (Nat.le_of_succ_le_succ runLenLe)
                  exact bunchedBimonoidSwapCommutesRunBelowConv wordWidth letter (letter - 2) (lowerLenTwo + 1)
                    (Nat.le_of_eq (bunchedBimonoidSubTwoAddTwoCombInsert letter letterGe2)) widthOk
            exact SaturatedConvOverWithId.trans braid
              (SaturatedConvOverWithId.trans
                (SaturatedConvOverWithId.vcompCongrRight (bunchedBimonoidSigmaAt wordWidth letter)
                  (SaturatedConvOverWithId.vcompCongrRight (bunchedBimonoidSigmaAt wordWidth (letter - 1)) comm))
                (SaturatedConvOverWithId.symm
                  (SaturatedConvOverWithId.trans
                    (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                      (StrictAxiomRel.vcompAssoc (bunchedBimonoidSigmaAt wordWidth letter)
                        (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth (letter - 1))
                          (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (letter - 2) lowerLen)
                            wordWidth))
                        (bunchedBimonoidSigmaAt wordWidth letter)))
                    (SaturatedConvOverWithId.vcompCongrRight (bunchedBimonoidSigmaAt wordWidth letter)
                      (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                        (StrictAxiomRel.vcompAssoc (bunchedBimonoidSigmaAt wordWidth (letter - 1))
                          (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (letter - 2) lowerLen)
                            wordWidth)
                          (bunchedBimonoidSigmaAt wordWidth letter)))))))

/-! # =========================================================================================
    # A4 — THE FOUR-BRANCH COMB-INSERTION CONV STEP (`combInsertConv`, F2)
    # =========================================================================================
-/

/-- ★★★ **THE FOUR-BRANCH COMB-INSERTION CONV STEP (F2, DELIVERED).**  The CONV mirror of the r14 pure keystone
`bunchedBimonoidCombInsertDataRealizesSwap`: one `combInsertData` step, read at `permWord` granularity, is a single
right-post-composition by `sigmaAt (generatorCount + 1) letter`, over the star scope.  Four branches on the same
`Nat.lt_trichotomy (letter + stateRun) generatorCount` the DATA uses:

  * COMMUTE (`letter + stateRun + 2 <= gc`): B1 `permWordAppendConv` factors the shared prefix, the snoc CONV
    peels `letter`, and the shipped P3 `swapCommutesRunAboveConv` commutes it past the run above.
  * EXTEND (`letter + stateRun + 1 = gc`): the run snocs `letter` at its bottom (`descendingPositionsSnoc`), so
    the whole word is a single snoc — `permWordSnocConv` closes it directly.
  * CANCEL (`letter + stateRun = gc`): the run snocs `letter` (undoing it), the snoc CONV produces
    `s_letter ; s_letter`, the shipped S2 `cancelLetterConv` fires `s_k s_k ~ id`, and the trailing identity is
    absorbed (via `permWordBoundaryTarget` + `vcompIdRightBridgedWithId`).
  * CARRY (`letter + stateRun > gc`): B1 factors the prefix, the snoc peels `letter - 1`, and the NEW
    `carryPermConv` carries it through the run into `run ; s_letter`.

No prefix `mentionsOnlyBelow` validity is needed (each B1 firing splits off the self-validating descending run,
whose validity comes from `descendingPositionsMentionBelow`).  Gated exactly as the DATA keystone
(`stateRun <= gc`, `letter < gc`, `1 <= gc`). -/
theorem bunchedBimonoidCombInsertConv (generatorCount : Nat) (genPos : 1 ≤ generatorCount)
    (statePrefix : List Nat) (stateRun : Nat) (stateRunLe : stateRun ≤ generatorCount)
    (letter : Nat) (letterLt : letter < generatorCount) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidPermWord
        ((bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).1
          ++ bunchedBimonoidDescendingPositions (generatorCount - 1)
              (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).2)
        (generatorCount + 1))
      (CellExpr.vcomp
        (bunchedBimonoidPermWord (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
          (generatorCount + 1))
        (bunchedBimonoidSigmaAt (generatorCount + 1) letter)) := by
  have gcMinusOneLt : generatorCount - 1 < generatorCount :=
    Nat.le_of_eq (bunchedBimonoidPredSuccCombInsert generatorCount genPos)
  have runValid : bunchedBimonoidMentionsOnlyBelow generatorCount
      (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) = true :=
    bunchedBimonoidDescendingPositionsMentionBelowCombInsert generatorCount (generatorCount - 1) stateRun
      gcMinusOneLt
  have widthAboveGate : (generatorCount - 1) + 2 ≤ generatorCount + 1 :=
    Nat.le_of_eq (congrArg Nat.succ (bunchedBimonoidPredSuccCombInsert generatorCount genPos))
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
      have widthOk : letter + 2 ≤ generatorCount + 1 :=
        Nat.le_trans (Nat.le_trans (Nat.add_le_add_right (Nat.le_add_right letter stateRun) 2) condCommute)
          (Nat.le_succ generatorCount)
      have aboveGate : letter + stateRun + 1 ≤ generatorCount - 1 :=
        bunchedBimonoidNatLePredCombInsert (letter + stateRun + 1) generatorCount condCommute
      show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
          (bunchedBimonoidPermWord
            ((statePrefix ++ [letter]) ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
            (generatorCount + 1))
          (CellExpr.vcomp
            (bunchedBimonoidPermWord (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
              (generatorCount + 1))
            (bunchedBimonoidSigmaAt (generatorCount + 1) letter))
      exact SaturatedConvOverWithId.trans
        (bunchedBimonoidPermWordAppendConv (generatorCount + 1) (statePrefix ++ [letter])
          (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) runValid)
        (SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.vcompCongrLeft
            (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
              (generatorCount + 1))
            (bunchedBimonoidPermWordSnocConv (generatorCount + 1) letter widthOk statePrefix))
          (SaturatedConvOverWithId.trans
            (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
              (StrictAxiomRel.vcompAssoc (bunchedBimonoidPermWord statePrefix (generatorCount + 1))
                (bunchedBimonoidSigmaAt (generatorCount + 1) letter)
                (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
                  (generatorCount + 1))))
            (SaturatedConvOverWithId.trans
              (SaturatedConvOverWithId.vcompCongrRight (bunchedBimonoidPermWord statePrefix (generatorCount + 1))
                (bunchedBimonoidSwapCommutesRunAboveConv (generatorCount + 1) letter (generatorCount - 1) stateRun
                  aboveGate widthAboveGate))
              (SaturatedConvOverWithId.trans
                (SaturatedConvOverWithId.symm (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                  (StrictAxiomRel.vcompAssoc (bunchedBimonoidPermWord statePrefix (generatorCount + 1))
                    (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
                      (generatorCount + 1))
                    (bunchedBimonoidSigmaAt (generatorCount + 1) letter))))
                (SaturatedConvOverWithId.symm
                  (SaturatedConvOverWithId.vcompCongrLeft (bunchedBimonoidSigmaAt (generatorCount + 1) letter)
                    (bunchedBimonoidPermWordAppendConv (generatorCount + 1) statePrefix
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
      have widthOk : letter + 2 ≤ generatorCount + 1 := by
        have h1 : letter + 1 ≤ generatorCount := by
          rw [← hExtend]; exact Nat.add_le_add_right (Nat.le_add_right letter stateRun) 1
        exact Nat.succ_le_succ h1
      have letterEq : letter = (generatorCount - 1) - stateRun :=
        bunchedBimonoidNatEqSubOfAddEqCombInsert letter stateRun (generatorCount - 1)
          (bunchedBimonoidNatEqSubOfAddEqCombInsert (letter + stateRun) 1 generatorCount hExtend)
      have runSnoc : bunchedBimonoidDescendingPositions (generatorCount - 1) (stateRun + 1)
          = bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun ++ [letter] := by
        rw [letterEq]
        exact (bunchedBimonoidDescendingPositionsSnocCombInsert (generatorCount - 1) stateRun).symm
      have listEq : statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) (stateRun + 1)
          = (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) ++ [letter] := by
        rw [runSnoc]
        exact (bunchedBimonoidAppendAssocCombInsert statePrefix
          (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) [letter]).symm
      show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
          (bunchedBimonoidPermWord
            (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) (stateRun + 1))
            (generatorCount + 1))
          (CellExpr.vcomp
            (bunchedBimonoidPermWord (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
              (generatorCount + 1))
            (bunchedBimonoidSigmaAt (generatorCount + 1) letter))
      rw [listEq]
      exact bunchedBimonoidPermWordSnocConv (generatorCount + 1) letter widthOk
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
    have widthOk : letter + 2 ≤ generatorCount + 1 := Nat.succ_le_succ letterLt
    cases stateRun with
    | zero =>
        have hEqZero : letter = generatorCount := hEq
        exact absurd (hEqZero ▸ letterLt) (Nat.lt_irrefl generatorCount)
    | succ runPred =>
        show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
            (bunchedBimonoidPermWord (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) runPred)
              (generatorCount + 1))
            (CellExpr.vcomp
              (bunchedBimonoidPermWord
                (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) (runPred + 1))
                (generatorCount + 1))
              (bunchedBimonoidSigmaAt (generatorCount + 1) letter))
        have letterEq : letter = (generatorCount - 1) - runPred :=
          bunchedBimonoidNatEqSubOfAddEqCombInsert letter runPred (generatorCount - 1)
            (bunchedBimonoidNatEqSubOfAddEqCombInsert (letter + runPred) 1 generatorCount hEq)
        have runSnoc : bunchedBimonoidDescendingPositions (generatorCount - 1) (runPred + 1)
            = bunchedBimonoidDescendingPositions (generatorCount - 1) runPred ++ [letter] := by
          rw [letterEq]
          exact (bunchedBimonoidDescendingPositionsSnocCombInsert (generatorCount - 1) runPred).symm
        have listEq : statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) (runPred + 1)
            = (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) runPred) ++ [letter] := by
          rw [runSnoc]
          exact (bunchedBimonoidAppendAssocCombInsert statePrefix
            (bunchedBimonoidDescendingPositions (generatorCount - 1) runPred) [letter]).symm
        rw [listEq]
        have hbdry : boundaryTarget (bunchedBimonoidPermWord
            (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) runPred) (generatorCount + 1))
            = bunchedBimonoidAWordPow (generatorCount + 1) :=
          bunchedBimonoidPermWordBoundaryTarget (generatorCount + 1)
            (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) runPred)
        have hconv : SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
            (boundarySource (bunchedBimonoidSigmaAt (generatorCount + 1) letter))
            (boundaryTarget (bunchedBimonoidPermWord
              (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) runPred)
              (generatorCount + 1))) := by
          rw [hbdry]
          exact (bunchedBimonoidSigmaAtBoundaryReshapeConv (generatorCount + 1) letter widthOk).symm
        exact SaturatedConvOverWithId.symm
          (SaturatedConvOverWithId.trans
            (SaturatedConvOverWithId.vcompCongrLeft (bunchedBimonoidSigmaAt (generatorCount + 1) letter)
              (bunchedBimonoidPermWordSnocConv (generatorCount + 1) letter widthOk
                (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) runPred)))
            (SaturatedConvOverWithId.trans
              (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                (StrictAxiomRel.vcompAssoc
                  (bunchedBimonoidPermWord
                    (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) runPred)
                    (generatorCount + 1))
                  (bunchedBimonoidSigmaAt (generatorCount + 1) letter)
                  (bunchedBimonoidSigmaAt (generatorCount + 1) letter)))
              (SaturatedConvOverWithId.trans
                (SaturatedConvOverWithId.vcompCongrRight
                  (bunchedBimonoidPermWord
                    (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) runPred)
                    (generatorCount + 1))
                  (bunchedBimonoidCancelLetterConv (generatorCount + 1) letter))
                (bunchedBimonoidVcompIdRightBridgedWithId
                  (bunchedBimonoidPermWord
                    (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) runPred)
                    (generatorCount + 1))
                  hconv
                  (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                    (StrictAxiomRel.vcompUnitRight
                      (bunchedBimonoidPermWord
                        (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) runPred)
                        (generatorCount + 1))))))))
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
      exact bunchedBimonoidNatLeOfAddLeAddLeftCombInsert generatorCount 1 letter
        (by rw [Nat.add_comm letter generatorCount] at h1; exact h1)
    have widthOkCarry : (letter - 1) + 2 ≤ generatorCount + 1 := by
      rw [show (letter - 1) + 2 = letter + 1 from
        congrArg Nat.succ (bunchedBimonoidPredSuccCombInsert letter letterPos)]
      exact Nat.le_trans letterLt (Nat.le_succ generatorCount)
    show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
        (bunchedBimonoidPermWord
          ((statePrefix ++ [letter - 1]) ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
          (generatorCount + 1))
        (CellExpr.vcomp
          (bunchedBimonoidPermWord (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
            (generatorCount + 1))
          (bunchedBimonoidSigmaAt (generatorCount + 1) letter))
    exact SaturatedConvOverWithId.trans
      (bunchedBimonoidPermWordAppendConv (generatorCount + 1) (statePrefix ++ [letter - 1])
        (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) runValid)
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrLeft
          (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
            (generatorCount + 1))
          (bunchedBimonoidPermWordSnocConv (generatorCount + 1) (letter - 1) widthOkCarry statePrefix))
        (SaturatedConvOverWithId.trans
          (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
            (StrictAxiomRel.vcompAssoc (bunchedBimonoidPermWord statePrefix (generatorCount + 1))
              (bunchedBimonoidSigmaAt (generatorCount + 1) (letter - 1))
              (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
                (generatorCount + 1))))
          (SaturatedConvOverWithId.trans
            (SaturatedConvOverWithId.vcompCongrRight (bunchedBimonoidPermWord statePrefix (generatorCount + 1))
              (bunchedBimonoidCarryPermConv (generatorCount + 1) letter letterPos (generatorCount - 1) stateRun
                (bunchedBimonoidNatLePredCombInsert letter generatorCount letterLt)
                (by rw [bunchedBimonoidPredSuccCombInsert generatorCount genPos]; exact stateRunLe)
                (by
                  rw [show (generatorCount - 1) + 2 = generatorCount + 1 from
                    congrArg Nat.succ (bunchedBimonoidPredSuccCombInsert generatorCount genPos)]
                  exact hGt)
                widthAboveGate))
            (SaturatedConvOverWithId.trans
              (SaturatedConvOverWithId.symm (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
                (StrictAxiomRel.vcompAssoc (bunchedBimonoidPermWord statePrefix (generatorCount + 1))
                  (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
                    (generatorCount + 1))
                  (bunchedBimonoidSigmaAt (generatorCount + 1) letter))))
              (SaturatedConvOverWithId.symm
                (SaturatedConvOverWithId.vcompCongrLeft (bunchedBimonoidSigmaAt (generatorCount + 1) letter)
                  (bunchedBimonoidPermWordAppendConv (generatorCount + 1) statePrefix
                    (bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) runValid)))))))

/-! # =========================================================================================
    # A5 — THE COMB-FOLD CONV + THE ONE-LEVEL NORMAL-FORM CONV (F3)
    # =========================================================================================

★ The CONV mirror of the r14 pure `bunchedBimonoidCombFoldPreservesPerm` / `bunchedBimonoidCombNormalizeFormPreservesPerm`.
Structural on the remaining word `rest`, threading the state invariants through the shipped
`bunchedBimonoidCombInsertPreservesInvariants` and the per-step CONV through the F2 `combInsertConv`; the pure
`permOfWordAppendSplit` (permutation product) is replaced by the B1 CONV reshape `permWordAppendConv` (append is a
vcomp of the two `permWord` factors, gated on the run's `mentionsOnlyBelow`). -/

/-- `leftFlag = true` from `leftFlag && rightFlag = true` — full-enum (propext-clean). -/
private theorem bunchedBimonoidBoolAndLeftCombInsert :
    (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → leftFlag = true
  | true, _, _ => rfl
  | false, _, conj => Bool.noConfusion conj

/-- `rightFlag = true` from `leftFlag && rightFlag = true` — full-enum (propext-clean). -/
private theorem bunchedBimonoidBoolAndRightCombInsert :
    (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → rightFlag = true
  | true, _, conj => conj
  | false, _, conj => Bool.noConfusion conj

/-- `lower <= upper` from `Nat.ble lower upper = true` — structural on both (propext-clean). -/
private theorem bunchedBimonoidNatLeOfBleCombInsert :
    (lower upper : Nat) → Nat.ble lower upper = true → lower ≤ upper
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => Bool.noConfusion h
  | lower + 1, upper + 1, h => Nat.succ_le_succ (bunchedBimonoidNatLeOfBleCombInsert lower upper h)

/-- `lower < upper` from `Nat.blt lower upper = true` (`Nat.blt lower upper` is `Nat.ble (lower + 1) upper`). -/
private theorem bunchedBimonoidNatLtOfBltCombInsert (lower upper : Nat)
    (h : Nat.blt lower upper = true) : lower < upper :=
  bunchedBimonoidNatLeOfBleCombInsert (lower + 1) upper h

/-- List right-identity `list ++ [] = list` — structural on `list`. -/
private theorem bunchedBimonoidAppendNilCombInsert {alpha : Type _} :
    (list : List alpha) → list ++ [] = list
  | [] => rfl
  | head :: rest => congrArg (head :: ·) (bunchedBimonoidAppendNilCombInsert rest)

/-- ★★★ **THE COMB-FOLD CONV (from any state).**  Fold the F2 `combInsertConv` step down the remaining word,
threading the state invariants — the CONV mirror of the r14 pure `bunchedBimonoidCombFoldPreservesPerm`.
Structural on `rest`: the `[]` case is `refl` modulo the `list ++ [] = list` right-identity; the `letter :: restTail`
case chains the IH (from the post-insert state) with a B1 reshape splitting off `restTail`, the F2 step on the
head factor (via `vcompCongrLeft`), one `vcompAssoc` regrouping, and the B1 reshape run backwards to recombine
`(statePrefix ++ run) ++ (letter :: restTail)`. -/
theorem bunchedBimonoidCombFoldConv (generatorCount : Nat) (genPos : 1 ≤ generatorCount) :
    (rest : List Nat) → (statePrefix : List Nat) → (stateRun : Nat) →
    bunchedBimonoidMentionsOnlyBelow (generatorCount - 1) statePrefix = true → stateRun ≤ generatorCount →
    bunchedBimonoidMentionsOnlyBelow generatorCount rest = true →
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidPermWord
        ((rest.foldl (bunchedBimonoidCombInsertData generatorCount) (statePrefix, stateRun)).1
          ++ bunchedBimonoidDescendingPositions (generatorCount - 1)
              (rest.foldl (bunchedBimonoidCombInsertData generatorCount) (statePrefix, stateRun)).2)
        (generatorCount + 1))
      (bunchedBimonoidPermWord
        ((statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) ++ rest)
        (generatorCount + 1))
  | [], statePrefix, stateRun, _, _, _ => by
      show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
          (bunchedBimonoidPermWord
            (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) (generatorCount + 1))
          (bunchedBimonoidPermWord
            ((statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) ++ [])
            (generatorCount + 1))
      rw [bunchedBimonoidAppendNilCombInsert
        (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)]
      exact SaturatedConvOverWithId.refl _
  | letter :: restTail, statePrefix, stateRun, uBelow, runLe, hRange => by
      have letterLt : letter < generatorCount :=
        bunchedBimonoidNatLtOfBltCombInsert letter generatorCount
          (bunchedBimonoidBoolAndLeftCombInsert _ _ hRange)
      have restValid : bunchedBimonoidMentionsOnlyBelow generatorCount restTail = true :=
        bunchedBimonoidBoolAndRightCombInsert _ _ hRange
      obtain ⟨belowMid, runLeMid⟩ :=
        bunchedBimonoidCombInsertPreservesInvariants generatorCount genPos statePrefix stateRun uBelow runLe
          letter letterLt
      have ihConv := bunchedBimonoidCombFoldConv generatorCount genPos restTail
        (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).1
        (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).2 belowMid runLeMid restValid
      show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
          (bunchedBimonoidPermWord
            ((restTail.foldl (bunchedBimonoidCombInsertData generatorCount)
                (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter)).1
              ++ bunchedBimonoidDescendingPositions (generatorCount - 1)
                  (restTail.foldl (bunchedBimonoidCombInsertData generatorCount)
                    (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter)).2)
            (generatorCount + 1))
          (bunchedBimonoidPermWord
            ((statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
              ++ (letter :: restTail)) (generatorCount + 1))
      refine SaturatedConvOverWithId.trans ihConv ?_
      refine SaturatedConvOverWithId.trans
        (bunchedBimonoidPermWordAppendConv (generatorCount + 1)
          ((bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).1
            ++ bunchedBimonoidDescendingPositions (generatorCount - 1)
                (bunchedBimonoidCombInsertData generatorCount (statePrefix, stateRun) letter).2)
          restTail restValid) ?_
      refine SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrLeft
          (bunchedBimonoidPermWord restTail (generatorCount + 1))
          (bunchedBimonoidCombInsertConv generatorCount genPos statePrefix stateRun runLe letter letterLt)) ?_
      refine SaturatedConvOverWithId.trans
        (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
          (StrictAxiomRel.vcompAssoc
            (bunchedBimonoidPermWord
              (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun) (generatorCount + 1))
            (bunchedBimonoidSigmaAt (generatorCount + 1) letter)
            (bunchedBimonoidPermWord restTail (generatorCount + 1)))) ?_
      exact SaturatedConvOverWithId.symm
        (bunchedBimonoidPermWordAppendConv (generatorCount + 1)
          (statePrefix ++ bunchedBimonoidDescendingPositions (generatorCount - 1) stateRun)
          (letter :: restTail) hRange)

/-- ★★★ **THE ONE-LEVEL NORMAL-FORM CONV (F3).**  `permWord (combNormalizeForm gc input) (gc+1) ~ permWord input
(gc+1)` for in-range `input` — the CONV mirror of the r14 pure `bunchedBimonoidCombNormalizeFormPreservesPerm`.
`combFoldConv` from the empty state, with the empty-state word `([] ++ descendingPositions (gc-1) 0) ++ input`
reduced to `input` on the nose. -/
theorem bunchedBimonoidCombNormalizeFormConv (generatorCount : Nat) (genPos : 1 ≤ generatorCount)
    (input : List Nat) (inRange : bunchedBimonoidMentionsOnlyBelow generatorCount input = true) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidPermWord (bunchedBimonoidCombNormalizeForm generatorCount input) (generatorCount + 1))
      (bunchedBimonoidPermWord input (generatorCount + 1)) := by
  have folded := bunchedBimonoidCombFoldConv generatorCount genPos input [] 0 rfl
    (Nat.zero_le generatorCount) inRange
  have startEq : ([] ++ bunchedBimonoidDescendingPositions (generatorCount - 1) 0) ++ input = input := rfl
  rw [startEq] at folded
  exact folded

/-! # =========================================================================================
    # THE r25 NON-VACUITY + MATRIX SOUNDNESS PINS
    # =========================================================================================
-/

/-- ★ **`carryPermConv` fires at a genuine within-gate instance** — the smallest genuine CARRY at width 3:
`letter = 1`, `top = 1`, run length `2` (`descendingPositions 1 2 = [1, 0]`), so `s_0` carries through the run
`[1, 0]` into `[1, 0] ; s_1`.  Gates `1 <= 1`, `2 <= 2`, `1 + 2 = 3 <= letter + runLength = 3`, `1 + 2 = 3 <= 3`,
`1 <= 1` — all by `decide`.  A hypothesis-free inhabitant of
`vcomp (sigmaAt 3 0) (permWord [1, 0] 3) ~ vcomp (permWord [1, 0] 3) (sigmaAt 3 1)` over the star scope. -/
theorem bunchedBimonoidCarryPermConvWidthThreeInstance :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.vcomp (bunchedBimonoidSigmaAt 3 0)
        (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions 1 2) 3))
      (CellExpr.vcomp (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions 1 2) 3)
        (bunchedBimonoidSigmaAt 3 1)) :=
  bunchedBimonoidCarryPermConv 3 1 (by decide) 1 2 (by decide) (by decide) (by decide) (by decide)

/-- The carry base's Coxeter braid `s_0 s_1 s_0 = s_1 s_0 s_1` shares its `3 x 3` permutation matrix (the
reversal `[[0,0,1],[0,1,0],[1,0,0]]`), pinned in the RAW kernel-cheap left-associated form.  The
`permWord`-of-`[0,1,0]` phrasing carries the trailing `id (aWordPow 3)` node whose evaluation exceeds the kernel
`rfl` heartbeat budget (the r20/r21 endpoint-matrix compute wall); the CONV derivation is term-mode and needs no
matrix `rfl`, so this small witness is stated on the bare `vcomp` triple (byte-identical reduction to the shipped
`bunchedBimonoidGenericBraidThreeZeroMatrixShared`).  The `#eval decide` below witnesses the `permWord`-level
endpoints `[0,1,0]`/`[1,0,1]` agree on their matrix entries via the fast compiled evaluator. -/
theorem bunchedBimonoidCarryPermBraidMatrixShared :
    bunchedBimonoidEvalCell
        (CellExpr.vcomp (CellExpr.vcomp (bunchedBimonoidSigmaAt 3 0) (bunchedBimonoidSigmaAt 3 1))
          (bunchedBimonoidSigmaAt 3 0))
      = bunchedBimonoidEvalCell
        (CellExpr.vcomp (CellExpr.vcomp (bunchedBimonoidSigmaAt 3 1) (bunchedBimonoidSigmaAt 3 0))
          (bunchedBimonoidSigmaAt 3 1)) := rfl

#eval decide ((bunchedBimonoidEvalCell (bunchedBimonoidPermWord [0, 1, 0] 3)).entries
  = (bunchedBimonoidEvalCell (bunchedBimonoidPermWord [1, 0, 1] 3)).entries) -- expect true

/-- ★ **`combInsertConv` fires at a concrete CARRY step** — `generatorCount = 3`, `statePrefix = []`,
`stateRun = 2`, `letter = 2` (so `letter + stateRun = 4 > 3`, the CARRY branch).  A hypothesis-free inhabitant of
the four-branch step at the exact r9 jam configuration. -/
theorem bunchedBimonoidCombInsertConvCarryInstance :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidPermWord
        ((bunchedBimonoidCombInsertData 3 ([], 2) 2).1
          ++ bunchedBimonoidDescendingPositions 2 (bunchedBimonoidCombInsertData 3 ([], 2) 2).2) 4)
      (CellExpr.vcomp
        (bunchedBimonoidPermWord ([] ++ bunchedBimonoidDescendingPositions 2 2) 4)
        (bunchedBimonoidSigmaAt 4 2)) :=
  bunchedBimonoidCombInsertConv 3 (by decide) [] 2 (by decide) 2 (by decide)

/-- ★ **`combInsertConv` fires at a concrete COMMUTE step** — `generatorCount = 3`, `statePrefix = []`,
`stateRun = 0`, `letter = 0` (so `letter + stateRun + 2 = 2 <= 3`, the COMMUTE branch). -/
theorem bunchedBimonoidCombInsertConvCommuteInstance :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidPermWord
        ((bunchedBimonoidCombInsertData 3 ([], 0) 0).1
          ++ bunchedBimonoidDescendingPositions 2 (bunchedBimonoidCombInsertData 3 ([], 0) 0).2) 4)
      (CellExpr.vcomp
        (bunchedBimonoidPermWord ([] ++ bunchedBimonoidDescendingPositions 2 0) 4)
        (bunchedBimonoidSigmaAt 4 0)) :=
  bunchedBimonoidCombInsertConv 3 (by decide) [] 0 (by decide) 0 (by decide)

/-- ★ **`combInsertConv` fires at a concrete EXTEND step** — `generatorCount = 3`, `statePrefix = []`,
`stateRun = 2`, `letter = 0` (so `letter + stateRun + 1 = 3 = generatorCount`, the EXTEND branch): the run snocs
`letter` at its bottom, extending `descendingPositions 2 2` to `descendingPositions 2 3`. -/
theorem bunchedBimonoidCombInsertConvExtendInstance :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidPermWord
        ((bunchedBimonoidCombInsertData 3 ([], 2) 0).1
          ++ bunchedBimonoidDescendingPositions 2 (bunchedBimonoidCombInsertData 3 ([], 2) 0).2) 4)
      (CellExpr.vcomp
        (bunchedBimonoidPermWord ([] ++ bunchedBimonoidDescendingPositions 2 2) 4)
        (bunchedBimonoidSigmaAt 4 0)) :=
  bunchedBimonoidCombInsertConv 3 (by decide) [] 2 (by decide) 0 (by decide)

/-- ★ **`combInsertConv` fires at a concrete CANCEL step** — `generatorCount = 2`, `statePrefix = []`,
`stateRun = 1`, `letter = 1` (so `letter + stateRun = 2 = generatorCount`, the CANCEL branch): the snocked
`s_letter` meets the run's trailing `s_letter` and cancels `s_k s_k ~ id`, dropping the run from
`descendingPositions 1 1` to `descendingPositions 1 0 = []`. -/
theorem bunchedBimonoidCombInsertConvCancelInstance :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidPermWord
        ((bunchedBimonoidCombInsertData 2 ([], 1) 1).1
          ++ bunchedBimonoidDescendingPositions 1 (bunchedBimonoidCombInsertData 2 ([], 1) 1).2) 3)
      (CellExpr.vcomp
        (bunchedBimonoidPermWord ([] ++ bunchedBimonoidDescendingPositions 1 1) 3)
        (bunchedBimonoidSigmaAt 3 1)) :=
  bunchedBimonoidCombInsertConv 2 (by decide) [] 1 (by decide) 1 (by decide)

/-- ★ **`combNormalizeFormConv` (F3) fires at the r9 jam word** — `generatorCount = 3`, `input = [2, 0, 1, 2]`
(the exact word the Brauer insertion residual jammed on): one comb level converts `permWord (combNormalizeForm 3
[2,0,1,2]) 4 ~ permWord [2,0,1,2] 4` over the star scope.  A hypothesis-free inhabitant of the one-level fold at
the recon's headline configuration. -/
theorem bunchedBimonoidCombNormalizeFormConvJamInstance :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidPermWord (bunchedBimonoidCombNormalizeForm 3 [2, 0, 1, 2]) 4)
      (bunchedBimonoidPermWord [2, 0, 1, 2] 4) :=
  bunchedBimonoidCombNormalizeFormConv 3 (by decide) [2, 0, 1, 2] (by decide)

/-! # =========================================================================================
    # THE r25 HONESTY MARKERS (fresh markers per literal delivery; owners + r23/r24 markers byte-intact)
    # =========================================================================================
-/

/-- ★★★ **ESTABLISHED (A3) — the permutation-carry CONV atom `carryPermConv` is DELIVERED.**  `= true` records
`bunchedBimonoidCarryPermConv`: `s_{letter-1}` carries through a whole descending run into `run ; s_letter`, the
CONV mirror of the r14 pure `bunchedBimonoidCarryPerm`, structural on the run length.  STEP peels the run-top by
the shipped P2 `sigmaAtDistantCommuteConv`; BASE fires the r24 braid via `bunchedBimonoidBraidWithTailConv` then
the shipped F1 `swapCommutesRunBelowConv` (or the P1 unit commutation) past the lower sub-run.  This is the single
genuinely-new atom the CARRY unblock needed — the r23 "braid-walled" verdict is retired by the r24 braid atom.
Matrix-sound (the width-3 braid pin `[0,1,0]`/`[1,0,1]`) and non-vacuous (the width-3 smallest-carry instance).
Zero-axiom. -/
def fxBunchedBimonoid_carryPermConvShipped : Bool := true

/-- ★★★ **ESTABLISHED (F2) — the four-branch comb-insertion CONV step `combInsertConv` is DELIVERED.**  `= true`
records `bunchedBimonoidCombInsertConv`: one `combInsertData` step, at `permWord` granularity, is a single
right-post-composition by `sigmaAt (gc+1) letter` over the star scope — the CONV mirror of the r14 pure keystone
`bunchedBimonoidCombInsertDataRealizesSwap`.  Four branches assembled from shipped bricks: COMMUTE (B1
`permWordAppendConv` + `permWordSnocConv` + P3 `swapCommutesRunAboveConv`), EXTEND (`descendingPositionsSnoc` +
`permWordSnocConv`), CANCEL (`permWordSnocConv` + S2 `cancelLetterConv` + `permWordBoundaryTarget` +
`vcompIdRightBridgedWithId`), CARRY (B1 + `permWordSnocConv` + the NEW `carryPermConv`).  Closes the F2 clause of
the r23 census marker `fxBunchedBimonoid_combFoldsBraidWalledDownstreamOfCarry` (retire-name-only; that marker
stays `= false` byte-intact cross-file, superseded by the r24 braid atom).  Non-vacuous (COMMUTE + CARRY concrete
instances).  Zero-axiom. -/
def fxBunchedBimonoid_combInsertConvShipped : Bool := true

/-- ★★★ **ESTABLISHED (F3) — the one-level comb normal-form CONV `combNormalizeFormConv` is DELIVERED.**
`= true` records `bunchedBimonoidCombNormalizeFormConv`: `permWord (combNormalizeForm gc input) (gc+1) ~ permWord
input (gc+1)` for in-range `input`, the CONV mirror of the r14 pure `bunchedBimonoidCombNormalizeFormPreservesPerm`.
Built by folding the F2 `combInsertConv` step down the word (`bunchedBimonoidCombFoldConv`, structural on the
remaining word, threading the shipped `combInsertPreservesInvariants` and the B1 `permWordAppendConv` reshape),
from the empty state.  Non-vacuous (the r9 jam-word instance `[2,0,1,2]` at generator count 3).  Closes the F3
clause of the r25 census.  Zero-axiom. -/
def fxBunchedBimonoid_combNormalizeFormConvShipped : Bool := true

/-- ★ **THE LEVEL RECURSION + THE OWNER FLIP STAY OPEN — the honest r25 census, no fabricated flip.**  `= false`
records what this round does NOT reach: the recursive comb staircase `recCombConv` (F4, structural on the generator
count, recursing through F3 `combNormalizeFormConv`) and the `CoxeterUniqueness` owner flip (F4 twice + the shipped
r18 T3 `recCombEqOfEvalEq`).  With F2 (`combInsertConv`) and F3 (`combNormalizeFormConv`) shipped this round, F4 is
the SOLE remaining CONV node before the owner flip; everything under it (F2, F3, the T3 data half, `combCanonicity`)
is now shipped.  The four star owners (StarAssembly / RiffleAssembly / CollisionCanonForm / CoxeterUniqueness) stay
`= false` byte-intact; `StrictAxioms.lean` + the shipped star scope are untouched (only the shipped
`StrictAxiomRel.{vcompAssoc, vcompUnitLeft, vcompUnitRight}` rows consumed).  The r23 census marker and the r24
braid marker keep their names and values byte-intact.  No fabricated star flip. -/
def fxBunchedBimonoid_recCombConvAndOwnerFlipStillOpen : Bool := false

end FX1Poly.Polygraph.Omega
