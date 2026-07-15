-- TODO: DELETE THIS GARBAGE -- defective bunchedBimonoid star (refuted r29/r30/r31); superseded by the LafontProp re-founding
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidStarDimTwoCanonicalRestatement
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidPermMatrixExtractorKit

/-! # Polygraph/Omega/WalkingBunchedBimonoidStarDimTwoCanonicalFires — the corrected target FIRED on concrete
data: the block-threading family satisfies every guard at EVERY width (positive fire, flagship width 6 with the
full premise vector incl. matrix equality), and the mu/delta pair is the negative control (WP-PROP r29, #2033)

★★ **THE FIRES.**  The r29 restatement names the corrected dim-2 canonical-gens target; this file proves it is
neither vacuous nor trivial on the lane's own data:

  * **the POSITIVE family fire** — the mu- and delta-side block-threading pairs
    (`bunchedBimonoidSigmaPast{MuFold,DeltaFan}Block{Left,Right} k`) satisfy ALL SIX structural guards
    (additive x2, well-typed x2, canonical x2) at EVERY width `k`
    (`bunchedBimonoidBlockThreadingPairSatisfiesGuards{Mu,Delta}`), and the corrected star's implication holds
    at the whole family (`bunchedBimonoidCorrectedStarHoldsAtBlockThreadingFamily{Mu,Delta}` — the conclusion is
    the r29-delivered CONV, premises not even needed).  The dimension census
    (`...MatrixRows/Cols` for the folds, fans, and both braidings) powers the well-typedness induction.
  * **the FLAGSHIP width-6 fire** — at `k = 6` (far above the natural width) the FULL premise vector holds
    including the `Mat(N)` equality (`bunchedBimonoidBlockThreadingPairMatrixEqAtWidthSix`, assembled from the
    r27 kernel-`decide` entries agreement through the shipped `bunchedBimonoidMatEqOfEntries` — no wide `rfl`),
    so the corrected target's instance at the pair is FULLY discharged
    (`bunchedBimonoidCorrectedStarFiredPositiveAtWidthSix`).
  * **the NEGATIVE control** — `mu_a` vs `delta_a`: both additive, well-typed, canonical, but their matrices
    DIFFER (`bunchedBimonoidMuDeltaMatricesDiffer`, a `rows` clash `1 != 2`), so the corrected star's premises
    are unsatisfiable at the pair — the target does not over-identify
    (`bunchedBimonoidCorrectedStarNegativeControlMuDelta`).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # THE DIMENSION CENSUS — rows / cols of the folds, fans, powers, and braidings
    # =========================================================================================
-/

/-- The shipped word-power width, re-typed through `bunchedBimonoidWordWidth` (the `Nat`-pinned wrapper) so
`rw` can fire inside `HAdd`-spelled goals. -/
theorem bunchedBimonoidAWordPowWordWidth (wordWidth : Nat) :
    bunchedBimonoidWordWidth (bunchedBimonoidAWordPow wordWidth) = wordWidth :=
  bunchedBimonoidAWordPowWidth wordWidth

/-- The mu-fold's matrix has ONE row at every width (the fold output; the peel layer ends in `mu`). -/
theorem bunchedBimonoidMuFoldMatrixRows :
    ∀ (blockWidth : Nat), (bunchedBimonoidEvalCell (bunchedBimonoidMuFold blockWidth)).rows = 1
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- The mu-fold's matrix has `blockWidth` columns (the fold inputs; induction on the peel). -/
theorem bunchedBimonoidMuFoldMatrixCols :
    ∀ (blockWidth : Nat), (bunchedBimonoidEvalCell (bunchedBimonoidMuFold blockWidth)).cols = blockWidth
  | 0 => rfl
  | 1 => rfl
  | k + 2 => congrArg (fun colCount => colCount + 1) (bunchedBimonoidMuFoldMatrixCols (k + 1))

/-- The delta-fan's matrix has ONE column at every width (the fan input; the peel layer starts with `delta`). -/
theorem bunchedBimonoidDeltaFanMatrixCols :
    ∀ (blockWidth : Nat), (bunchedBimonoidEvalCell (bunchedBimonoidDeltaFan blockWidth)).cols = 1
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- The delta-fan's matrix has `blockWidth` rows (the fan outputs). -/
theorem bunchedBimonoidDeltaFanMatrixRows :
    ∀ (blockWidth : Nat), (bunchedBimonoidEvalCell (bunchedBimonoidDeltaFan blockWidth)).rows = blockWidth
  | 0 => rfl
  | 1 => rfl
  | k + 2 => congrArg (fun rowCount => rowCount + 1) (bunchedBimonoidDeltaFanMatrixRows (k + 1))

/-- The forward block braiding is `(blockWidth + 1)`-square: rows. -/
theorem bunchedBimonoidStrandPastBlockMatrixRows :
    ∀ (blockWidth : Nat),
      (bunchedBimonoidEvalCell (bunchedBimonoidStrandPastBlock blockWidth)).rows = blockWidth + 1
  | 0 => rfl
  | 1 => rfl
  | k + 2 =>
      (congrArg (Nat.add 1) (bunchedBimonoidStrandPastBlockMatrixRows (k + 1))).trans
        (Nat.add_comm 1 (k + 2))

/-- The forward block braiding is `(blockWidth + 1)`-square: cols. -/
theorem bunchedBimonoidStrandPastBlockMatrixCols :
    ∀ (blockWidth : Nat),
      (bunchedBimonoidEvalCell (bunchedBimonoidStrandPastBlock blockWidth)).cols = blockWidth + 1
  | 0 => rfl
  | 1 => rfl
  | k + 2 =>
      (congrArg (fun width => Nat.add 2 width) (bunchedBimonoidAWordPowWidth (k + 1))).trans
        (Nat.add_comm 2 (k + 1))

/-- The reverse block braiding is `(blockWidth + 1)`-square: rows. -/
theorem bunchedBimonoidStrandPastBlockRevMatrixRows :
    ∀ (blockWidth : Nat),
      (bunchedBimonoidEvalCell (bunchedBimonoidStrandPastBlockRev blockWidth)).rows = blockWidth + 1
  | 0 => rfl
  | 1 => rfl
  | k + 2 =>
      congrArg (fun rowCount => rowCount + 1) (bunchedBimonoidStrandPastBlockRevMatrixRows (k + 1))

/-- The reverse block braiding is `(blockWidth + 1)`-square: cols. -/
theorem bunchedBimonoidStrandPastBlockRevMatrixCols :
    ∀ (blockWidth : Nat),
      (bunchedBimonoidEvalCell (bunchedBimonoidStrandPastBlockRev blockWidth)).cols = blockWidth + 1
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
      show bunchedBimonoidWordWidth (bunchedBimonoidAWordPow (k + 1)) + 2 = k + 2 + 1
      rw [bunchedBimonoidAWordPowWordWidth (k + 1)]

/-! # =========================================================================================
    # THE GUARD INDUCTIONS — additivity, well-typedness, canonicity of the whole family
    # =========================================================================================
-/

/-- Every word power is additive. -/
theorem bunchedBimonoidAWordPowAdditive :
    ∀ (wordWidth : Nat),
      bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidAWordPow wordWidth) = true
  | 0 => rfl
  | n + 1 => by
      show (true && bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidAWordPow n)) = true
      rw [bunchedBimonoidAWordPowAdditive n]
      rfl

/-- Every mu-fold is additive. -/
theorem bunchedBimonoidMuFoldAdditive :
    ∀ (blockWidth : Nat),
      bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidMuFold blockWidth) = true
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
      show ((bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidMuFold (k + 1)) && true) && true) = true
      rw [bunchedBimonoidMuFoldAdditive (k + 1)]
      rfl

/-- Every delta-fan is additive. -/
theorem bunchedBimonoidDeltaFanAdditive :
    ∀ (blockWidth : Nat),
      bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidDeltaFan blockWidth) = true
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
      show (true && (bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidDeltaFan (k + 1)) && true)) = true
      rw [bunchedBimonoidDeltaFanAdditive (k + 1)]
      rfl

/-- Every forward block braiding is additive. -/
theorem bunchedBimonoidStrandPastBlockAdditive :
    ∀ (blockWidth : Nat),
      bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidStrandPastBlock blockWidth) = true
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
      show ((true && bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidAWordPow (k + 1)))
          && (true && bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidStrandPastBlock (k + 1)))) = true
      rw [bunchedBimonoidAWordPowAdditive (k + 1), bunchedBimonoidStrandPastBlockAdditive (k + 1)]
      rfl

/-- Every reverse block braiding is additive. -/
theorem bunchedBimonoidStrandPastBlockRevAdditive :
    ∀ (blockWidth : Nat),
      bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidStrandPastBlockRev blockWidth) = true
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
      show ((bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidAWordPow (k + 1)) && true)
          && (bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidStrandPastBlockRev (k + 1)) && true)) = true
      rw [bunchedBimonoidAWordPowAdditive (k + 1), bunchedBimonoidStrandPastBlockRevAdditive (k + 1)]
      rfl

/-- The additive unit is well-typed (`0 = 0` and `1 = 1` width agreements). -/
theorem bunchedBimonoidAddEtaGenWellTyped : bunchedBimonoidCellWellTyped bunchedBimonoidAddEtaGen :=
  ⟨True.intro, ⟨True.intro, True.intro, True.intro⟩, rfl, rfl⟩

/-- The additive counit is well-typed. -/
theorem bunchedBimonoidAddEpsGenWellTyped : bunchedBimonoidCellWellTyped bunchedBimonoidAddEpsGen :=
  ⟨⟨True.intro, True.intro, True.intro⟩, True.intro, rfl, rfl⟩

/-- Every word power is well-typed (dimension-1 composition carries no matrix constraint). -/
theorem bunchedBimonoidAWordPowWellTyped :
    ∀ (wordWidth : Nat), bunchedBimonoidCellWellTyped (bunchedBimonoidAWordPow wordWidth)
  | 0 => True.intro
  | n + 1 =>
      ⟨⟨True.intro, True.intro, True.intro⟩, bunchedBimonoidAWordPowWellTyped n, True.intro⟩

/-- Every mu-fold is well-typed — the peel layer's composability is the rows census. -/
theorem bunchedBimonoidMuFoldWellTyped :
    ∀ (blockWidth : Nat), bunchedBimonoidCellWellTyped (bunchedBimonoidMuFold blockWidth)
  | 0 => bunchedBimonoidAddEtaGenWellTyped
  | 1 => ⟨True.intro, True.intro, True.intro⟩
  | k + 2 =>
      ⟨⟨bunchedBimonoidMuFoldWellTyped (k + 1), ⟨True.intro, True.intro, True.intro⟩⟩,
        bunchedBimonoidAddMuGenWellTyped,
        congrArg (fun rowCount => rowCount + 1) (bunchedBimonoidMuFoldMatrixRows (k + 1))⟩

/-- Every delta-fan is well-typed — the peel layer's composability is the cols census. -/
theorem bunchedBimonoidDeltaFanWellTyped :
    ∀ (blockWidth : Nat), bunchedBimonoidCellWellTyped (bunchedBimonoidDeltaFan blockWidth)
  | 0 => bunchedBimonoidAddEpsGenWellTyped
  | 1 => ⟨True.intro, True.intro, True.intro⟩
  | k + 2 =>
      ⟨bunchedBimonoidAddDeltaGenWellTyped,
        ⟨bunchedBimonoidDeltaFanWellTyped (k + 1), ⟨True.intro, True.intro, True.intro⟩⟩,
        by
          show (2 : Nat) = (bunchedBimonoidEvalCell (bunchedBimonoidDeltaFan (k + 1))).cols + 1
          rw [bunchedBimonoidDeltaFanMatrixCols (k + 1)]⟩

/-- Every forward block braiding is well-typed — the recursion layer's composability is the square census. -/
theorem bunchedBimonoidStrandPastBlockWellTyped :
    ∀ (blockWidth : Nat), bunchedBimonoidCellWellTyped (bunchedBimonoidStrandPastBlock blockWidth)
  | 0 => ⟨True.intro, True.intro, True.intro⟩
  | 1 => bunchedBimonoidAddSigmaGenWellTyped
  | k + 2 =>
      ⟨⟨bunchedBimonoidAddSigmaGenWellTyped, bunchedBimonoidAWordPowWellTyped (k + 1)⟩,
        ⟨⟨True.intro, True.intro, True.intro⟩, bunchedBimonoidStrandPastBlockWellTyped (k + 1)⟩,
        by
          show 2 + bunchedBimonoidWordWidth (bunchedBimonoidAWordPow (k + 1))
            = 1 + (bunchedBimonoidEvalCell (bunchedBimonoidStrandPastBlock (k + 1))).cols
          rw [bunchedBimonoidAWordPowWordWidth (k + 1),
            bunchedBimonoidStrandPastBlockMatrixCols (k + 1)]
          rw [Nat.add_comm 2 (k + 1), Nat.add_comm 1 (k + 2)]⟩

/-- Every reverse block braiding is well-typed. -/
theorem bunchedBimonoidStrandPastBlockRevWellTyped :
    ∀ (blockWidth : Nat), bunchedBimonoidCellWellTyped (bunchedBimonoidStrandPastBlockRev blockWidth)
  | 0 => ⟨True.intro, True.intro, True.intro⟩
  | 1 => bunchedBimonoidAddSigmaGenWellTyped
  | k + 2 =>
      ⟨⟨bunchedBimonoidAWordPowWellTyped (k + 1), bunchedBimonoidAddSigmaGenWellTyped⟩,
        ⟨bunchedBimonoidStrandPastBlockRevWellTyped (k + 1), ⟨True.intro, True.intro, True.intro⟩⟩,
        by
          show bunchedBimonoidWordWidth (bunchedBimonoidAWordPow (k + 1)) + 2
            = (bunchedBimonoidEvalCell (bunchedBimonoidStrandPastBlockRev (k + 1))).cols + 1
          rw [bunchedBimonoidAWordPowWordWidth (k + 1),
            bunchedBimonoidStrandPastBlockRevMatrixCols (k + 1)]⟩

/-- The additive unit is canonical. -/
theorem bunchedBimonoidAddEtaGenCanonical : bunchedBimonoidCellGensCanonical bunchedBimonoidAddEtaGen :=
  ⟨Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), True.intro, bunchedBimonoidAdditiveGenCanonical⟩

/-- The additive counit is canonical. -/
theorem bunchedBimonoidAddEpsGenCanonical : bunchedBimonoidCellGensCanonical bunchedBimonoidAddEpsGen :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))), bunchedBimonoidAdditiveGenCanonical, True.intro⟩

/-- Every word power is canonical. -/
theorem bunchedBimonoidAWordPowCanonical :
    ∀ (wordWidth : Nat), bunchedBimonoidCellGensCanonical (bunchedBimonoidAWordPow wordWidth)
  | 0 => True.intro
  | n + 1 => ⟨bunchedBimonoidAdditiveGenCanonical, bunchedBimonoidAWordPowCanonical n⟩

/-- Every mu-fold is canonical. -/
theorem bunchedBimonoidMuFoldCanonical :
    ∀ (blockWidth : Nat), bunchedBimonoidCellGensCanonical (bunchedBimonoidMuFold blockWidth)
  | 0 => bunchedBimonoidAddEtaGenCanonical
  | 1 => bunchedBimonoidAdditiveGenCanonical
  | k + 2 =>
      ⟨⟨bunchedBimonoidMuFoldCanonical (k + 1), bunchedBimonoidAdditiveGenCanonical⟩,
        bunchedBimonoidAddMuGenCanonical⟩

/-- Every delta-fan is canonical. -/
theorem bunchedBimonoidDeltaFanCanonical :
    ∀ (blockWidth : Nat), bunchedBimonoidCellGensCanonical (bunchedBimonoidDeltaFan blockWidth)
  | 0 => bunchedBimonoidAddEpsGenCanonical
  | 1 => bunchedBimonoidAdditiveGenCanonical
  | k + 2 =>
      ⟨bunchedBimonoidAddDeltaGenCanonical,
        ⟨bunchedBimonoidDeltaFanCanonical (k + 1), bunchedBimonoidAdditiveGenCanonical⟩⟩

/-- Every forward block braiding is canonical. -/
theorem bunchedBimonoidStrandPastBlockCanonical :
    ∀ (blockWidth : Nat), bunchedBimonoidCellGensCanonical (bunchedBimonoidStrandPastBlock blockWidth)
  | 0 => bunchedBimonoidAdditiveGenCanonical
  | 1 => bunchedBimonoidAddSigmaGenCanonical
  | k + 2 =>
      ⟨⟨bunchedBimonoidAddSigmaGenCanonical, bunchedBimonoidAWordPowCanonical (k + 1)⟩,
        ⟨bunchedBimonoidAdditiveGenCanonical, bunchedBimonoidStrandPastBlockCanonical (k + 1)⟩⟩

/-- Every reverse block braiding is canonical. -/
theorem bunchedBimonoidStrandPastBlockRevCanonical :
    ∀ (blockWidth : Nat), bunchedBimonoidCellGensCanonical (bunchedBimonoidStrandPastBlockRev blockWidth)
  | 0 => bunchedBimonoidAdditiveGenCanonical
  | 1 => bunchedBimonoidAddSigmaGenCanonical
  | k + 2 =>
      ⟨⟨bunchedBimonoidAWordPowCanonical (k + 1), bunchedBimonoidAddSigmaGenCanonical⟩,
        ⟨bunchedBimonoidStrandPastBlockRevCanonical (k + 1), bunchedBimonoidAdditiveGenCanonical⟩⟩

/-! # =========================================================================================
    # THE POSITIVE FAMILY FIRE — all six structural guards at every width, both colours
    # =========================================================================================
-/

/-- ★★ **The mu-side block-threading pair satisfies ALL SIX structural guards at EVERY width** — additive x2,
well-typed x2 (the composability arms discharged by the dimension census), canonical x2.  The corrected target's
premise vector, minus only the matrix equality, holds generically. -/
theorem bunchedBimonoidBlockThreadingPairSatisfiesGuardsMu (blockWidth : Nat) :
    bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidSigmaPastMuFoldBlockLeft blockWidth) = true
      ∧ bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidSigmaPastMuFoldBlockRight blockWidth) = true
      ∧ bunchedBimonoidCellWellTyped (bunchedBimonoidSigmaPastMuFoldBlockLeft blockWidth)
      ∧ bunchedBimonoidCellWellTyped (bunchedBimonoidSigmaPastMuFoldBlockRight blockWidth)
      ∧ bunchedBimonoidCellGensCanonical (bunchedBimonoidSigmaPastMuFoldBlockLeft blockWidth)
      ∧ bunchedBimonoidCellGensCanonical (bunchedBimonoidSigmaPastMuFoldBlockRight blockWidth) :=
  ⟨by
      show ((true && bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidMuFold blockWidth)) && true) = true
      rw [bunchedBimonoidMuFoldAdditive blockWidth]
      rfl,
    by
      show (bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidStrandPastBlock blockWidth)
          && (bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidMuFold blockWidth) && true)) = true
      rw [bunchedBimonoidMuFoldAdditive blockWidth, bunchedBimonoidStrandPastBlockAdditive blockWidth]
      rfl,
    ⟨⟨⟨True.intro, True.intro, True.intro⟩, bunchedBimonoidMuFoldWellTyped blockWidth⟩,
      bunchedBimonoidAddSigmaGenWellTyped,
      by
        show 1 + (bunchedBimonoidEvalCell (bunchedBimonoidMuFold blockWidth)).rows = 2
        rw [bunchedBimonoidMuFoldMatrixRows blockWidth]⟩,
    ⟨bunchedBimonoidStrandPastBlockWellTyped blockWidth,
      ⟨bunchedBimonoidMuFoldWellTyped blockWidth, ⟨True.intro, True.intro, True.intro⟩⟩,
      by
        show (bunchedBimonoidEvalCell (bunchedBimonoidStrandPastBlock blockWidth)).rows
          = (bunchedBimonoidEvalCell (bunchedBimonoidMuFold blockWidth)).cols + 1
        rw [bunchedBimonoidStrandPastBlockMatrixRows blockWidth,
          bunchedBimonoidMuFoldMatrixCols blockWidth]⟩,
    ⟨⟨bunchedBimonoidAdditiveGenCanonical, bunchedBimonoidMuFoldCanonical blockWidth⟩,
      bunchedBimonoidAddSigmaGenCanonical⟩,
    ⟨bunchedBimonoidStrandPastBlockCanonical blockWidth,
      ⟨bunchedBimonoidMuFoldCanonical blockWidth, bunchedBimonoidAdditiveGenCanonical⟩⟩⟩

/-- ★★ The delta-side pair satisfies all six structural guards at every width. -/
theorem bunchedBimonoidBlockThreadingPairSatisfiesGuardsDelta (blockWidth : Nat) :
    bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidSigmaPastDeltaFanBlockLeft blockWidth) = true
      ∧ bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidSigmaPastDeltaFanBlockRight blockWidth) = true
      ∧ bunchedBimonoidCellWellTyped (bunchedBimonoidSigmaPastDeltaFanBlockLeft blockWidth)
      ∧ bunchedBimonoidCellWellTyped (bunchedBimonoidSigmaPastDeltaFanBlockRight blockWidth)
      ∧ bunchedBimonoidCellGensCanonical (bunchedBimonoidSigmaPastDeltaFanBlockLeft blockWidth)
      ∧ bunchedBimonoidCellGensCanonical (bunchedBimonoidSigmaPastDeltaFanBlockRight blockWidth) :=
  ⟨by
      show (true && (true && bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidDeltaFan blockWidth))) = true
      rw [bunchedBimonoidDeltaFanAdditive blockWidth]
      rfl,
    by
      show ((bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidDeltaFan blockWidth) && true)
          && bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidStrandPastBlockRev blockWidth)) = true
      rw [bunchedBimonoidDeltaFanAdditive blockWidth, bunchedBimonoidStrandPastBlockRevAdditive blockWidth]
      rfl,
    ⟨bunchedBimonoidAddSigmaGenWellTyped,
      ⟨⟨True.intro, True.intro, True.intro⟩, bunchedBimonoidDeltaFanWellTyped blockWidth⟩,
      by
        show (2 : Nat) = 1 + (bunchedBimonoidEvalCell (bunchedBimonoidDeltaFan blockWidth)).cols
        rw [bunchedBimonoidDeltaFanMatrixCols blockWidth]⟩,
    ⟨⟨bunchedBimonoidDeltaFanWellTyped blockWidth, ⟨True.intro, True.intro, True.intro⟩⟩,
      bunchedBimonoidStrandPastBlockRevWellTyped blockWidth,
      by
        show (bunchedBimonoidEvalCell (bunchedBimonoidDeltaFan blockWidth)).rows + 1
          = (bunchedBimonoidEvalCell (bunchedBimonoidStrandPastBlockRev blockWidth)).cols
        rw [bunchedBimonoidDeltaFanMatrixRows blockWidth,
          bunchedBimonoidStrandPastBlockRevMatrixCols blockWidth]⟩,
    ⟨bunchedBimonoidAddSigmaGenCanonical,
      ⟨bunchedBimonoidAdditiveGenCanonical, bunchedBimonoidDeltaFanCanonical blockWidth⟩⟩,
    ⟨⟨bunchedBimonoidDeltaFanCanonical blockWidth, bunchedBimonoidAdditiveGenCanonical⟩,
      bunchedBimonoidStrandPastBlockRevCanonical blockWidth⟩⟩

/-- ★★ **The corrected star's implication HOLDS at the whole mu-side family** — the conclusion is the
r29-delivered CONV, so the restricted instance is a theorem at every width. -/
theorem bunchedBimonoidCorrectedStarHoldsAtBlockThreadingFamilyMu (blockWidth : Nat) :
    bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidSigmaPastMuFoldBlockLeft blockWidth) = true →
    bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidSigmaPastMuFoldBlockRight blockWidth) = true →
    bunchedBimonoidCellWellTyped (bunchedBimonoidSigmaPastMuFoldBlockLeft blockWidth) →
    bunchedBimonoidCellWellTyped (bunchedBimonoidSigmaPastMuFoldBlockRight blockWidth) →
    bunchedBimonoidCellGensCanonical (bunchedBimonoidSigmaPastMuFoldBlockLeft blockWidth) →
    bunchedBimonoidCellGensCanonical (bunchedBimonoidSigmaPastMuFoldBlockRight blockWidth) →
    bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockLeft blockWidth)
      = bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockRight blockWidth) →
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidSigmaPastMuFoldBlockLeft blockWidth)
      (bunchedBimonoidSigmaPastMuFoldBlockRight blockWidth) :=
  fun _ _ _ _ _ _ _ => bunchedBimonoidSigmaPastMuFoldBlockThreadConv blockWidth

/-- ★★ The delta-side family instance of the corrected star. -/
theorem bunchedBimonoidCorrectedStarHoldsAtBlockThreadingFamilyDelta (blockWidth : Nat) :
    bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidSigmaPastDeltaFanBlockLeft blockWidth) = true →
    bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidSigmaPastDeltaFanBlockRight blockWidth) = true →
    bunchedBimonoidCellWellTyped (bunchedBimonoidSigmaPastDeltaFanBlockLeft blockWidth) →
    bunchedBimonoidCellWellTyped (bunchedBimonoidSigmaPastDeltaFanBlockRight blockWidth) →
    bunchedBimonoidCellGensCanonical (bunchedBimonoidSigmaPastDeltaFanBlockLeft blockWidth) →
    bunchedBimonoidCellGensCanonical (bunchedBimonoidSigmaPastDeltaFanBlockRight blockWidth) →
    bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastDeltaFanBlockLeft blockWidth)
      = bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastDeltaFanBlockRight blockWidth) →
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidSigmaPastDeltaFanBlockLeft blockWidth)
      (bunchedBimonoidSigmaPastDeltaFanBlockRight blockWidth) :=
  fun _ _ _ _ _ _ _ => bunchedBimonoidSigmaPastDeltaFanBlockThreadConv blockWidth

/-! # =========================================================================================
    # THE FLAGSHIP WIDTH-6 FIRE — the full premise vector, matrix equality included
    # =========================================================================================
-/

/-- ★★ **The width-6 matrix equality as a FULL record equality** — assembled from the r27 kernel-`decide`
entries agreement through the shipped `bunchedBimonoidMatEqOfEntries` (rows `2 = 2`, cols `7 = 7` reduce on the
closed pair; no wide `rfl` on the record). -/
theorem bunchedBimonoidBlockThreadingPairMatrixEqAtWidthSix :
    bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockLeft 6)
      = bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockRight 6) :=
  bunchedBimonoidMatEqOfEntries _ _ rfl rfl bunchedBimonoidSigmaPastMuFoldBlockSoundAtWidthSix

/-- ★★★ **THE FLAGSHIP POSITIVE FIRE (width 6, far above natural)** — the corrected target's FULL premise
vector (all six structural guards AND the matrix equality) is machine-checked at the width-6 mu-side pair, and
the conclusion CONV is the r29 delivery: the corrected star's instance at the pair is discharged end-to-end.
The corrected target is non-vacuous on genuinely wide data. -/
theorem bunchedBimonoidCorrectedStarFiredPositiveAtWidthSix :
    (bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidSigmaPastMuFoldBlockLeft 6) = true
        ∧ bunchedBimonoidCellUsesOnlyAdditive (bunchedBimonoidSigmaPastMuFoldBlockRight 6) = true
        ∧ bunchedBimonoidCellWellTyped (bunchedBimonoidSigmaPastMuFoldBlockLeft 6)
        ∧ bunchedBimonoidCellWellTyped (bunchedBimonoidSigmaPastMuFoldBlockRight 6)
        ∧ bunchedBimonoidCellGensCanonical (bunchedBimonoidSigmaPastMuFoldBlockLeft 6)
        ∧ bunchedBimonoidCellGensCanonical (bunchedBimonoidSigmaPastMuFoldBlockRight 6)
        ∧ bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockLeft 6)
            = bunchedBimonoidEvalCell (bunchedBimonoidSigmaPastMuFoldBlockRight 6))
      ∧ SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
          (bunchedBimonoidSigmaPastMuFoldBlockLeft 6) (bunchedBimonoidSigmaPastMuFoldBlockRight 6) :=
  ⟨⟨(bunchedBimonoidBlockThreadingPairSatisfiesGuardsMu 6).1,
      (bunchedBimonoidBlockThreadingPairSatisfiesGuardsMu 6).2.1,
      (bunchedBimonoidBlockThreadingPairSatisfiesGuardsMu 6).2.2.1,
      (bunchedBimonoidBlockThreadingPairSatisfiesGuardsMu 6).2.2.2.1,
      (bunchedBimonoidBlockThreadingPairSatisfiesGuardsMu 6).2.2.2.2.1,
      (bunchedBimonoidBlockThreadingPairSatisfiesGuardsMu 6).2.2.2.2.2,
      bunchedBimonoidBlockThreadingPairMatrixEqAtWidthSix⟩,
    bunchedBimonoidSigmaPastMuFoldBlockThreadConv 6⟩

/-! # =========================================================================================
    # THE NEGATIVE CONTROL — mu vs delta: all structural guards pass, the matrices differ
    # =========================================================================================
-/

/-- The mu / delta matrices DIFFER (`rows` clash `1 != 2`) — the equal-matrices premise is the separating
guard, exactly as completeness demands. -/
theorem bunchedBimonoidMuDeltaMatricesDiffer :
    bunchedBimonoidEvalCell bunchedBimonoidAddMuGen ≠ bunchedBimonoidEvalCell bunchedBimonoidAddDeltaGen :=
  fun hmatEq => Nat.noConfusion (Nat.succ.inj (congrArg (fun matrix => matrix.rows) hmatEq))

/-- ★★ **THE NEGATIVE CONTROL** — `mu_a` vs `delta_a` pass every STRUCTURAL guard (additive, well-typed,
canonical) yet their matrices differ, so the corrected star's premise vector is unsatisfiable at the pair: the
corrected target does not over-identify structurally-honest but semantically-distinct cells. -/
theorem bunchedBimonoidCorrectedStarNegativeControlMuDelta :
    (bunchedBimonoidCellUsesOnlyAdditive bunchedBimonoidAddMuGen = true
        ∧ bunchedBimonoidCellUsesOnlyAdditive bunchedBimonoidAddDeltaGen = true
        ∧ bunchedBimonoidCellWellTyped bunchedBimonoidAddMuGen
        ∧ bunchedBimonoidCellWellTyped bunchedBimonoidAddDeltaGen
        ∧ bunchedBimonoidCellGensCanonical bunchedBimonoidAddMuGen
        ∧ bunchedBimonoidCellGensCanonical bunchedBimonoidAddDeltaGen)
      ∧ bunchedBimonoidEvalCell bunchedBimonoidAddMuGen
          ≠ bunchedBimonoidEvalCell bunchedBimonoidAddDeltaGen :=
  ⟨⟨rfl, rfl, bunchedBimonoidAddMuGenWellTyped, bunchedBimonoidAddDeltaGenWellTyped,
      bunchedBimonoidAddMuGenCanonical, bunchedBimonoidAddDeltaGenCanonical⟩,
    bunchedBimonoidMuDeltaMatricesDiffer⟩

/-! # =========================================================================================
    # THE MARKERS
    # =========================================================================================
-/

/-- ★★★ **ESTABLISHED — the corrected target is FIRED on concrete data.**  `= true` records the positive
family fire (all six structural guards at EVERY width, both colours, with the corrected star's implication a
theorem at the family), the FLAGSHIP width-6 fire with the full premise vector including the record-level
matrix equality, and the mu/delta negative control (structural guards pass, matrices differ, premises
unsatisfiable).  The corrected dim-2 canonical-gens target is non-vacuous and non-trivial on the lane's own
data; its owner `fxBunchedBimonoid_dimTwoCanonicalGensStarStillOpen` stays `= false` (the general statement
remains open — the retract bill stands). -/
def fxBunchedBimonoid_correctedStarFiredOnConcreteData : Bool := true

end FX1Poly.Polygraph.Omega
