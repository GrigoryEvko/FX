import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordCanonicity
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidPermMatrixExtractorGates

/-! # Polygraph/Omega/WalkingBunchedBimonoidCanonicalWordMatrixToRecComb — the matrix→recComb leg of
`CoxeterWordUnique`: `evalCell (permWord w1) = evalCell (permWord w2) -> recComb (W-1) w1 = recComb (W-1) w2`
(WP-PROP r18, T3 — unblocked by the r18 T1 canonicity)

★ **THE r18 T3 ATOM — the whole matrix-determined recComb leg, now shipped.**  r11 delivered the matrix→permutation
reduction (`evalCell (permWord w1) = evalCell (permWord w2) -> permOfWord w1 = permOfWord w2`, via the generic
extractor `bunchedBimonoidPermWordExtractor` + the injective read-off `bunchedBimonoidPermMatrixInjective`), and named
the "portable `combCanonicity` re-derivation turning `permOfWord`-equality into `recComb`-equality" as the outstanding
residual (`WalkingBunchedBimonoidPermMatrixExtractor` r11 ledger).  The r18 T1 file shipped exactly that residual
(`bunchedBimonoidCombCanonicity`).  This file COMPOSES the two into the full leg:

  `evalCell (permWord w1 W) = evalCell (permWord w2 W)`  (a MATRIX equality)
    -->  `permMatrixOf W (permOfWord w1 W) = permMatrixOf W (permOfWord w2 W)`   (extractor, both legs)
    -->  `permOfWord w1 W = permOfWord w2 W`                                     (permMatrixInjective + entry-bound)
    -->  `recComb (W-1) w1 = recComb (W-1) w2`                                   (combCanonicity)

for every word valid at width `W = generatorCount + 1`.  This is the determinism the star's `CoxeterWordUnique` needs
on the MATRIX side (the semantic decision), now at generic width, PURE.  ZERO CONV: no cell / `SaturatedConvOver`
layer is touched — the `recCombConv`-over-cells CONV lift stays gated on the r18 T2 whisker-coherence wall
(`WalkingBunchedBimonoidWhiskerOneCellCoherenceWall`), which this leg does NOT touch.  The star does NOT flip: this is
a LEG (the matrix side), not the full `CoxeterWordUnique` = matrix-leg + CONV-mirror; every star / residual marker
stays byte-intact.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

set_option maxHeartbeats 4000000

/-! ## T3.bridge — `positionsValid width w` implies `mentionsOnlyBelow (width - 1) w` -/

private theorem bunchedBimonoidNatBleOfLeMatrix : (lower upper : Nat) → lower ≤ upper → Nat.ble lower upper = true
  | 0, _, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | lower + 1, upper + 1, h => bunchedBimonoidNatBleOfLeMatrix lower upper (Nat.le_of_succ_le_succ h)

private theorem bunchedBimonoidNatBltOfLtMatrix (lower upper : Nat) (h : lower < upper) : Nat.blt lower upper = true :=
  bunchedBimonoidNatBleOfLeMatrix (lower + 1) upper h

private theorem bunchedBimonoidNatLePredMatrix : (lower top : Nat) → lower + 1 ≤ top → lower ≤ top - 1
  | lower, 0, h => absurd h (Nat.not_succ_le_zero lower)
  | _, _ + 1, h => Nat.le_of_succ_le_succ h

/-- ★ **Validity implies the range certificate.**  A word valid for the extractor at `width` (`k + 2 ≤ width` per
letter) mentions only positions `< width - 1` — the `mentionsOnlyBelow (width - 1)` certificate `combCanonicity`
consumes.  Structural on the word, reusing the shipped `bunchedBimonoidPositionsValidHead` / `...Tail`. -/
theorem bunchedBimonoidMentionsOnlyBelowOfPositionsValid :
    (width : Nat) → (word : List Nat) → bunchedBimonoidPositionsValid width word = true →
    bunchedBimonoidMentionsOnlyBelow (width - 1) word = true
  | _, [], _ => rfl
  | width, letter :: rest, hvalid => by
      have hLetter : letter + 1 < width := bunchedBimonoidPositionsValidHead width letter rest hvalid
      have hrest : bunchedBimonoidPositionsValid width rest = true :=
        bunchedBimonoidPositionsValidTail width letter rest hvalid
      have hLetterLt : letter < width - 1 := bunchedBimonoidNatLePredMatrix (letter + 1) width hLetter
      show (Nat.blt letter (width - 1) && bunchedBimonoidMentionsOnlyBelow (width - 1) rest) = true
      rw [bunchedBimonoidNatBltOfLtMatrix letter (width - 1) hLetterLt]
      exact bunchedBimonoidMentionsOnlyBelowOfPositionsValid width rest hrest

/-! ## T3 — the matrix→recComb leg -/

/-- ★★ **The matrix determines the recursive-comb staircase.**  Two words valid at width `generatorCount + 1` whose
`permWord` cells evaluate to the SAME `Mat(N)` map have the SAME recursive-comb staircase.  Composes the generic
extractor + injective read-off (matrix → `permOfWord`-equality) with the r18 T1 canonicity
(`permOfWord`-equality → `recComb`-equality).  The determinism the star's `CoxeterWordUnique` needs on the matrix
side, at generic width. -/
theorem bunchedBimonoidRecCombEqOfEvalEq (generatorCount : Nat) (word1 word2 : List Nat)
    (valid1 : bunchedBimonoidPositionsValid (generatorCount + 1) word1 = true)
    (valid2 : bunchedBimonoidPositionsValid (generatorCount + 1) word2 = true)
    (evalEq : (bunchedBimonoidEvalCell (bunchedBimonoidPermWord word1 (generatorCount + 1)) : BunchedBimonoidMat)
      = bunchedBimonoidEvalCell (bunchedBimonoidPermWord word2 (generatorCount + 1))) :
    bunchedBimonoidRecComb generatorCount word1 = bunchedBimonoidRecComb generatorCount word2 := by
  have extract1 := bunchedBimonoidPermWordExtractor word1 (generatorCount + 1) valid1
  have extract2 := bunchedBimonoidPermWordExtractor word2 (generatorCount + 1) valid2
  have matrixEq : bunchedBimonoidPermMatrixOf (generatorCount + 1)
        (bunchedBimonoidPermOfWord word1 (generatorCount + 1))
      = bunchedBimonoidPermMatrixOf (generatorCount + 1)
        (bunchedBimonoidPermOfWord word2 (generatorCount + 1)) := by
    rw [← extract1, ← extract2]; exact evalEq
  have permEq : bunchedBimonoidPermOfWord word1 (generatorCount + 1)
      = bunchedBimonoidPermOfWord word2 (generatorCount + 1) :=
    bunchedBimonoidPermMatrixInjective (generatorCount + 1)
      (bunchedBimonoidPermOfWord word1 (generatorCount + 1))
      (bunchedBimonoidPermOfWord word2 (generatorCount + 1))
      (bunchedBimonoidPermOfWordLength word1 (generatorCount + 1))
      (bunchedBimonoidPermOfWordLength word2 (generatorCount + 1))
      (fun index hindex => bunchedBimonoidPermOfWordEntriesBelow word1 (generatorCount + 1) index hindex)
      matrixEq
  have mentions1 : bunchedBimonoidMentionsOnlyBelow generatorCount word1 = true :=
    bunchedBimonoidMentionsOnlyBelowOfPositionsValid (generatorCount + 1) word1 valid1
  have mentions2 : bunchedBimonoidMentionsOnlyBelow generatorCount word2 = true :=
    bunchedBimonoidMentionsOnlyBelowOfPositionsValid (generatorCount + 1) word2 valid2
  exact bunchedBimonoidCombCanonicity generatorCount word1 word2 mentions1 mentions2 permEq

/-! ## T3 — non-vacuity: the braid pair fires the whole matrix→recComb leg -/

/-- The r9 braid pair shares its `permWord` matrix — both `evalCell (permWord _ 3)` reads are the width-3 reversal
`permMatrixOf 3 [2,1,0]` (via the shipped extractor pins + the shared one-line permutation). -/
theorem bunchedBimonoidBraidPairEvalShared :
    (bunchedBimonoidEvalCell (bunchedBimonoidPermWord [0, 1, 0] 3) : BunchedBimonoidMat)
      = bunchedBimonoidEvalCell (bunchedBimonoidPermWord [1, 0, 1] 3) :=
  bunchedBimonoidExtractorBraidThree.trans
    ((congrArg (bunchedBimonoidPermMatrixOf 3) bunchedBimonoidBraidPairPermShared).trans
      bunchedBimonoidExtractorBraidThreeOther.symm)

/-- ★★ **Non-vacuity — the whole matrix→recComb leg fires on the r9 braid pair.**  From the matrix equality
`evalCell (permWord [0,1,0] 3) = evalCell (permWord [1,0,1] 3)` alone, the leg derives
`recComb 2 [0,1,0] = recComb 2 [1,0,1]` — the width-3 Yang–Baxter braid pair decided from the semantic (matrix)
side. -/
theorem bunchedBimonoidRecCombEqOfEvalEq_braidPair :
    bunchedBimonoidRecComb 2 [0, 1, 0] = bunchedBimonoidRecComb 2 [1, 0, 1] :=
  bunchedBimonoidRecCombEqOfEvalEq 2 [0, 1, 0] [1, 0, 1] rfl rfl bunchedBimonoidBraidPairEvalShared

/-! ## The r18 T3 honesty marker -/

/-- ★★★ **ESTABLISHED (r18 T3) — the matrix→recComb leg of `CoxeterWordUnique` is SHIPPED and zero-axiom.**  `= true`
records `bunchedBimonoidRecCombEqOfEvalEq`: `evalCell (permWord w1) = evalCell (permWord w2) -> recComb (W-1) w1 =
recComb (W-1) w2` for words valid at width `W`, composing the r11 generic extractor + injective read-off (matrix ->
`permOfWord`-equality) with the r18 T1 canonicity (`permOfWord`-equality -> `recComb`-equality), through the
`positionsValid -> mentionsOnlyBelow` bridge.  This closes the exact residual the r11 ledger named ("the portable
`combCanonicity` re-derivation turning `permOfWord`-equality into `recComb`-equality").  Non-vacuous: it fires on the
r9 braid pair (`bunchedBimonoidRecCombEqOfEvalEq_braidPair`), deciding `recComb 2 [0,1,0] = recComb 2 [1,0,1]` from the
matrix side alone.  PURE `List Nat` + `Mat(N)`, ZERO CONV — the `recCombConv`-over-cells lift stays gated on the r18 T2
whisker-coherence wall.  The four star owners keep their name and `= false` value byte-intact (cross-file, not
edited); NO fabricated star flip.  Zero-axiom (per-decl `#assert_no_axioms` in the twin); STRUCTURAL only. -/
def fxBunchedBimonoid_hasMatrixToRecCombLeg : Bool := true

end FX1Poly.Polygraph.Omega
