import FX1Poly.Tier0.Mode.AdjunctionTriangleObstruction
import FX1Poly.Tier0.Mode.FreeTwoCellStrongNormalization

/-! # FX1Poly/Tier0/Mode/AdjunctionSaturatedNormalization
    — the KB-completed walking-adjunction rewrite terminates UNCONDITIONALLY (structural floor discharged, fib-3 dim-2)

`AdjunctionTriangleObstruction` ships the Knuth–Bendix completion of the walking-adjunction word problem: the two
bare triangles (`leftBareSnake` / `rightBareSnake`), their snake-prefix completions, the `vcompAssoc` critical
pairs (both JOIN), and the `generatorCount` MONOVARIANT (every saturated step is generator-count non-increasing).
What that file's termination docstring left as prose — and slightly overclaimed as "mode-8's already-shipped
structural SN" — this file makes a RIGOROUS THEOREM, and corrects the dependency:

  ★ **Every generator-count-PRESERVING saturated step is already a free structural `TwoCellStep`.**

`generatorCountPreserving_isStructural` (left and right): a saturated step whose source and target have equal
`generatorCount` is one of the free strict-2-category laws (`ofFree`) — the two saturating completions
(`bareSnake` drops 2→0, `snakePrefix` drops `2 + rest → rest`) STRICTLY decrease the count, so they cannot be
count-preserving.  Equivalently: the KB completion adds to the free rewrite ONLY generator-count-strictly-
decreasing rules.

The consequence (`adjunction{Left,Right}Saturated_isStronglyNormalizing`): the saturated rewrite is strongly
normalizing — **UNCONDITIONALLY**, now that the structural floor `TwoCellStep` SN is proven
(`FreeTwoCellStrongNormalization.twoCellStep_isStronglyNormalizing`, via a left-heavy polynomial weight; the naive
`size` fails — `vcompAssoc` preserves it and `whiskerVcomp` increases it).  The proof is a clean lexicographic
descent on `(generatorCount, structural-accessibility)`: a saturated step either strictly drops `generatorCount`
(recurse on the fuel bound) or preserves it and is therefore structural (recurse on the structural `Acc`, fed by
the now-discharged floor).  So the walking-adjunction completion adds NO termination obligation beyond the
structural floor, and that floor is itself closed — the saturated system is SN outright.  (The broader 3-polygraph
CONVERGENCE flag `fxMode_hasConvergentThreeCellSystem` still awaits its confluence half: joining the
interchange/Godement critical pair, then Newman's lemma.)

## Zero-axiom

Structural induction on the saturated step (`generatorCountPreserving_isStructural`) + a fuel-bounded
lexicographic `Acc` descent (`isStronglyNormalizing`), both over `Nat` order (`natAddRightCancel` — the
propext-free right-cancellation proved here, since core's `Nat.add_right_cancel` routes through `propext` —
`Nat.succ.inj`, `Nat.add_assoc`, `Nat.zero_add`, `Nat.le_of_lt_succ`, `Nat.lt_of_lt_of_le`, `Nat.lt_or_eq_of_le`,
`Nat.not_lt_zero`, `Nat.lt_succ_self`, `Nat.le_trans`, `Nat.le_of_eq`) and `Acc.rec`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`, `decide`.  Per-declaration audit-gated in
`FX1PolyAudit/`. -/

namespace FX1Poly.Tier0

/-- Right-cancellation for `Nat` addition, propext-free.  Lean core's `Nat.add_right_cancel` is proved through
a `propext`-using route; this structural-induction version (on the cancelled summand) keeps the file zero-axiom.
Used to strip the shared right factor `+ cellBeta.generatorCount` in the `vcomp` congruence arm and to expose the
`2 = 0` contradiction in the bare-snake / snake-prefix arms. -/
theorem natAddRightCancel {leftSummand rightSummand : Nat} :
    {cancelled : Nat} → leftSummand + cancelled = rightSummand + cancelled →
      leftSummand = rightSummand := by
  intro cancelled
  induction cancelled with
  | zero => intro equalSums; exact equalSums
  | succ cancelled inductionHypothesis =>
      intro equalSums; exact inductionHypothesis (Nat.succ.inj equalSums)

/-! ## ★ The KB completion adds only count-decreasing rules: count-preserving saturated ⟹ structural -/

/-- ★ **A generator-count-preserving LEFT-saturated step is a free structural step.**  Case the saturated step:
`ofFree` IS already a `TwoCellStep`; the bare LEFT triangle drops `2 → 0` and the snake-prefix drops
`1 + (1 + rest) → rest`, both contradicting count preservation; the left-factor congruence cancels the shared
right factor's count (`Nat.add_right_cancel`) and recurses.  So the only count-preserving left-saturated steps
are the free strict-2-category laws — the KB completion's extra rules are all strictly count-decreasing. -/
theorem AdjunctionLeftSaturatedStep.generatorCountPreserving_isStructural
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (step : AdjunctionLeftSaturatedStep cellA cellB) :
    cellA.generatorCount = cellB.generatorCount →
      TwoCellStep adjunctionModeSignature cellA cellB := by
  induction step with
  | ofFree freeStep => exact fun _ => freeStep
  | leftBareSnake =>
      intro countPreserved
      exact absurd
        (adjunctionSeedLeftSnake_generatorCount.symm.trans
          (countPreserved.trans leftIdentityCell_generatorCount))
        (fun twoEqualsZero => Nat.noConfusion twoEqualsZero)
  | leftSnakePrefix rest =>
      intro countPreserved
      exact absurd
        (natAddRightCancel
          ((Nat.add_assoc 1 1 rest.generatorCount).trans
            (countPreserved.trans (Nat.zero_add rest.generatorCount).symm)))
        (fun twoEqualsZero => Nat.noConfusion twoEqualsZero)
  | vcompCongrLeft cellBeta _ structuralOfSub =>
      intro countPreserved
      exact TwoCellStep.vcompCongrLeft cellBeta (structuralOfSub (natAddRightCancel countPreserved))

/-- ★ **A generator-count-preserving RIGHT-saturated step is a free structural step** — the dual of the left
characterization, same shape (`ofFree` structural; bare right triangle and right snake-prefix strictly drop the
count; left-factor congruence cancels and recurses). -/
theorem AdjunctionRightSaturatedStep.generatorCountPreserving_isStructural
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (step : AdjunctionRightSaturatedStep cellA cellB) :
    cellA.generatorCount = cellB.generatorCount →
      TwoCellStep adjunctionModeSignature cellA cellB := by
  induction step with
  | ofFree freeStep => exact fun _ => freeStep
  | rightBareSnake =>
      intro countPreserved
      exact absurd
        (adjunctionSeedRightSnake_generatorCount.symm.trans
          (countPreserved.trans
            (rfl : (RawTwoCellExpr.id (signature := adjunctionModeSignature)
              (singletonModalityPath AdjunctionModality.right)).generatorCount = 0)))
        (fun twoEqualsZero => Nat.noConfusion twoEqualsZero)
  | rightSnakePrefix rest =>
      intro countPreserved
      exact absurd
        (natAddRightCancel
          ((Nat.add_assoc 1 1 rest.generatorCount).trans
            (countPreserved.trans (Nat.zero_add rest.generatorCount).symm)))
        (fun twoEqualsZero => Nat.noConfusion twoEqualsZero)
  | vcompCongrLeft cellBeta _ structuralOfSub =>
      intro countPreserved
      exact TwoCellStep.vcompCongrLeft cellBeta (structuralOfSub (natAddRightCancel countPreserved))

/-! ## ★ The saturated rewrite is strongly normalizing RELATIVE TO the structural floor -/

/-- ★ **The LEFT KB-completed walking-adjunction rewrite is strongly normalizing — UNCONDITIONALLY.**
The structural floor `TwoCellStep` SN is now proven (`twoCellStep_isStronglyNormalizing`), so the KB-completed
left-saturated rewrite is strongly normalizing outright.  Lexicographic descent on `(generatorCount,
structural-Acc)`: a fuel bound on
`generatorCount` (strictly dropped by the saturating completions, so the outer fuel induction handles them) wraps
an induction on the structural accessibility (the count-preserving steps are structural by
`generatorCountPreserving_isStructural`, so the inner `Acc` handles them).  The walking-adjunction completion adds
NO termination obligation beyond the structural floor. -/
theorem adjunctionLeftSaturated_isStronglyNormalizing
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Acc (fun reduct expr => AdjunctionLeftSaturatedStep expr reduct) cell := by
  have fueled :
      ∀ (fuel : Nat) {sourceMode targetMode : AdjunctionMode}
        {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
        (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath),
        cell.generatorCount < fuel →
          Acc (fun reduct expr => AdjunctionLeftSaturatedStep expr reduct) cell := by
    intro fuel
    induction fuel with
    | zero => intro _ _ _ _ _ countBelow; exact absurd countBelow (Nat.not_lt_zero _)
    | succ fuel outerIH =>
        have inner :
            ∀ {sourceMode targetMode : AdjunctionMode}
              {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
              (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath),
              Acc (fun reduct expr => TwoCellStep adjunctionModeSignature expr reduct) cell →
                cell.generatorCount ≤ fuel →
                  Acc (fun reduct expr => AdjunctionLeftSaturatedStep expr reduct) cell := by
          intro _ _ _ _ _ structAcc
          induction structAcc with
          | intro current _ innerIH =>
              intro boundedByFuel
              refine Acc.intro current (fun reduct saturatedStep => ?_)
              rcases Nat.lt_or_eq_of_le saturatedStep.generatorCount_le with countDrops | countEqual
              · exact outerIH reduct (Nat.lt_of_lt_of_le countDrops boundedByFuel)
              · exact innerIH reduct
                  (saturatedStep.generatorCountPreserving_isStructural countEqual.symm)
                  (Nat.le_trans (Nat.le_of_eq countEqual) boundedByFuel)
        intro _ _ _ _ cell countBelow
        exact inner cell (twoCellStep_isStronglyNormalizing cell) (Nat.le_of_lt_succ countBelow)
  exact fueled (cell.generatorCount + 1) cell (Nat.lt_succ_self _)

/-- ★ **The RIGHT KB-completed walking-adjunction rewrite is strongly normalizing — UNCONDITIONALLY** —
the dual of the left SN, the same lexicographic descent fed by the now-proven structural floor. -/
theorem adjunctionRightSaturated_isStronglyNormalizing
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Acc (fun reduct expr => AdjunctionRightSaturatedStep expr reduct) cell := by
  have fueled :
      ∀ (fuel : Nat) {sourceMode targetMode : AdjunctionMode}
        {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
        (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath),
        cell.generatorCount < fuel →
          Acc (fun reduct expr => AdjunctionRightSaturatedStep expr reduct) cell := by
    intro fuel
    induction fuel with
    | zero => intro _ _ _ _ _ countBelow; exact absurd countBelow (Nat.not_lt_zero _)
    | succ fuel outerIH =>
        have inner :
            ∀ {sourceMode targetMode : AdjunctionMode}
              {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
              (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath),
              Acc (fun reduct expr => TwoCellStep adjunctionModeSignature expr reduct) cell →
                cell.generatorCount ≤ fuel →
                  Acc (fun reduct expr => AdjunctionRightSaturatedStep expr reduct) cell := by
          intro _ _ _ _ _ structAcc
          induction structAcc with
          | intro current _ innerIH =>
              intro boundedByFuel
              refine Acc.intro current (fun reduct saturatedStep => ?_)
              rcases Nat.lt_or_eq_of_le saturatedStep.generatorCount_le with countDrops | countEqual
              · exact outerIH reduct (Nat.lt_of_lt_of_le countDrops boundedByFuel)
              · exact innerIH reduct
                  (saturatedStep.generatorCountPreserving_isStructural countEqual.symm)
                  (Nat.le_trans (Nat.le_of_eq countEqual) boundedByFuel)
        intro _ _ _ _ cell countBelow
        exact inner cell (twoCellStep_isStronglyNormalizing cell) (Nat.le_of_lt_succ countBelow)
  exact fueled (cell.generatorCount + 1) cell (Nat.lt_succ_self _)

end FX1Poly.Tier0
