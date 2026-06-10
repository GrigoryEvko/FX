import FX1Poly.NbE.DecisionComplexity
import FX1Poly.Universe.LevelExprSimplify

/-! # FX1Poly/Universe/LevelExprComplexity
   — the STRICT-COMPLEXITY witness for the universe-level equivalence decider (M22-A11)

`LevelExprSimplify` ships the shadow comparison counters (`*Steps`, mirror-faithful by
construction) and the per-phase bounds, culminating in `decideDenoteEquivSteps_le_size`:
deciding `denoteEquiv e1 e2` costs at most `size e1² + 2·size e1 + size e2² + 2·size e2`
comparisons.  This file packages that bound as the first `DecisionComplexity` instance — the
generic §11.8.7 STRICT-COMPLEXITY hook — closing the "decidable but EXP-tower" loophole for the
universe-level decider used throughout universe-formation typing.

## The honest bound is QUADRATIC, not `O(n·log n)`

The sort inside `canonicalizeVarOffsets` is an INSERTION sort, so the genuine worst case is
quadratic (`sortByVariableSteps_le : ≤ length²`, realized by the reversed-input smokes).  The
witness records degree 2 with constant 4: `stepCount l r ≤ 4 · (size l² + size r²) + 4`.  An
`O(n·log n)` witness would require swapping the insertion sort for a merge sort — the per-phase
counters are already factored so only the sort brick changes; that upgrade is deliberately NOT
claimed here.

## Why this is not a `StrictNormalizer` instance

`StrictNormalizer` (audit-A4) is term-normalizer-shaped: its `normalizer` field demands an
`FX1Poly.NbE.Normalizer`, a `RawTerm scope → RawTerm scope` contract.  The level decider is a
decision procedure, not a term normalizer; it instantiates the generic sibling
`DecisionComplexity` instead.  `StrictNormalizer` remains the hook for the term-layer normalizer
witness (SN-145).

## Zero-axiom verification

The arithmetic is structural `Nat` reasoning only — `Nat.add_assoc`/`add_comm`/`le_trans`/
`mul_le_mul_left`/`succ_mul`/`pow_succ` term applications, `decide` on closed base cases; no
`omega`, no `simp`.  Numeral/`succ` conversions go through term-level lemma application (the
elaborator's definitional literal unification), never `rw` pattern matching.  Audit-gated in
`AuditUniverse.lean`.
-/

namespace FX1Poly.Universe

/-- `s + s ≤ s² + 2` — the linear term of the per-operand cost is absorbed by the square plus a
constant.  Base cases `0`/`1` close by evaluation; from `s ≥ 2` the square dominates the double
(`s·2 ≤ s·s` by multiplication monotonicity). -/
theorem addSelf_le_mulSelf_add_two : ∀ (value : Nat), value + value ≤ value * value + 2
  | 0 => by decide
  | 1 => by decide
  | base + 2 => by
      have hTwoLe : 2 ≤ base + 2 := Nat.le_add_left 2 base
      have hDoubleLeSquare : (base + 2) * 2 ≤ (base + 2) * (base + 2) :=
        Nat.mul_le_mul_left (base + 2) hTwoLe
      have hDoubleUnfold : (base + 2) * 2 = (base + 2) + (base + 2) :=
        (Nat.mul_succ (base + 2) 1).trans
          (congrArg (· + (base + 2)) (Nat.mul_one (base + 2)))
      exact Nat.le_trans
        (Nat.le_trans (Nat.le_of_eq hDoubleUnfold.symm) hDoubleLeSquare)
        (Nat.le_add_right ((base + 2) * (base + 2)) 2)

/-- Per-operand absorption: one side's full canonicalization cost `s² + 2s` is bounded by two
squares plus a constant, `(s² + s²) + 2`. -/
theorem mulSelf_add_self_add_self_le_doubleSquare (value : Nat) :
    value * value + value + value ≤ (value * value + value * value) + 2 :=
  Nat.le_trans
    (Nat.le_of_eq (Nat.add_assoc (value * value) value value))
    (Nat.le_trans
      (Nat.add_le_add_left (addSelf_le_mulSelf_add_two value) (value * value))
      (Nat.le_of_eq (Nat.add_assoc (value * value) (value * value) 2).symm))

/-- `v ^ 1 = v` rebuilt from the propext-FREE pieces `Nat.pow_succ`/`Nat.pow_zero`/`Nat.one_mul` —
core's own `Nat.pow_one` depends on `propext` and is banned here. -/
theorem pow_one_eq_self (value : Nat) : value ^ 1 = value :=
  (Nat.pow_succ value 0).trans
    ((congrArg (· * value) (Nat.pow_zero value)).trans (Nat.one_mul value))

/-- Four-fold sum as a numeral multiple: `(t + t) + (t + t) = 4·t`.  Unfolds `4·t` one successor
at a time through term-level `Nat.succ_mul` applications (the elaborator's definitional literal
unification handles `4 ≡ succ 3`; `rw` pattern matching cannot). -/
theorem addSelf_add_addSelf_eq_four_mul (total : Nat) :
    (total + total) + (total + total) = 4 * total := by
  have hTwo : 2 * total = total + total :=
    (Nat.succ_mul 1 total).trans (congrArg (· + total) (Nat.one_mul total))
  have hThree : 3 * total = (total + total) + total :=
    (Nat.succ_mul 2 total).trans (congrArg (· + total) hTwo)
  have hFour : 4 * total = ((total + total) + total) + total :=
    (Nat.succ_mul 3 total).trans (congrArg (· + total) hThree)
  exact ((hFour.trans (Nat.add_assoc (total + total) total total)).symm)

/-- Constant shuffle: `(x + 2) + (y + 2) = (x + y) + 4` — pure `add_assoc`/`add_comm`
rebracketing (the final `2 + 2 ≡ 4` is definitional). -/
theorem add_two_add_add_two_eq_add_four (doubledLeft doubledRight : Nat) :
    (doubledLeft + 2) + (doubledRight + 2) = (doubledLeft + doubledRight) + 4 :=
  (Nat.add_assoc doubledLeft 2 (doubledRight + 2)).trans
    ((congrArg (doubledLeft + ·)
        ((Nat.add_comm 2 (doubledRight + 2)).trans
          (Nat.add_assoc doubledRight 2 2))).trans
      (Nat.add_assoc doubledLeft doubledRight 4).symm)

/-- **The polynomial-shape certificate for the level decider's cost (M22-A11 headline).**
Deciding `denoteEquiv e1 e2` costs at most `4 · (size e1² + size e2²) + 4` comparisons — the
shipped per-operand bound `decideDenoteEquivSteps_le_size` massaged into the `DecisionComplexity`
polynomial form.  Degree 2 is HONEST: the insertion sort is genuinely quadratic (see the
reversed-input worst-case smokes in `LevelExprSimplify`). -/
theorem LevelExpr.decideDenoteEquivSteps_isPolynomial (e1 e2 : LevelExpr) :
    LevelExpr.decideDenoteEquivSteps e1 e2 ≤
      4 * (e1.size ^ 2 + e2.size ^ 2) + 4 := by
  have hPowLeft : e1.size ^ 2 = e1.size * e1.size :=
    (Nat.pow_succ e1.size 1).trans (congrArg (· * e1.size) (pow_one_eq_self e1.size))
  have hPowRight : e2.size ^ 2 = e2.size * e2.size :=
    (Nat.pow_succ e2.size 1).trans (congrArg (· * e2.size) (pow_one_eq_self e2.size))
  rw [hPowLeft, hPowRight]
  have hShipped := LevelExpr.decideDenoteEquivSteps_le_size e1 e2
  have hSum :
      e1.size * e1.size + e1.size + e1.size + (e2.size * e2.size + e2.size + e2.size) ≤
        ((e1.size * e1.size + e1.size * e1.size) + 2) +
          ((e2.size * e2.size + e2.size * e2.size) + 2) :=
    Nat.add_le_add
      (mulSelf_add_self_add_self_le_doubleSquare e1.size)
      (mulSelf_add_self_add_self_le_doubleSquare e2.size)
  have hSquaresLe :
      (e1.size * e1.size + e1.size * e1.size) +
          (e2.size * e2.size + e2.size * e2.size) ≤
        4 * (e1.size * e1.size + e2.size * e2.size) :=
    Nat.le_trans
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.le_add_right (e1.size * e1.size) (e2.size * e2.size))
          (Nat.le_add_right (e1.size * e1.size) (e2.size * e2.size)))
        (Nat.add_le_add
          (Nat.le_add_left (e2.size * e2.size) (e1.size * e1.size))
          (Nat.le_add_left (e2.size * e2.size) (e1.size * e1.size))))
      (Nat.le_of_eq (addSelf_add_addSelf_eq_four_mul (e1.size * e1.size + e2.size * e2.size)))
  exact Nat.le_trans hShipped
    (Nat.le_trans hSum
      (Nat.le_trans
        (Nat.le_of_eq
          (add_two_add_add_two_eq_add_four (e1.size * e1.size + e1.size * e1.size)
            (e2.size * e2.size + e2.size * e2.size)))
        (Nat.add_le_add_right hSquaresLe 4)))

/-- **The first `DecisionComplexity` instance (M22-A11 / the M19 STRICT-COMPLEXITY hook fires).**
The universe-level equivalence decider on the predicative fragment, with its mirror-faithful
comparison counter and the machine-checked quadratic bound `≤ 4·(size² + size²) + 4`.  The
counter's faithfulness is by construction: `decideDenoteEquivSteps` mirrors
`decideDenoteEquiv`'s canonicalize-both-then-compare control flow exactly (see its definition
site); the trailing canonical-form equality test is a strictly-lower-order linear pass. -/
def levelDenoteEquivDecisionComplexity :
    FX1Poly.NbE.DecisionComplexity
      (fun (level : LevelExpr) => LevelExpr.isPredicative level = true)
      LevelExpr.denoteEquiv where
  decider left right hLeftPredicative hRightPredicative :=
    LevelExpr.decideDenoteEquiv left right hLeftPredicative hRightPredicative
  inputSize := LevelExpr.size
  stepCount := LevelExpr.decideDenoteEquivSteps
  polynomialDegree := 2
  polynomialConstant := 4
  stepCount_isPolynomial left right :=
    LevelExpr.decideDenoteEquivSteps_isPolynomial left right

/-- Non-vacuity: the instance's counter computes a concrete non-zero comparison count on a small
fixture (`lmax (lvar 1) (lvar 0)` vs `lvar 0` costs exactly 5 comparisons), closed by full
evaluation. -/
theorem levelDenoteEquivDecisionComplexity_stepCount_smoke :
    levelDenoteEquivDecisionComplexity.stepCount
      (.lmax (.lvar 1) (.lvar 0)) (.lvar 0) = 5 := rfl

/-- Non-vacuity at a larger fixture: a 5-node vs 3-node operand pair costs exactly 11
comparisons — inside the certified envelope `4·(25 + 9) + 4 = 140`. -/
theorem levelDenoteEquivDecisionComplexity_stepCount_smoke_larger :
    levelDenoteEquivDecisionComplexity.stepCount
      (.lmax (.lvar 1) (.lmax (.lvar 0) (.lvar 2))) (.lmax (.lvar 0) (.lvar 0)) = 11 := rfl

end FX1Poly.Universe
