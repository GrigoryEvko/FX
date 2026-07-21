import FX1Poly.ComputerAlgebra.Decision.PresburgerCooper

/-! # FX1Poly/ComputerAlgebra/Decision/PresburgerCooperFires — kernel-decided
    fires for the Cooper decision pipeline (`rfl` pins)

Concrete instances exercising `pcqDecide` end-to-end through NNF,
product-scale unitarization, the Cooper elimination step, and ground
evaluation:

  * The `2x = 1` integrality gap `∃ x. 2x < 2 ∧ 0 < 2x` decides FALSE while
    its rational relaxation is satisfiable at `x = 1/2` — the exact reason
    Farkas and Fourier–Motzkin certificates fail to decide the integers.
    Pinned both directly and through the system-translation path
    (`pcqSystemFormula` on the `2x = 1` equality row under `pcqFexN`
    closure, the formula `pcqPresburgerDecisionHolds` evaluates).
  * `∃ x. 3 | x ∧ x > 5` decides TRUE (divisibility atom).
  * `∃ x. ∃ y. x < y ∧ y < x + 2` decides TRUE (two Cooper rounds).
  * `∃ x. x < 0 ∧ 0 < x` decides FALSE (empty strict window).
  * `¬ ∃ x. 2x = 1` decides TRUE (negation path through `fneg`/`qneg`).

All pins are `rfl` on `Bool` equalities; the kernel evaluates the full
pipeline.  Zero-axiom discipline matches the parent file; per-declaration
gate in the audit twin. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.ComputerAlgebra

/-! ## Fixture terms -/

/-- The term `2 * v0` (coefficient vector `[2]`, constant `0`). -/
def pcqFireTwoPivotTerm : PcqTerm :=
  PcqTerm.mk (LfkInt.mk 2 0 :: List.nil) lfkIntZero

/-- The term `v0` (coefficient vector `[1]`, constant `0`). -/
def pcqFirePivotTerm : PcqTerm :=
  PcqTerm.mk (LfkInt.mk 1 0 :: List.nil) lfkIntZero

/-- The term `v1` under two binders (coefficient vector `[0, 1]`). -/
def pcqFireOuterPivotTerm : PcqTerm :=
  PcqTerm.mk (lfkIntZero :: LfkInt.mk 1 0 :: List.nil) lfkIntZero

/-- The term `v1 + 2` under two binders. -/
def pcqFireOuterPivotPlusTwoTerm : PcqTerm :=
  PcqTerm.mk (lfkIntZero :: LfkInt.mk 1 0 :: List.nil) (LfkInt.mk 2 0)

/-! ## Fire 1 — THE INTEGRALITY GAP: `∃ x. 2x = 1` decides FALSE -/

/-- `∃ x. 2x < 2 ∧ 0 < 2x` — the succ-le rendering of `∃ x. 2x = 1`. -/
def pcqFireGapFormula : PcqFormula :=
  PcqFormula.fexists
    (PcqFormula.fconj
      (PcqFormula.flt pcqFireTwoPivotTerm (pcqConstTerm (LfkInt.mk 2 0)))
      (PcqFormula.flt (pcqConstTerm lfkIntZero) pcqFireTwoPivotTerm))

/-- FALSE: the integrality gap has no integer witness. -/
theorem pcqFireGapDecidesFalse : pcqDecide pcqFireGapFormula = false := rfl

/-- The gap as a constraint system: the single equality row `2x = 1`. -/
def pcqFireGapSystem : List LfkConstraint :=
  LfkConstraint.mk (LfkInt.mk 2 0 :: List.nil) (LfkInt.mk 1 0) LfkRelation.isEqualTo
    :: List.nil

/-- FALSE, system-translation path: deciding the translated, existentially
closed `2x = 1` system (the formula `pcqPresburgerDecisionHolds` evaluates). -/
theorem pcqFireGapSystemDecidesFalse :
    pcqDecide (pcqFexN (pcqSystemVarCount pcqFireGapSystem)
      (pcqSystemFormula pcqFireGapSystem)) = false := rfl

/-- The separator's other half: environment `[1]` satisfies the
denominator-2-scaled system, so the gap is rationally feasible (`x = 1/2`) and
certificate-free, yet integer-FALSE by the pin above. -/
theorem pcqFireGapRationallyFeasible :
    lfkSatisfiesSystem (LfkInt.mk 1 0 :: List.nil)
      (lfkScaleBoundsForDenominator 2 pcqFireGapSystem) = true := rfl

/-! ## Fire 2 — `∃ x. 3 | x ∧ x > 5` decides TRUE -/

/-- `∃ x. 3 | x ∧ 5 < x`. -/
def pcqFireDvdFormula : PcqFormula :=
  PcqFormula.fexists
    (PcqFormula.fconj
      (PcqFormula.fdvd 2 pcqFirePivotTerm)
      (PcqFormula.flt (pcqConstTerm (LfkInt.mk 5 0)) pcqFirePivotTerm))

/-- TRUE: `x = 6` is a witness. -/
theorem pcqFireDvdDecidesTrue : pcqDecide pcqFireDvdFormula = true := rfl

/-! ## Fire 3 — two quantifiers: `∃ x. ∃ y. x < y ∧ y < x + 2` decides TRUE -/

/-- `∃ x. ∃ y. x < y ∧ y < x + 2` (witness `y = x + 1`). -/
def pcqFireTwoQuantFormula : PcqFormula :=
  PcqFormula.fexists
    (PcqFormula.fexists
      (PcqFormula.fconj
        (PcqFormula.flt pcqFireOuterPivotTerm pcqFirePivotTerm)
        (PcqFormula.flt pcqFirePivotTerm pcqFireOuterPivotPlusTwoTerm)))

/-- TRUE: two Cooper rounds compose. -/
theorem pcqFireTwoQuantDecidesTrue : pcqDecide pcqFireTwoQuantFormula = true := rfl

/-! ## Fire 4 — negative control: `∃ x. x < 0 ∧ 0 < x` decides FALSE -/

/-- `∃ x. x < 0 ∧ 0 < x` — an unsatisfiable window. -/
def pcqFireEmptyWindowFormula : PcqFormula :=
  PcqFormula.fexists
    (PcqFormula.fconj
      (PcqFormula.flt pcqFirePivotTerm (pcqConstTerm lfkIntZero))
      (PcqFormula.flt (pcqConstTerm lfkIntZero) pcqFirePivotTerm))

/-- FALSE: the empty strict window refutes. -/
theorem pcqFireEmptyWindowDecidesFalse :
    pcqDecide pcqFireEmptyWindowFormula = false := rfl

/-! ## Fire 5 — the negation path: `¬ ∃ x. 2x = 1` decides TRUE -/

/-- TRUE: the negated gap decides through `fneg`/`qneg`. -/
theorem pcqFireNegatedGapDecidesTrue :
    pcqDecide (PcqFormula.fneg pcqFireGapFormula) = true := rfl

-- Executable demonstrations; each mirrors an `rfl` pin above.
#eval pcqDecide pcqFireGapFormula
#eval pcqDecide (pcqFexN (pcqSystemVarCount pcqFireGapSystem)
  (pcqSystemFormula pcqFireGapSystem))
#eval lfkSatisfiesSystem (LfkInt.mk 1 0 :: List.nil)
  (lfkScaleBoundsForDenominator 2 pcqFireGapSystem)
#eval pcqDecide pcqFireDvdFormula
#eval pcqDecide pcqFireTwoQuantFormula
#eval pcqDecide pcqFireEmptyWindowFormula
#eval pcqDecide (PcqFormula.fneg pcqFireGapFormula)

end FX1Poly.ComputerAlgebra
