import FX1Poly.ComputerAlgebra.Decision.PresburgerCooper

/-! # FX1Poly/ComputerAlgebra/Decision/PresburgerCooperFires — kernel-decided
    fires for the Cooper decision pipeline (tiny deltas, `rfl` pins)

Concrete instances exercising `pcqDecide` end-to-end through NNF,
product-scale unitarization, the Cooper step, and ground evaluation:

  * **THE 2x = 1 INTEGRALITY GAP** (the DISSAT-ARITH lane's signature
    separator): `∃ x. 2x < 2 ∧ 0 < 2x` — i.e. `∃ x. 2x = 1` in the succ-le
    encoding — decides FALSE, while its rational relaxation is satisfiable
    (`x = 1/2`), which is exactly why Farkas/Fourier–Motzkin certificates
    cannot decide the integers (`lfkPresburgerDecisionStatement`'s
    docstring names this gap).  Pinned BOTH directly and through the lane
    translation path (`pcqSystemFormula` on the `2x = 1` equality row plus
    `pcqFexN` closure — the exact route `pcqPresburgerDecisionHolds` runs).
  * `∃ x. 3 | x ∧ x > 5` decides TRUE (divisibility atom live, delta 3).
  * A TWO-QUANTIFIER instance `∃ x. ∃ y. x < y ∧ y < x + 2` decides TRUE
    (two full Cooper rounds, inner then outer).
  * Negative control `∃ x. x < 0 ∧ 0 < x` decides FALSE.
  * The negation path: `¬ ∃ x. 2x = 1` decides TRUE (`fneg`/`qneg` live).

All pins are `rfl` on `Bool` equalities — the kernel evaluates the full
pipeline.  All deltas are at most 4.  Zero-axiom discipline identical to the
parent file; per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/Decision/PresburgerCooperFires.lean`. -/

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

/-- KERNEL PIN (FALSE): the integrality gap has no integer witness. -/
theorem pcqFireGapDecidesFalse : pcqDecide pcqFireGapFormula = false := rfl

/-- The gap as a LANE constraint system: the single equality row `2x = 1`. -/
def pcqFireGapSystem : List LfkConstraint :=
  LfkConstraint.mk (LfkInt.mk 2 0 :: List.nil) (LfkInt.mk 1 0) LfkRelation.isEqualTo
    :: List.nil

/-- KERNEL PIN (FALSE, lane translation path): deciding the translated,
existentially closed `2x = 1` system — the exact formula
`pcqPresburgerDecisionHolds` evaluates — lands FALSE. -/
theorem pcqFireGapSystemDecidesFalse :
    pcqDecide (pcqFexN (pcqSystemVarCount pcqFireGapSystem)
      (pcqSystemFormula pcqFireGapSystem)) = false := rfl

/-- KERNEL PIN (the separator's other half): the rational point `x = 1/2`
satisfies the denominator-2-scaled system `2x = 2·(1/2)·... ` — concretely,
the environment `[1]` satisfies the bounds-doubled system, so the gap system
is RATIONALLY feasible and hence Farkas-certificate-free, yet integer-FALSE
by the pin above. -/
theorem pcqFireGapRationallyFeasible :
    lfkSatisfiesSystem (LfkInt.mk 1 0 :: List.nil)
      (lfkScaleBoundsForDenominator 2 pcqFireGapSystem) = true := rfl

/-! ## Fire 2 — `∃ x. 3 | x ∧ x > 5` decides TRUE -/

/-- `∃ x. 3 | x ∧ 5 < x` (modulus literal `2 + 1 = 3`). -/
def pcqFireDvdFormula : PcqFormula :=
  PcqFormula.fexists
    (PcqFormula.fconj
      (PcqFormula.fdvd 2 pcqFirePivotTerm)
      (PcqFormula.flt (pcqConstTerm (LfkInt.mk 5 0)) pcqFirePivotTerm))

/-- KERNEL PIN (TRUE): `x = 6` exists (found at boundary window `5 + 1`). -/
theorem pcqFireDvdDecidesTrue : pcqDecide pcqFireDvdFormula = true := rfl

/-! ## Fire 3 — two quantifiers: `∃ x. ∃ y. x < y ∧ y < x + 2` decides TRUE -/

/-- `∃ x. ∃ y. x < y ∧ y < x + 2` (inner binder `y` at index 0, outer `x` at
index 1; the witness is `y = x + 1`). -/
def pcqFireTwoQuantFormula : PcqFormula :=
  PcqFormula.fexists
    (PcqFormula.fexists
      (PcqFormula.fconj
        (PcqFormula.flt pcqFireOuterPivotTerm pcqFirePivotTerm)
        (PcqFormula.flt pcqFirePivotTerm pcqFireOuterPivotPlusTwoTerm)))

/-- KERNEL PIN (TRUE): two full Cooper rounds compose. -/
theorem pcqFireTwoQuantDecidesTrue : pcqDecide pcqFireTwoQuantFormula = true := rfl

/-! ## Fire 4 — negative control: `∃ x. x < 0 ∧ 0 < x` decides FALSE -/

/-- `∃ x. x < 0 ∧ 0 < x` — an unsatisfiable window with delta 1. -/
def pcqFireEmptyWindowFormula : PcqFormula :=
  PcqFormula.fexists
    (PcqFormula.fconj
      (PcqFormula.flt pcqFirePivotTerm (pcqConstTerm lfkIntZero))
      (PcqFormula.flt (pcqConstTerm lfkIntZero) pcqFirePivotTerm))

/-- KERNEL PIN (FALSE): the empty strict window refutes. -/
theorem pcqFireEmptyWindowDecidesFalse :
    pcqDecide pcqFireEmptyWindowFormula = false := rfl

/-! ## Fire 5 — the negation path: `¬ ∃ x. 2x = 1` decides TRUE -/

/-- KERNEL PIN (TRUE): the negated gap decides TRUE through `fneg`/`qneg`. -/
theorem pcqFireNegatedGapDecidesTrue :
    pcqDecide (PcqFormula.fneg pcqFireGapFormula) = true := rfl

-- The integrality gap, direct encoding. Expect: false
#eval pcqDecide pcqFireGapFormula
-- The gap through the lane translation + existential closure. Expect: false
#eval pcqDecide (pcqFexN (pcqSystemVarCount pcqFireGapSystem)
  (pcqSystemFormula pcqFireGapSystem))
-- The gap's rational relaxation (denominator 2, env [1]). Expect: true
#eval lfkSatisfiesSystem (LfkInt.mk 1 0 :: List.nil)
  (lfkScaleBoundsForDenominator 2 pcqFireGapSystem)
-- Divisibility fire: exists x, 3 | x and x > 5. Expect: true
#eval pcqDecide pcqFireDvdFormula
-- Two-quantifier fire. Expect: true
#eval pcqDecide pcqFireTwoQuantFormula
-- Negative control: empty strict window. Expect: false
#eval pcqDecide pcqFireEmptyWindowFormula
-- Negation path: not (exists x, 2x = 1). Expect: true
#eval pcqDecide (PcqFormula.fneg pcqFireGapFormula)

end FX1Poly.ComputerAlgebra
