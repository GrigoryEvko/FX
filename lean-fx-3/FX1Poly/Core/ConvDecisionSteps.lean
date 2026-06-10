import FX1Poly.Core.NormalizeSteps

/-! # FX1Poly/Core/ConvDecisionSteps
   — the exact cost witness for the SN-fragment `Conv` decider (M19, STRICT-COMPLEXITY)

`Conv.decidableOfStronglyNormalizing` decides convertibility of two strongly-normalizing terms by
normalizing BOTH operands and comparing the normal forms.  Its dominant cost is therefore the two
normalizer runs; this file ships the exact accounting:

  * `Conv.decideStronglyNormalizingSteps` — the decider's reducer-firing count: the sum of the two
    operands' `normalizeSteps`.  Mirror-faithful by construction: the decider's verdict is computed
    from exactly the two `RawTerm.normalize` runs the counter instruments (the trailing
    normal-form equality test is one structural `DecidableEq` pass over the OUTPUTS, not counted —
    stated, not absorbed).
  * `Conv.decideStronglyNormalizing_costAccounting` — the one-object package: the verdict IS
    normal-form equality of the two normalizer outputs (`iff_normalize_eq`), and each run is a
    counted chain of exactly its `normalizeSteps` length (`normalizeSteps_chainExact`).
  * `decideStronglyNormalizingSteps_eq_zero_iff_normalForms` — the positive anchor: the decider
    performs ZERO reducer firings exactly when both operands are already structural normal forms
    (the normal-fragment decider's cost is the comparison pass alone).

## The honest STRICT-COMPLEXITY verdict for raw `Conv` (closing M19 honestly)

The `DecisionComplexity` schema (the §11.8.7 polynomial witness, instantiated for the LevelExpr
decider) is deliberately NOT instantiated for raw `Conv`: the decider's cost is two β-normalization
runs, and β-normalization length is non-elementary in term size (Statman 1979) — no size-polynomial
`stepCount_isPolynomial` field can be truthfully supplied.  What IS machine-checked: the exact
counter, its chain-length identity, the zero-cost normal fragment, the identity-tower family
realizing the count exactly, and unboundedness (`Typed/NormalizeStepsTower.lean`).  The
"decidable but EXP-tower" loophole of §11.8.7 is thus closed by DISCLOSURE: the cost is exact and
visibly unbounded, never hidden behind a polynomial overclaim.

## Zero-axiom verification

Compositions of the shipped `normalizeSteps` facts and `iff_normalize_eq_of_isStronglyNormalizing`;
`Nat` arithmetic is `add`-monotonicity only.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open Foundation

/-- **The SN-fragment `Conv` decider's exact reducer-firing count**: the decider normalizes both
operands, so its reduction cost is the sum of the two exact normalizer counters.  The trailing
normal-form `DecidableEq` comparison is a single structural pass over the outputs (not a reducer
firing; stated in the module docstring). -/
def Conv.decideStronglyNormalizingSteps {scope : Nat} (leftTerm rightTerm : RawTerm scope)
    (leftTerminates : StepStar.IsStronglyNormalizing leftTerm)
    (rightTerminates : StepStar.IsStronglyNormalizing rightTerm) : Nat :=
  RawTerm.normalizeSteps leftTerm leftTerminates +
    RawTerm.normalizeSteps rightTerm rightTerminates

/-- **The cost-accounting package for the SN-fragment `Conv` decider**: the verdict is exactly
normal-form equality of the two normalizer outputs, and each normalizer run is a counted reduction
chain of exactly its `normalizeSteps` length — so the decider's behavior and its cost are pinned
by one object. -/
theorem Conv.decideStronglyNormalizing_costAccounting {scope : Nat}
    {leftTerm rightTerm : RawTerm scope}
    (leftTerminates : StepStar.IsStronglyNormalizing leftTerm)
    (rightTerminates : StepStar.IsStronglyNormalizing rightTerm) :
    (Conv leftTerm rightTerm ↔
      RawTerm.normalize leftTerm leftTerminates =
        RawTerm.normalize rightTerm rightTerminates) ∧
    StepStarN (RawTerm.normalizeSteps leftTerm leftTerminates) leftTerm
      (RawTerm.normalize leftTerm leftTerminates) ∧
    StepStarN (RawTerm.normalizeSteps rightTerm rightTerminates) rightTerm
      (RawTerm.normalize rightTerm rightTerminates) :=
  ⟨Conv.iff_normalize_eq_of_isStronglyNormalizing leftTerminates rightTerminates,
   RawTerm.normalizeSteps_chainExact leftTerm leftTerminates,
   RawTerm.normalizeSteps_chainExact rightTerm rightTerminates⟩

/-- **Zero reducer firings exactly on the normal fragment**: the decider's reduction cost vanishes
iff both operands are already structural normal forms — there the whole decision is the
comparison pass (the #716 normal-fragment decider's regime). -/
theorem Conv.decideStronglyNormalizingSteps_eq_zero_iff_normalForms {scope : Nat}
    (leftTerm rightTerm : RawTerm scope)
    (leftTerminates : StepStar.IsStronglyNormalizing leftTerm)
    (rightTerminates : StepStar.IsStronglyNormalizing rightTerm) :
    Conv.decideStronglyNormalizingSteps leftTerm rightTerm leftTerminates rightTerminates = 0 ↔
      (RawTerm.isStepNormalForm leftTerm ∧ RawTerm.isStepNormalForm rightTerm) := by
  constructor
  · intro hZeroTotal
    have hBothZero := Nat.add_eq_zero_iff.mp hZeroTotal
    exact ⟨(RawTerm.normalizeSteps_eq_zero_iff leftTerm leftTerminates).mp hBothZero.1,
           (RawTerm.normalizeSteps_eq_zero_iff rightTerm rightTerminates).mp hBothZero.2⟩
  · intro hBothNormal
    show RawTerm.normalizeSteps leftTerm leftTerminates +
        RawTerm.normalizeSteps rightTerm rightTerminates = 0
    rw [(RawTerm.normalizeSteps_eq_zero_iff leftTerm leftTerminates).mpr hBothNormal.1,
        (RawTerm.normalizeSteps_eq_zero_iff rightTerm rightTerminates).mpr hBothNormal.2]

end FX1Poly.Core
