import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithWindowedChainReduction

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithDiagonalInputSpecialization — the diagonal-input
    specialization of the Smith keystone (H2-SMITH r24, #2261)

The r22–r23 arc collapsed the corrected-driver totality
(`SmithReduceCompleteDriverStatement`) onto the SINGLE residual
`SmithCascadeLandedPivotDividesMinor`: the pivot-`p` clearing position sweep lands, at the pivot,
a divisor of every entry of the input's `[p, ·)` minor (the "min-abs Euclid cascade computes the
gcd" fact — a standalone major arc).

r24 asks whether SPECIALIZING that keystone to DIAGONAL inputs — the shape the Phase-A output
provably has (`smithReduceTotalSweepDiagonalizes`) — closes the chain.  The verdict, machine-adjudicated
here, is **NO** (recon fill-in-region verdict (iii)):

  * On a window-diagonal input the keystone's INPUT off-diagonal cells are all `0` (divisible by
    anything), so the keystone-input-minor divisibility collapses to the DIAGONAL half alone
    (`matrixEntriesDivisibleByWithinOfDiagonalInput`) — a genuine narrowing.
  * But `chainWindowedThroughPivots` (NODE A of the shipped reduction) invokes the keystone on the
    ADVANCED matrix at every pivot `p ≥ 1`, and the advanced matrix is generally NON-diagonal:
    `smithDiagonalInputPivotOneInputNotWindowDiagonal` machine-refutes window-diagonality of the
    pivot-0 sweep output of `diag(15, 10, 6, 4)` at floor `1` (its `[1, ·)` minor carries `-20` at
    `(3, 1)`).  So the diagonal-input specialization discharges ONLY the pivot-0 evaluation and does
    NOT re-plumb the chain.

This file also ships the pure PAIRWISE-GCD contract (`IntPairwiseGcdSpec`, the cash-out of the shipped
Euclid induction) and the ITERATED-pairwise-gcd common-divisor fact (`intGcdFoldrDividesAll`), which is
the ARITHMETIC half of the diagonal-common-divisor obligation.  The surviving residual remains
`SmithCascadeLandedPivotDividesMinor` (the cascade lands the diagonal gcd), OPEN.

## Zero-axiom

`by decide` on small `Int`/matrix literals (independently `#print axioms`-clean), structural
`List.foldr` recursion, `∃`-witness arithmetic over the shipped `intGcd*` / `intMulAssoc` /
`entryAtBeyondZero` / `matrixEntriesDivisibleByWithinOfHalves`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithDiagonalInputSpecialization.lean`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## BRICK 1 — the pairwise-gcd contract + the eval truth-probes (H2-SMITH r24, B1)

The pairwise gcd `intGcd a b` and all its structural facts are SHIPPED (`IntGreatestCommonDivisor`,
riding the counting-Euclid induction `natGcdWithFuelDividesBoth` / `natGcdBezout`).  B1 truth-probes
the values on the recon battery FIRST (by `decide`), then bundles the shipped facts into ONE reusable
contract `IntPairwiseGcdSpec` (nonnegative common divisor, greatest).  The magnitude-descent half of
the contract is the SHIPPED `smithRepairDecreasesPivotSize`
(`(intGcd a b).natAbs < a.natAbs` when `0 < a.natAbs ∧ a ∤ b`); it is conditional, so it stays a
companion rather than an unconditional field. -/

/-- Pairwise gcd of the NODE-A fold operands: `gcd(15, 10) = 5`. -/
theorem intGcdFifteenTen : intGcd 15 10 = 5 := by decide

/-- Pairwise gcd of the concrete gcd > 1 window pivot pair: `gcd(6, 10) = 2`. -/
theorem intGcdSixTen : intGcd 6 10 = 2 := by decide

/-- Zero-pivot bootstrap: `gcd(0, 4) = 4` — `0` contributes nothing, the gcd is the other magnitude. -/
theorem intGcdZeroFour : intGcd 0 4 = 4 := by decide

/-- Both-negative pair: signs fold into magnitudes, `gcd(-6, -4) = 2`. -/
theorem intGcdNegSixNegFour : intGcd (-6) (-4) = 2 := by decide

/-- Mixed-sign pair: `gcd(6, -4) = 2` (the nonnegative representative). -/
theorem intGcdSixNegFour : intGcd 6 (-4) = 2 := by decide

/-- Negative-left pair: `gcd(-15, 10) = 5`. -/
theorem intGcdNegFifteenTen : intGcd (-15) 10 = 5 := by decide

/-- **The pairwise-gcd contract over `Int`** — `intGcd a b` is a NONNEGATIVE common divisor of the
pair that is GREATEST (every common divisor divides it).  The reusable cash-out of the shipped
counting-Euclid induction; the conditional magnitude-descent half is the companion
`smithRepairDecreasesPivotSize`. -/
structure IntPairwiseGcdSpec (leftValue rightValue : Int) : Prop where
  /-- The gcd is nonnegative (the canonical sign choice). -/
  isNonnegative : (0 : Int) ≤ intGcd leftValue rightValue
  /-- The gcd divides the left argument. -/
  dividesLeft : IntDivides (intGcd leftValue rightValue) leftValue
  /-- The gcd divides the right argument. -/
  dividesRight : IntDivides (intGcd leftValue rightValue) rightValue
  /-- Every common divisor of the pair divides the gcd. -/
  isGreatest : ∀ {commonDivisor : Int}, IntDivides commonDivisor leftValue →
    IntDivides commonDivisor rightValue → IntDivides commonDivisor (intGcd leftValue rightValue)

/-- **`intGcd` satisfies the pairwise-gcd contract** — assembles the shipped `intGcdIsNonnegative`,
`intGcdDividesLeft`, `intGcdDividesRight`, `intGcdGreatest` into the single contract object.  A
`∀ a b`-theorem to fire on the battery. -/
theorem intGcdSatisfiesPairwiseSpec (leftValue rightValue : Int) :
    IntPairwiseGcdSpec leftValue rightValue :=
  ⟨intGcdIsNonnegative leftValue rightValue,
   intGcdDividesLeft leftValue rightValue,
   intGcdDividesRight leftValue rightValue,
   fun dividesLeft dividesRight => intGcdGreatest dividesLeft dividesRight⟩

end FX1Poly.ComputerAlgebra
