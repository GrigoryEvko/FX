import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialGcd
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDegree
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDegreeBound
import FX1Poly.ComputerAlgebra.Number.IntNoZeroDivisors

/-! # IntPolynomialGcdConverse — every GCD root is a common root

Proves the converse of `polyGcdVanishesAtCommonRoot`, so the GCD's root set is exactly the common-root set.
`polyPseudoRemBackwardRoot` is the single Euclidean-step converse (for a nonzero divisor, `eval(divisor) = 0
∧ eval(pseudoRem) = 0 → eval(dividend) = 0`, cancelling `leadDivisor^scalePower` off the reconstruction via
the ℤ no-zero-divisor).  `polyGcdRootIsCommonRoot` carries it through the recursion under the `Bool`-valued
honest-termination flag `polyGcdReachesNil`, which rules out the fuel-exhaustion fallback that would
otherwise break the converse.

Reconstruction identity + ℤ no-zero-divisor + structural fuel recursion; `Bool.noConfusion` /
`List.cons_ne_nil` close the `polyTrim` split.  Free of `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The single Euclidean-step converse -/

/-- **A root of the divisor and the pseudo-remainder is a root of the dividend.**  For a nonzero `divisor`,
`eval(divisor) = 0 ∧ eval(pseudoRem) = 0 → eval(dividend) = 0`.  The reconstruction gives
`leadDivisor^scalePower · eval(dividend) = eval(quotient)·eval(divisor) + eval(remainder) = 0`, and the
leading power is nonzero, so the dividend vanishes. -/
theorem polyPseudoRemBackwardRoot (point : Int) (fuel : Nat) (divisor dividend : List Int)
    (isDivisorNonempty : polyTrim divisor ≠ [])
    (divisorVanishes : polyEval point divisor = 0)
    (remainderVanishes : polyEval point (polyPseudoRem fuel divisor dividend) = 0) :
    polyEval point dividend = 0 := by
  have rightIsZero :
      polyEval point (polyPseudoDivMod fuel divisor dividend).2.1 * polyEval point divisor
          + polyEval point (polyPseudoDivMod fuel divisor dividend).2.2
        = 0 := by
    rw [divisorVanishes, intMulZero, intZeroAdd]
    exact remainderVanishes
  have scaledIsZero :
      intPower (polyLeadingCoeff divisor) (polyPseudoDivMod fuel divisor dividend).1
          * polyEval point dividend
        = 0 :=
    (polyPseudoDivModReconstructs point fuel divisor dividend).trans rightIsZero
  exact intMulEqZeroLeftFactor
    (intPowerNeZero (polyLeadingCoeffNonzeroWhenNonempty divisor isDivisorNonempty) _)
    scaledIsZero

/-! ## Evaluation of a trimmed-away polynomial -/

/-- **A polynomial that trims to nil vanishes everywhere.**  `polyTrim coeffs = [] → polyEval point coeffs
= 0`: trimming preserves evaluation and `polyEval point [] = 0`. -/
theorem polyEvalZeroOfTrimNil (point : Int) (coeffs : List Int) (isTrimNil : polyTrim coeffs = []) :
    polyEval point coeffs = 0 :=
  (polyTrimPreservesEval point coeffs).symm.trans (congrArg (polyEval point) isTrimNil)

/-! ## The Euclidean-termination adequacy flag -/

/-- **The GCD recursion terminates honestly (not by fuel exhaustion).**  `true` exactly when
`polyGcd fuel primary secondary` reaches the `polyTrim secondary = []` branch within `fuel`; at `fuel = 0`
it demands `polyTrim secondary = []` (the only honest reading of the fuel-0 fallback). -/
def polyGcdReachesNil : Nat → List Int → List Int → Bool
  | 0, _, secondary => match polyTrim secondary with | [] => true | _ :: _ => false
  | fuel + 1, primary, secondary =>
      match polyTrim secondary with
      | [] => true
      | _ :: _ => polyGcdReachesNil fuel secondary (polyPseudoRem fuel secondary primary)

/-! ## The full converse (carried through the Euclidean recursion) -/

/-- **Every root of an honestly-terminated GCD is a common root.**  If `polyGcdReachesNil fuel primary
secondary` and `polyEval point (polyGcd fuel primary secondary) = 0`, then `point` is a root of both inputs.
Induction on fuel: the `polyTrim secondary = []` cases identify the GCD with `primary` and force `secondary`
to vanish; the Euclidean step recovers `primary`'s root via `polyPseudoRemBackwardRoot`. -/
theorem polyGcdRootIsCommonRoot (point : Int) :
    ∀ (fuel : Nat) (primary secondary : List Int),
      polyGcdReachesNil fuel primary secondary = true →
      polyEval point (polyGcd fuel primary secondary) = 0 →
      polyEval point primary = 0 ∧ polyEval point secondary = 0
  | 0, primary, secondary => by
      dsimp only [polyGcd, polyGcdReachesNil]
      cases hTrim : polyTrim secondary with
      | nil => intro _ gcdVanishes; exact ⟨gcdVanishes, polyEvalZeroOfTrimNil point secondary hTrim⟩
      | cons _ _ => intro reachesNil _; exact Bool.noConfusion reachesNil
  | fuel + 1, primary, secondary => by
      dsimp only [polyGcd, polyGcdReachesNil]
      cases hTrim : polyTrim secondary with
      | nil => intro _ gcdVanishes; exact ⟨gcdVanishes, polyEvalZeroOfTrimNil point secondary hTrim⟩
      | cons trimHead trimTail =>
          intro reachesNil gcdVanishes
          have ih := polyGcdRootIsCommonRoot point fuel secondary
            (polyPseudoRem fuel secondary primary) reachesNil gcdVanishes
          exact ⟨polyPseudoRemBackwardRoot point fuel secondary primary
              (fun contra => List.cons_ne_nil trimHead trimTail (hTrim.symm.trans contra)) ih.1 ih.2,
            ih.1⟩

/-! ## Groundings -/

/-- The single-step converse exhibited: with divisor `x + 1` (`[1, 1]`, root `−1`) and dividend `x² − 1`
(`[-1, 0, 1]`), the pseudo-remainder vanishes at `−1` and so does the divisor, so the dividend does too —
`polyEval (-1) [-1, 0, 1] = 0`. -/
theorem polyPseudoRemBackwardRootGrounding : polyEval (-1) [-1, 0, 1] = 0 := by decide

/-- The full converse on the shared factor of `x² − 1 = (x−1)(x+1)` and `(x+1)² = x² + 2x + 1`: the
honestly-terminated GCD (fuel 5) has root `−1`, and `−1` is a root of the second input `[1, 2, 1]`. -/
theorem polyGcdRootIsCommonRootGrounding : polyEval (-1) [1, 2, 1] = 0 := by decide

/-- The adequacy flag fires on the worked instance (fuel 5 suffices for the two quadratics). -/
theorem polyGcdReachesNilGrounding : polyGcdReachesNil 5 [-1, 0, 1] [1, 2, 1] = true := by decide

end FX1Poly.ComputerAlgebra
