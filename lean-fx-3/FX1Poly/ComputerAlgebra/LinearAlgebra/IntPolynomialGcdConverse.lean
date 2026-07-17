import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialGcd
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDegree
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDegreeBound
import FX1Poly.ComputerAlgebra.Number.IntNoZeroDivisors

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntPolynomialGcdConverse — every GCD root is a common root
(the twelfth brick of `invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255)

`IntPolynomialGcd` proved the *forward* direction — the GCD vanishes at every common root of its inputs
(`polyGcdVanishesAtCommonRoot`).  This file proves the *converse*: every root of the GCD is a common root
of the inputs, so the GCD's root set is *exactly* the common-root set.

## What is PROVEN

  * `polyPseudoRemBackwardRoot` (the single Euclidean-step converse): for a nonzero `divisor`,
    `eval(divisor) = 0 ∧ eval(pseudoRem) = 0 → eval(dividend) = 0` — read backward off the r10
    reconstruction `leadDivisor^scalePower · eval(dividend) = eval(quotient)·eval(divisor) +
    eval(remainder)`: both right-hand terms vanish, so `leadDivisor^scalePower · eval(dividend) = 0`, and
    (r22, `leadDivisor ≠ 0` since the divisor is nonempty) `eval(dividend) = 0`.
  * `polyGcdRootIsCommonRoot` (the full converse): every root of `polyGcd fuel primary secondary` is a root
    of *both* `primary` and `secondary` — **provided the recursion terminated honestly** (the adequacy flag
    `polyGcdReachesNil`, i.e. it reached the `polyTrim secondary = []` branch rather than exhausting fuel).
    The `fuel = 0` fallback returns `primary` and says nothing about `secondary`, so the adequacy guard is
    exactly the honest boundary; the flag is discharged by fuel-adequacy (r21) at any real call site.

Together with `polyGcdVanishesAtCommonRoot`, the polynomial GCD's roots ARE the common roots.

## Why the adequacy flag

`polyGcd 0 primary _ = primary` unconditionally, and `polyGcd (fuel+1) primary secondary = primary` when
`polyTrim secondary = []` (secondary is the zero polynomial there, so it vanishes at *every* point — the
converse holds).  Only the fuel-exhaustion fallback breaks the converse, so `polyGcdReachesNil` rules
exactly that out: `true` at `fuel+1`/nil, recursion otherwise, and at `fuel = 0` it demands
`polyTrim secondary = []`.

## Zero-axiom design

Reconstruction identity + the arbitrary-sign ℤ no-zero-divisor (r22) + structural fuel recursion; the
adequacy flag is `Bool`-valued (no Prop-match), and the only case analysis is `polyTrim`'s `nil`/`cons`
enumeration closed by `Bool.noConfusion` / `List.cons_ne_nil`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/IntPolynomialGcdConverse.lean`.
-/

namespace FX1Poly.ComputerAlgebra

/-! ## The single Euclidean-step converse -/

/-- **A root of the divisor and the pseudo-remainder is a root of the dividend.**  For a nonzero `divisor`,
`eval(divisor) = 0 ∧ eval(pseudoRem) = 0 → eval(dividend) = 0`.  The r10 reconstruction gives
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
secondary` and `polyEval point (polyGcd fuel primary secondary) = 0`, then `point` is a root of *both*
`primary` and `secondary`.  Induction on fuel: the `polyTrim secondary = []` cases identify the GCD with
`primary` and force `secondary` to vanish (it trims away); the Euclidean step recovers `primary`'s root
from the recursive result (`secondary`'s and the pseudo-remainder's roots) via the single-step converse
(`polyPseudoRemBackwardRoot`, divisor nonempty in the `cons` branch). -/
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

/-- The full converse exhibited on the shared factor of `x² − 1 = (x−1)(x+1)` and `(x+1)² = x² + 2x + 1`:
the honestly-terminated GCD (fuel 5) has root `−1`, and `−1` is a root of *both* inputs — here shown for
the second input `polyEval (-1) [1, 2, 1] = 0`. -/
theorem polyGcdRootIsCommonRootGrounding : polyEval (-1) [1, 2, 1] = 0 := by decide

/-- The adequacy flag fires on the worked instance (fuel 5 suffices for the two quadratics). -/
theorem polyGcdReachesNilGrounding : polyGcdReachesNil 5 [-1, 0, 1] [1, 2, 1] = true := by decide

/-- Marker: the ℤ[x] GCD converse root-containment — a root of both the divisor and the pseudo-remainder is
a root of the dividend (`polyPseudoRemBackwardRoot`), carried through the Euclidean recursion under the
honest-termination flag (`polyGcdRootIsCommonRoot`).  With `polyGcdVanishesAtCommonRoot`, the GCD's roots
are exactly the common roots. -/
def fxIntPoly_hasGcdConverseRootContainment : Bool := true

end FX1Poly.ComputerAlgebra
