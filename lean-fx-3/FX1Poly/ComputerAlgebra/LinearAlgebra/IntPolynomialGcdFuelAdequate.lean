import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialConstDivisorNil
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialPseudoRemBound
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialGcdRootSet

/-! # IntPolynomialGcdFuelAdequate — the fuel-adequacy capstone of the ℤ[x] GCD

With a computed adequate fuel the Euclidean GCD terminates honestly (`polyGcdReachesNil = true`), so the
converse root-containment holds unconditionally — no flag hypothesis to discharge.  This is the parent of
the ℤ[x] GCD sub-arc, whose markers are consolidated here (see `fxIntPoly_hasGcdFuelAdequacy`).

  * `polyGcdStepMeasureDecreases`: the Euclidean step strictly shrinks the divisor's trim-length —
    `(polyTrim (polyPseudoRem fuel secondary primary)).length < (polyTrim secondary).length` for a nonempty
    `secondary` and adequate inner fuel, whether the divisor is nonconstant (pseudo-remainder degree drops)
    or constant (pseudo-remainder is zero).
  * `polyGcdReachesNilOfBudget` / `polyGcdReachesNilAdequateFuel`: for
    `fuel = (polyTrim secondary).length + (polyDegree primary + polyDegree secondary) + 1`,
    `polyGcdReachesNil fuel primary secondary = true` — the strictly-decreasing measure exhausts within the
    computed fuel.
  * `polyGcdAdequateFuelRootIffCommonRoot`: at that computed fuel, a point is a root of `polyGcd` iff it is
    a common root of both inputs.

Structural budget recursion threading a uniform degree bound; core Nat order arithmetic.  Free of `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Small Nat helper -/

/-- `n ≤ (n − 1) + 1` — a Nat is at most its predecessor's successor. -/
theorem natLeSubOneAddOne : ∀ n : Nat, n ≤ (n - 1) + 1
  | 0 => Nat.zero_le 1
  | _ + 1 => Nat.le_refl _

/-! ## The Euclidean step strictly shrinks the measure -/

/-- **The pseudo-remainder step strictly shrinks the divisor's trim-length.**  For a nonempty `secondary`
and adequate inner fuel (`polyDegree primary < fuel`), `(polyTrim (polyPseudoRem fuel secondary
primary)).length < (polyTrim secondary).length`.  Nonconstant `secondary`: r21 drops the pseudo-remainder
degree; constant `secondary`: r30 makes the pseudo-remainder zero. -/
theorem polyGcdStepMeasureDecreases (secondary primary : List Int) (fuel : Nat)
    (isNonempty : polyTrim secondary ≠ [])
    (isAdequate : polyDegree primary < fuel) :
    (polyTrim (polyPseudoRem fuel secondary primary)).length < (polyTrim secondary).length := by
  have measureEq : (polyTrim secondary).length = polyDegree secondary + 1 :=
    polyTrimLengthEqDegreeSucc secondary isNonempty
  cases Nat.eq_zero_or_pos (polyDegree secondary) with
  | inl isConstant =>
      rw [polyPseudoRemConstantTrimsNil secondary isNonempty isConstant fuel primary isAdequate, measureEq]
      exact Nat.succ_pos (polyDegree secondary)
  | inr isNonconstant =>
      have degreeDrop : polyDegree (polyPseudoRem fuel secondary primary) < polyDegree secondary :=
        polyPseudoRemDegreeLtDivisor secondary isNonconstant fuel primary isAdequate
      rw [measureEq]
      -- (polyTrim pseudoRem).length ≤ polyDegree pseudoRem + 1 ≤ polyDegree secondary < polyDegree secondary + 1
      have lengthLe : (polyTrim (polyPseudoRem fuel secondary primary)).length
          ≤ polyDegree (polyPseudoRem fuel secondary primary) + 1 :=
        natLeSubOneAddOne (polyTrim (polyPseudoRem fuel secondary primary)).length
      exact Nat.lt_of_le_of_lt lengthLe (Nat.succ_lt_succ degreeDrop)

/-! ## The GCD reaches nil within a computed fuel -/

/-- **The GCD recursion reaches nil within an adequate fuel.**  For a fixed `degreeBound` on both inputs and
`budget` bounding the divisor's trim-length, `fuel ≥ budget + degreeBound + 1` suffices for
`polyGcdReachesNil fuel primary secondary = true`.  Structural on `budget`; each Euclidean step drops the
measure (`polyGcdStepMeasureDecreases`) while the degree bound and the fuel headroom are preserved. -/
theorem polyGcdReachesNilOfBudget (degreeBound : Nat) :
    ∀ (budget fuel : Nat) (primary secondary : List Int),
      (polyTrim secondary).length ≤ budget →
      polyDegree primary ≤ degreeBound →
      polyDegree secondary ≤ degreeBound →
      budget + degreeBound + 1 ≤ fuel →
      polyGcdReachesNil fuel primary secondary = true
  | 0, fuel, primary, secondary, measureLe, _, _, _ => by
      have trimNil : polyTrim secondary = [] := by
        cases hTrim : polyTrim secondary with
        | nil => rfl
        | cons _ _ => rw [hTrim] at measureLe; exact absurd measureLe (Nat.not_succ_le_zero _)
      cases fuel with
      | zero =>
          show (match polyTrim secondary with | [] => true | _ :: _ => false) = true
          rw [trimNil]
      | succ _ =>
          show (match polyTrim secondary with
            | [] => true
            | _ :: _ => polyGcdReachesNil _ secondary (polyPseudoRem _ secondary primary)) = true
          rw [trimNil]
  | budget + 1, fuel, primary, secondary, measureLe, primaryDegLe, secondaryDegLe, fuelAdequate => by
      cases fuel with
      | zero => exact absurd fuelAdequate (Nat.not_succ_le_zero _)
      | succ innerFuel =>
          have fInner : budget + degreeBound + 1 ≤ innerFuel := by
            have rearrange : budget + 1 + degreeBound + 1 = (budget + degreeBound + 1) + 1 := by
              rw [Nat.add_right_comm budget 1 degreeBound]
            rw [rearrange] at fuelAdequate
            exact Nat.le_of_succ_le_succ fuelAdequate
          have innerAdequate : polyDegree primary < innerFuel :=
            Nat.lt_of_le_of_lt primaryDegLe
              (Nat.lt_of_lt_of_le (Nat.lt_succ_self degreeBound)
                (Nat.le_trans (Nat.le_add_left (degreeBound + 1) budget) fInner))
          show polyGcdReachesNil (innerFuel + 1) primary secondary = true
          dsimp only [polyGcdReachesNil]
          cases hTrim : polyTrim secondary with
          | nil => rfl
          | cons trimHead trimTail =>
              have isNonempty : polyTrim secondary ≠ [] := by
                rw [hTrim]; exact List.cons_ne_nil trimHead trimTail
              have measureDrop :
                  (polyTrim (polyPseudoRem innerFuel secondary primary)).length
                    < (polyTrim secondary).length :=
                polyGcdStepMeasureDecreases secondary primary innerFuel isNonempty innerAdequate
              have newMeasureLe :
                  (polyTrim (polyPseudoRem innerFuel secondary primary)).length ≤ budget :=
                Nat.le_of_lt_succ (Nat.lt_of_lt_of_le measureDrop measureLe)
              have newSecondaryDegLe :
                  polyDegree (polyPseudoRem innerFuel secondary primary) ≤ degreeBound := by
                have lenLe : (polyTrim (polyPseudoRem innerFuel secondary primary)).length
                    ≤ polyDegree secondary := by
                  have measureDropDeg :
                      (polyTrim (polyPseudoRem innerFuel secondary primary)).length
                        < polyDegree secondary + 1 := by
                    rw [← polyTrimLengthEqDegreeSucc secondary isNonempty]
                    exact measureDrop
                  exact Nat.le_of_lt_succ measureDropDeg
                exact Nat.le_trans
                  (Nat.le_trans (Nat.sub_le _ 1) lenLe) secondaryDegLe
              exact polyGcdReachesNilOfBudget degreeBound budget innerFuel secondary
                (polyPseudoRem innerFuel secondary primary) newMeasureLe secondaryDegLe
                newSecondaryDegLe fInner

/-- **The GCD reaches nil at a computed adequate fuel.**  `polyGcdReachesNil ((polyTrim secondary).length +
(polyDegree primary + polyDegree secondary) + 1) primary secondary = true`. -/
theorem polyGcdReachesNilAdequateFuel (primary secondary : List Int) :
    polyGcdReachesNil ((polyTrim secondary).length + (polyDegree primary + polyDegree secondary) + 1)
      primary secondary = true :=
  polyGcdReachesNilOfBudget (polyDegree primary + polyDegree secondary)
    (polyTrim secondary).length _ primary secondary (Nat.le_refl _)
    (Nat.le_add_right (polyDegree primary) (polyDegree secondary))
    (Nat.le_add_left (polyDegree secondary) (polyDegree primary)) (Nat.le_refl _)

/-! ## The unconditional root-set identity -/

/-- **The GCD's roots are exactly the common roots — unconditionally.**  At the computed adequate fuel, a
point is a root of `polyGcd` iff it is a root of *both* inputs.  r25's iff with the honest-termination flag
discharged by `polyGcdReachesNilAdequateFuel`. -/
theorem polyGcdAdequateFuelRootIffCommonRoot (point : Int) (primary secondary : List Int) :
    polyEval point
        (polyGcd ((polyTrim secondary).length + (polyDegree primary + polyDegree secondary) + 1)
          primary secondary)
      = 0 ↔
      (polyEval point primary = 0 ∧ polyEval point secondary = 0) :=
  polyGcdRootIffCommonRoot point
    ((polyTrim secondary).length + (polyDegree primary + polyDegree secondary) + 1)
    primary secondary (polyGcdReachesNilAdequateFuel primary secondary)

/-! ## Grounding -/

/-- The computed adequate fuel fires on the worked instance `x² − 1`, `(x+1)²`:
`polyGcdReachesNil (…) [-1,0,1] [1,2,1] = true` at the computed bound. -/
theorem polyGcdReachesNilAdequateFuelGrounding :
    polyGcdReachesNil (([1, 2, 1] : List Int).length.pred.succ.succ) [-1, 0, 1] [1, 2, 1] = true := by
  decide

/-- Consolidated marker for the ℤ[x] Euclidean GCD sub-arc.  Covers: the fuel-adequacy capstone of this
file — the Euclidean step strictly shrinks the divisor's trim-length (`polyGcdStepMeasureDecreases`), a
computed fuel reaches the honest-termination branch (`polyGcdReachesNilAdequateFuel`), and the converse
root-containment holds unconditionally at that fuel (`polyGcdAdequateFuelRootIffCommonRoot`); the Euclidean
GCD over pseudo-division and its capture of every common root (`IntPolynomialGcd`); the root-set
biconditional and eigenvalue-sharing shadow (`IntPolynomialGcdRootSet`); and the converse root-containment
under the honest-termination flag (`IntPolynomialGcdConverse`).  Referenced by `RationalPolynomial` and
`IntPolynomialDivision`. -/
def fxIntPoly_hasGcdFuelAdequacy : Bool := true

end FX1Poly.ComputerAlgebra
