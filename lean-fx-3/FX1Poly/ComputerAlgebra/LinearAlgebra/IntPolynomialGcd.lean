import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDivision

/-! # IntPolynomialGcd — the Euclidean GCD over ℤ[x]

Runs the Euclidean algorithm on the pseudo-remainder shipped by `IntPolynomialDivision`
(`gcd(f, g) = gcd(g, pseudoRem(f, g))` until the second argument trims to the zero polynomial), so the
polynomial GCD is computed over ℤ with no rationals.  The GCD captures every common root:
`polyGcdVanishesAtCommonRoot` shows that if `f` and `g` both vanish at a point, so does `polyGcd fuel f g`,
driven by `polyPseudoRemVanishesAtCommonRoot` (the pseudo-remainder `b^k·f − q·g` vanishes wherever `f` and
`g` both do) carried through the fuel recursion.

Structural recursion on `fuel`; the only case analysis is `polyTrim`'s `nil`/`cons` enumeration; vanishing
arithmetic routes through the corpus `Int` lemmas.  Free of `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The pseudo-remainder and the Euclidean GCD -/

/-- The pseudo-remainder of dividing `dividend` by `divisor` (the third component of pseudo-division). -/
def polyPseudoRem (fuel : Nat) (divisor dividend : List Int) : List Int :=
  (polyPseudoDivMod fuel divisor dividend).2.2

/-- The Euclidean GCD over ℤ[x] via the pseudo-remainder: `gcd(primary, secondary) = gcd(secondary,
pseudoRem(primary, secondary))` until the second argument trims to the zero polynomial.  `fuel` bounds the
recursion structurally. -/
def polyGcd : Nat → List Int → List Int → List Int
  | 0, primary, _ => primary
  | fuel + 1, primary, secondary =>
      match polyTrim secondary with
      | [] => primary
      | _ :: _ => polyGcd fuel secondary (polyPseudoRem fuel secondary primary)

/-! ## The GCD captures every common root -/

/-- **The pseudo-remainder vanishes at every common root.**  If `dividend` and `divisor` both evaluate to
`0` at a point, so does their pseudo-remainder — read off the reconstruction
`b^scalePower · eval(dividend) = eval(quotient)·eval(divisor) + eval(remainder)`: both products collapse to
`0`, leaving `eval(remainder) = 0`. -/
theorem polyPseudoRemVanishesAtCommonRoot (point : Int) (fuel : Nat) (divisor dividend : List Int)
    (dividendVanishes : polyEval point dividend = 0) (divisorVanishes : polyEval point divisor = 0) :
    polyEval point (polyPseudoRem fuel divisor dividend) = 0 := by
  show polyEval point (polyPseudoDivMod fuel divisor dividend).2.2 = 0
  have leftIsZero :
      intPower (polyLeadingCoeff divisor) (polyPseudoDivMod fuel divisor dividend).1
          * polyEval point dividend
        = 0 :=
    (congrArg
        (intPower (polyLeadingCoeff divisor) (polyPseudoDivMod fuel divisor dividend).1 * ·)
        dividendVanishes).trans
      (intMulZero (intPower (polyLeadingCoeff divisor) (polyPseudoDivMod fuel divisor dividend).1))
  have rightCollapses :
      polyEval point (polyPseudoDivMod fuel divisor dividend).2.1 * polyEval point divisor
          + polyEval point (polyPseudoDivMod fuel divisor dividend).2.2
        = polyEval point (polyPseudoDivMod fuel divisor dividend).2.2 :=
    (congrArg (· + polyEval point (polyPseudoDivMod fuel divisor dividend).2.2)
        ((congrArg (polyEval point (polyPseudoDivMod fuel divisor dividend).2.1 * ·) divisorVanishes).trans
          (intMulZero (polyEval point (polyPseudoDivMod fuel divisor dividend).2.1)))).trans
      (intZeroAdd (polyEval point (polyPseudoDivMod fuel divisor dividend).2.2))
  exact (leftIsZero.symm.trans
    ((polyPseudoDivModReconstructs point fuel divisor dividend).trans rightCollapses)).symm

/-- **The GCD vanishes at every common root.**  If `primary` and `secondary` both vanish at a point, so
does `polyGcd fuel primary secondary` — by induction on fuel, the base case returns `primary` (which
vanishes) and the Euclidean step preserves both vanishings through `polyPseudoRemVanishesAtCommonRoot`. -/
theorem polyGcdVanishesAtCommonRoot (point : Int) :
    ∀ (fuel : Nat) (primary secondary : List Int),
      polyEval point primary = 0 → polyEval point secondary = 0 →
      polyEval point (polyGcd fuel primary secondary) = 0
  | 0, _, _, primaryVanishes, _ => primaryVanishes
  | fuel + 1, primary, secondary, primaryVanishes, secondaryVanishes => by
      dsimp only [polyGcd]
      cases polyTrim secondary with
      | nil => exact primaryVanishes
      | cons _ _ =>
          exact polyGcdVanishesAtCommonRoot point fuel secondary
            (polyPseudoRem fuel secondary primary) secondaryVanishes
            (polyPseudoRemVanishesAtCommonRoot point fuel secondary primary
              primaryVanishes secondaryVanishes)

/-! ## The right-zero identity -/

/-- **`gcd(f, 0) = f`.**  When the second argument is the zero polynomial the GCD is the first argument —
the Euclidean terminating case (`polyTrim [] = []`), definitional. -/
theorem polyGcdRightZero (fuel : Nat) (primary : List Int) :
    polyGcd (fuel + 1) primary [] = primary := rfl

/-! ## Shared linear factors (the eigenvalue-sharing bridge) -/

/-- **A shared linear factor is seen by the GCD.**  If `x − root` divides both inputs (each is a multiple
of `polyLinearFactor root`), then the GCD vanishes at `root` — the polynomial shadow of "two matrices
share the eigenvalue `root`", composing the factor theorem (`polyLinearFactorRootAnnihilatesMultiple`) with
`polyGcdVanishesAtCommonRoot`. -/
theorem polyGcdSeesSharedLinearFactor (root : Int) (fuel : Nat)
    (cofactorPrimary cofactorSecondary : List Int) :
    polyEval root
        (polyGcd fuel (polyMul (polyLinearFactor root) cofactorPrimary)
          (polyMul (polyLinearFactor root) cofactorSecondary))
      = 0 :=
  polyGcdVanishesAtCommonRoot root fuel
    (polyMul (polyLinearFactor root) cofactorPrimary)
    (polyMul (polyLinearFactor root) cofactorSecondary)
    (polyLinearFactorRootAnnihilatesMultiple root cofactorPrimary)
    (polyLinearFactorRootAnnihilatesMultiple root cofactorSecondary)

/-! ## Groundings -/

/-- The Euclidean GCD of `x² − 1 = (x−1)(x+1)` and `x² + 2x + 1 = (x+1)²` shares the root `−1` (their common
factor `x + 1`): `polyEval (-1) (polyGcd 5 [-1, 0, 1] [1, 2, 1]) = 0`. -/
theorem polyGcdSharesCommonRootAtMinusOne :
    polyEval (-1) (polyGcd 5 [-1, 0, 1] [1, 2, 1]) = 0 := by decide

/-- The GCD extracts the degree-1 common factor `x + 1` (up to content scaling): the computed GCD has
degree `1` — `polyDegree (polyGcd 5 [-1, 0, 1] [1, 2, 1]) = 1`. -/
theorem polyGcdExtractsCommonFactorDegree :
    polyDegree (polyGcd 5 [-1, 0, 1] [1, 2, 1]) = 1 := by decide

/-- The pseudo-remainder step vanishes at the common root `−1` too: `polyEval (-1)
(polyPseudoRem 5 [1, 2, 1] [-1, 0, 1]) = 0`. -/
theorem polyPseudoRemSharesCommonRootAtMinusOne :
    polyEval (-1) (polyPseudoRem 5 [1, 2, 1] [-1, 0, 1]) = 0 := by decide

/-- The shared eigenvalue `2` (shared factor `x − 2`) of `(x−2)(x+1)` and `(x−2)(x+3)` is seen by the GCD:
`polyEval 2 (polyGcd 5 (polyMul (polyLinearFactor 2) [1, 1]) (polyMul (polyLinearFactor 2) [3, 1])) = 0`. -/
theorem polyGcdSeesSharedEigenvalueAtTwo :
    polyEval 2
        (polyGcd 5 (polyMul (polyLinearFactor 2) [1, 1]) (polyMul (polyLinearFactor 2) [3, 1]))
      = 0 := by decide

end FX1Poly.ComputerAlgebra
