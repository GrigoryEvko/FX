import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDivision

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntPolynomialGcd — the Euclidean GCD over ℤ[x]
(the fourth brick of `invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255)

`IntPolynomialDivision` shipped pseudo-division: `leadDivisor^scalePower · dividend = quotient · divisor +
remainder` for an arbitrary divisor, integrally.  This file runs the Euclidean algorithm on the
pseudo-remainder — `gcd(f, g) = gcd(g, pseudoRem(f, g))` until the second argument is the zero polynomial —
so the polynomial GCD is computed over ℤ with no rationals.

## What is PROVEN

The GCD captures every common root: `polyGcdVanishesAtCommonRoot` shows that if `f` and `g` both vanish at
a point, so does `polyGcd fuel f g`, for every fuel.  The engine is `polyPseudoRemVanishesAtCommonRoot` —
the pseudo-remainder `b^k·f − q·g` vanishes wherever `f` and `g` both vanish (read straight off the r10
reconstruction) — carried through the Euclidean recursion by induction on fuel.  This is the semantic heart
of why the Euclidean GCD computes the greatest common divisor: the common-root set is exactly what the
recursion preserves.

The converse (every root of the GCD is a common root) and the degree-based termination bound are the honest
remaining steps of the invariant-factor classifier.

## Zero-axiom design

The recursion is structural on `fuel`; the only case analysis is `polyTrim`'s full `nil`/`cons`
enumeration.  The vanishing arithmetic routes through the corpus `Int` lemmas.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/IntPolynomialGcd.lean`.
-/

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

/-! ## The GCD captures every common root (PROVEN) -/

/-- **The pseudo-remainder vanishes at every common root.**  If `dividend` and `divisor` both evaluate to
`0` at a point, so does their pseudo-remainder — read off the r10 reconstruction
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

/-! ## Groundings -/

/-- The Euclidean GCD of `x² − 1 = (x−1)(x+1)` and `x² + 2x + 1 = (x+1)²` shares the root `−1` (their common
factor `x + 1`): `polyEval (-1) (polyGcd 5 [-1, 0, 1] [1, 2, 1]) = 0`, an instance of
`polyGcdVanishesAtCommonRoot` since both vanish at `−1`. -/
theorem polyGcdSharesCommonRootAtMinusOne :
    polyEval (-1) (polyGcd 5 [-1, 0, 1] [1, 2, 1]) = 0 := by decide

/-- The pseudo-remainder step vanishes at the common root `−1` too: `polyEval (-1)
(polyPseudoRem 5 [1, 2, 1] [-1, 0, 1]) = 0`. -/
theorem polyPseudoRemSharesCommonRootAtMinusOne :
    polyEval (-1) (polyPseudoRem 5 [1, 2, 1] [-1, 0, 1]) = 0 := by decide

/-- Marker: the ℤ[x] Euclidean GCD ships over pseudo-division (no rationals), with the proof that it
captures every common root of its inputs (`polyGcdVanishesAtCommonRoot`).  The converse root-containment
and the degree-based termination bound are the next bricks of the invariant-factor classifier. -/
def fxIntPoly_hasEuclideanGcdCommonRoots : Bool := true

end FX1Poly.ComputerAlgebra
