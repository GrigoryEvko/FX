import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialGcd

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntPolynomialPseudoRemStable — fuel-stability of the pseudo-rem
(the fourteenth brick of `invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255)

Toward the fuel-adequacy → true-fixed-point wiring ("`polyGcd` with adequate fuel = the actual gcd") this
file supplies the foundational fuel-stability primitive: when the dividend already has degree below the
divisor, the pseudo-remainder is the dividend itself — *for every fuel*, so the pseudo-division has already
reached its terminal shape and adding fuel changes nothing.

## What is PROVEN

  * `polyPseudoRemBelowDivisor`: `polyDegree dividend < polyDegree divisor → polyPseudoRem fuel divisor
    dividend = dividend` for all `fuel` — both the `fuel = 0` base (`polyPseudoDivMod 0 = (0, [], dividend)`)
    and the `isTrue` guard branch return the dividend unchanged, and the guard `Nat.decLt (deg dividend)
    (deg divisor)` does not depend on fuel.
  * `polyPseudoRemZeroFuel`: `polyPseudoRem 0 divisor dividend = dividend` — the zero-fuel remainder is the
    whole dividend (nothing reduced yet).

## The remaining coupled-fuel grind (honest boundary)

The full "adequate fuel ⟹ `polyGcdReachesNil = true`" wiring is a genuine multi-brick grind, NOT walled but
laborious: `polyGcd`'s outer recursion depth and its inner pseudo-division share ONE fuel counter (`polyGcd
(fuel+1)` calls `polyPseudoRem fuel`), so an adequacy bound must dominate both simultaneously; and the
constant-divisor / nil-dividend edge breaks the strict degree-decrease (r20 needs `1 ≤ polyDegree divisor`)
and makes the pseudo-division's `scalePower` component fuel-dependent even where the *remainder* stabilizes.
This brick is the terminal-shape primitive both directions of that grind route through.

## Zero-axiom design

Structural on fuel; the guard `Nat.decLt` cased into `isTrue`/`isFalse` (the false branch closed by
`absurd`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/ComputerAlgebra/LinearAlgebra/IntPolynomialPseudoRemStable.lean`.
-/

namespace FX1Poly.ComputerAlgebra

/-- **The zero-fuel pseudo-remainder is the whole dividend.**  `polyPseudoDivMod 0 = (0, [], dividend)`, so
nothing has been reduced. -/
theorem polyPseudoRemZeroFuel (divisor dividend : List Int) :
    polyPseudoRem 0 divisor dividend = dividend := rfl

/-- **A below-degree dividend is its own pseudo-remainder, for every fuel.**  When `polyDegree dividend <
polyDegree divisor`, `polyPseudoRem fuel divisor dividend = dividend` — the pseudo-division's terminal
shape, reached immediately (the `isTrue` guard) and fuel-independent. -/
theorem polyPseudoRemBelowDivisor (divisor dividend : List Int)
    (isBelow : polyDegree dividend < polyDegree divisor) :
    ∀ fuel : Nat, polyPseudoRem fuel divisor dividend = dividend
  | 0 => rfl
  | _ + 1 => by
      show (polyPseudoDivMod _ divisor dividend).2.2 = dividend
      dsimp only [polyPseudoDivMod]
      cases Nat.decLt (polyDegree dividend) (polyDegree divisor) with
      | isTrue _ => rfl
      | isFalse isNotBelow => exact absurd isBelow isNotBelow

/-! ## Grounding -/

/-- The below-divisor stability exhibited: dividing `x + 1` (`[1, 1]`, degree 1) by `x² − 1` (`[-1, 0, 1]`,
degree 2), the remainder is `x + 1` unchanged at fuel 7 — `polyPseudoRem 7 [-1, 0, 1] [1, 1] = [1, 1]`. -/
theorem polyPseudoRemBelowDivisorGrounding : polyPseudoRem 7 [-1, 0, 1] [1, 1] = [1, 1] := by decide

/-- Marker: the ℤ[x] pseudo-remainder is fuel-stable at its terminal shape — a below-divisor-degree dividend
is its own remainder for every fuel (`polyPseudoRemBelowDivisor`).  The terminal-shape primitive of the
fuel-adequacy → true-fixed-point grind. -/
def fxIntPoly_hasPseudoRemainderTerminalStability : Bool := true

end FX1Poly.ComputerAlgebra
