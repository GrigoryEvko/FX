import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialGcd

/-! # IntPolynomialPseudoRemStable — fuel-stability of the pseudo-remainder

The foundational fuel-stability primitive for the fuel-adequacy wiring: when the dividend already has degree
below the divisor, the pseudo-remainder is the dividend itself for every fuel, so the pseudo-division has
reached its terminal shape and adding fuel changes nothing.  `polyPseudoRemBelowDivisor` proves `polyDegree
dividend < polyDegree divisor → polyPseudoRem fuel divisor dividend = dividend` for all `fuel` (both the
`fuel = 0` base and the `isTrue` guard branch return the dividend, and the guard is fuel-independent);
`polyPseudoRemZeroFuel` is the zero-fuel special case.

Structural on fuel; the guard `Nat.decLt` cased into `isTrue`/`isFalse` (the false branch closed by
`absurd`).  Free of `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.ComputerAlgebra

/-- **The zero-fuel pseudo-remainder is the whole dividend.**  `polyPseudoDivMod 0 = (0, [], dividend)`, so
nothing has been reduced. -/
theorem polyPseudoRemZeroFuel (divisor dividend : List Int) :
    polyPseudoRem 0 divisor dividend = dividend := rfl

/-- **A below-degree dividend is its own pseudo-remainder, for every fuel.**  When `polyDegree dividend <
polyDegree divisor`, `polyPseudoRem fuel divisor dividend = dividend` — the fuel-independent terminal
shape, reached at the `isTrue` guard. -/
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

/-- Below-divisor stability: `x + 1` divided by `x² − 1` is unchanged at fuel 7 —
`polyPseudoRem 7 [-1, 0, 1] [1, 1] = [1, 1]`. -/
theorem polyPseudoRemBelowDivisorGrounding : polyPseudoRem 7 [-1, 0, 1] [1, 1] = [1, 1] := by decide

end FX1Poly.ComputerAlgebra
