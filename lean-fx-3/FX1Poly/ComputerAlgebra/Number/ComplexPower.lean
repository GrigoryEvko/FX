import FX1Poly.ComputerAlgebra.Number.ComplexRealModulusUnitLaws

/-! # ComplexPower — ℝ/ℂ natural powers and the modulus-power law (FTA-path prerequisite)

The natural-number power `zⁿ` on the zero-axiom regular reals and Gaussian
reals, plus the multiplicative modulus-power law `|zⁿ| ~ |z|ⁿ`.  This is the
clean structural rung the polynomial growth bound of the Fundamental Theorem of
Algebra path consumes: it turns the already-shipped single-factor modulus law
`|z w| ~ |z| |w|` (`modulusMulDenotesSame`) into an `n`-factor statement by a
direct induction on the exponent.

* **Real power** `powReal base n` folds `mulReal` over `n` copies of `base`,
  anchored at the real unit `constantReal oneRational`.

* **Complex power** `powComplex base n` folds `mulComplex` over `n` copies,
  anchored at `oneComplex`.

* **Nonnegativity is preserved** (`powRealNonNeg`) — the unit is nonnegative and
  `mulReal` preserves nonnegativity, so every real power of a nonnegative real is
  nonnegative.

* **The modulus-power law** (`modulusPowDenotesSame`) `|zⁿ| ~ |z|ⁿ`.  The base
  case is the unit-modulus law `|1| ~ 1`; the step folds the modulus through one
  factor via `modulusMulDenotesSame`, then rewrites the remaining `|zⁿ|` to
  `|z|ⁿ` under the left-congruence of `mulReal` by the inductive hypothesis.

Structural recursion on `Nat` throughout; every brick is one of the shipped
zero-axiom setoid, ring, or √-congruence lemmas.  Zero axioms. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## The natural-power folds -/

/-- **The real natural power** `baseⁿ` — `n` sequential `mulReal` products of
`base`, anchored at the real unit. -/
def powReal (base : RegularReal) : Nat → RegularReal
  | 0 => constantReal oneRational
  | Nat.succ exponent => mulReal base (powReal base exponent)

/-- **The complex natural power** `baseⁿ` — `n` sequential `mulComplex` products
of `base`, anchored at the complex unit `1 + 0i`. -/
def powComplex (base : ComplexReal) : Nat → ComplexReal
  | 0 => oneComplex
  | Nat.succ exponent => mulComplex base (powComplex base exponent)

/-! ## Nonnegativity of real powers -/

/-- **Nonnegativity is closed under real powers** — the unit is a nonnegative
real, and `mulReal` preserves nonnegativity, so `baseⁿ` stays nonnegative for a
nonnegative `base`.  Structural induction on the exponent. -/
theorem powRealNonNeg {base : RegularReal} (isBaseNonNegative : IsNonNegativeReal base) :
    (exponent : Nat) → IsNonNegativeReal (powReal base exponent)
  | 0 => oneRealIsNonNegativeReal
  | Nat.succ exponent =>
      mulRealPreservesIsNonNegativeReal isBaseNonNegative
        (powRealNonNeg isBaseNonNegative exponent)

/-! ## The modulus-power law `|zⁿ| ~ |z|ⁿ` -/

/-- **The modulus of a power is the power of the modulus** `|zⁿ| ~ |z|ⁿ` on the
Gaussian-real setoid.  Structural induction on the exponent: the base case is
the unit-modulus law `|1| ~ 1` (`modulusOneDenotesSame`); the step peels one
factor off with the single-factor modulus law `|z w| ~ |z| |w|`
(`modulusMulDenotesSame`) and rewrites the residual `|zⁿ|` to `|z|ⁿ` under
`mulRealRespectsDenotesSame` by the inductive hypothesis. -/
theorem modulusPowDenotesSame (baseValue : ComplexReal) :
    (exponent : Nat) →
      DenotesSameReal (modulus (powComplex baseValue exponent))
        (powReal (modulus baseValue) exponent)
  | 0 => modulusOneDenotesSame
  | Nat.succ exponent =>
      denotesSameRealTrans
        (modulusMulDenotesSame baseValue (powComplex baseValue exponent))
        (mulRealRespectsDenotesSame
          (denotesSameRealRefl (modulus baseValue))
          (modulusPowDenotesSame baseValue exponent))

/-- Content marker — the ℝ/ℂ natural-power folds and the modulus-power law are
inhabited. -/
def fxComplexReal_hasPowerAndModulusPow : Bool := true

end FX1Poly.ComputerAlgebra
