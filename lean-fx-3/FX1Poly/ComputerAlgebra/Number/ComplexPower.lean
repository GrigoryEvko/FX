import FX1Poly.ComputerAlgebra.Number.ComplexRealModulusUnitLaws

/-! # ComplexPower — natural powers on the regular and Gaussian reals

Natural-number powers `zⁿ` on the zero-axiom regular reals and Gaussian reals,
with the multiplicative modulus-power law `|zⁿ| ~ |z|ⁿ`.  This supplies the
polynomial growth bound on the path to the Fundamental Theorem of Algebra by
lifting the single-factor modulus law `|z w| ~ |z| |w|`
(`modulusMulDenotesSame`) to `n` factors via induction on the exponent.

Structural recursion on `Nat` throughout; every step is a setoid, ring, or
square-root congruence lemma.  Zero axioms. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-- The real natural power `baseⁿ`: `n` sequential `mulReal` products of `base`,
anchored at the real unit. -/
def powReal (base : RegularReal) : Nat → RegularReal
  | 0 => constantReal oneRational
  | Nat.succ exponent => mulReal base (powReal base exponent)

/-- The complex natural power `baseⁿ`: `n` sequential `mulComplex` products of
`base`, anchored at the complex unit `1 + 0i`. -/
def powComplex (base : ComplexReal) : Nat → ComplexReal
  | 0 => oneComplex
  | Nat.succ exponent => mulComplex base (powComplex base exponent)

/-- A real power of a nonnegative real is nonnegative: the unit is nonnegative
and `mulReal` preserves nonnegativity.  Structural induction on the exponent. -/
theorem powRealNonNeg {base : RegularReal} (isBaseNonNegative : IsNonNegativeReal base) :
    (exponent : Nat) → IsNonNegativeReal (powReal base exponent)
  | 0 => oneRealIsNonNegativeReal
  | Nat.succ exponent =>
      mulRealPreservesIsNonNegativeReal isBaseNonNegative
        (powRealNonNeg isBaseNonNegative exponent)

/-- `|zⁿ| ~ |z|ⁿ` on the Gaussian-real setoid.  Induction on the exponent: base
case `|1| ~ 1` (`modulusOneDenotesSame`); step peels one factor with the
single-factor law `|z w| ~ |z| |w|` (`modulusMulDenotesSame`) and rewrites the
residual `|zⁿ|` to `|z|ⁿ` under `mulRealRespectsDenotesSame` by the inductive
hypothesis. -/
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

/-- Content marker: the natural-power folds and the modulus-power law are
inhabited. -/
def fxComplexReal_hasPowerAndModulusPow : Bool := true

end FX1Poly.ComputerAlgebra
