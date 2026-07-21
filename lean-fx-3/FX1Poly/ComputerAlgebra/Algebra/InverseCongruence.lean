import FX1Poly.ComputerAlgebra.Algebra.SetoidRingHom
import FX1Poly.ComputerAlgebra.Number.ComplexRealField

/-! # InverseCongruence — the analytic inverses are setoid-congruent

Setoid congruence for the multiplicative inverse on ℝ and ℂ.  Although the inverse
is built from `Type`-valued positivity/apartness data, it is characterized by the
field law `value · inverse ~ 1` rather than by its construction, and inverse
uniqueness in a commutative ring (`inverseUniqueInCommutativeRing`, module
`SetoidRingHom`) forces congruence by equational ring algebra.

Each result instantiates that generic lemma at the ℝ or ℂ ring witness.  The
base-congruence statement (`a ~ b`) subsumes witness-independence as its reflexive
special case.  No `Eq.rec`, no sign-branch dispatch, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## ℝ — the direct positivity inverse -/

/-- `inverseReal` is base-congruent: same-denoting positive reals have
same-denoting reciprocals, regardless of the chosen positivity witnesses, by
inverse uniqueness at the ℝ ring witness. -/
theorem inverseRealCongr {leftValue rightValue : RegularReal}
    (leftWitness : RealPositivityWitness leftValue)
    (rightWitness : RealPositivityWitness rightValue)
    (areSame : DenotesSameReal leftValue rightValue) :
    DenotesSameReal (inverseReal leftWitness) (inverseReal rightWitness) :=
  inverseUniqueInCommutativeRing regularRealCommutativeRingWitness areSame
    (mulRealInverseDenotesOne leftWitness) (mulRealInverseDenotesOne rightWitness)

/-- `inverseReal` is witness-independent: two positivity witnesses on the same real
give same-denoting reciprocals (the reflexive corollary). -/
theorem inverseRealWitnessIndependent {value : RegularReal}
    (firstWitness secondWitness : RealPositivityWitness value) :
    DenotesSameReal (inverseReal firstWitness) (inverseReal secondWitness) :=
  inverseRealCongr firstWitness secondWitness (denotesSameRealRefl value)

/-! ## ℝ — the apartness inverse (used by the Heyting field) -/

/-- `inverseRealOfApartness` is base-congruent.  The sign-branch dispatch is
immaterial: whichever branch each apartness witness takes, only the field law
`value · inverse ~ 1` is used. -/
theorem inverseRealOfApartnessCongr {leftValue rightValue : RegularReal}
    (leftApart : RealApartnessWitness leftValue (constantReal zeroRational))
    (rightApart : RealApartnessWitness rightValue (constantReal zeroRational))
    (areSame : DenotesSameReal leftValue rightValue) :
    DenotesSameReal (inverseRealOfApartness leftApart)
      (inverseRealOfApartness rightApart) :=
  inverseUniqueInCommutativeRing regularRealCommutativeRingWitness areSame
    (mulRealInverseOfApartnessDenotesOne leftApart)
    (mulRealInverseOfApartnessDenotesOne rightApart)

/-- `inverseRealOfApartness` is witness-independent, even across a differing
sign-side choice (the reflexive corollary). -/
theorem inverseRealOfApartnessWitnessIndependent {value : RegularReal}
    (firstApart secondApart : RealApartnessWitness value (constantReal zeroRational)) :
    DenotesSameReal (inverseRealOfApartness firstApart)
      (inverseRealOfApartness secondApart) :=
  inverseRealOfApartnessCongr firstApart secondApart (denotesSameRealRefl value)

/-! ## ℂ — the Gauss inverse -/

/-- `inverseComplex` is base-congruent, by the same lemma at the ℂ ring witness;
no descent to `realPart`/`imaginaryPart` is needed, the ℂ field law suffices. -/
theorem inverseComplexCongr {leftValue rightValue : ComplexReal}
    (leftApart : IsApartFromZeroComplex leftValue)
    (rightApart : IsApartFromZeroComplex rightValue)
    (areSame : DenotesSameComplex leftValue rightValue) :
    DenotesSameComplex (inverseComplex leftValue leftApart)
      (inverseComplex rightValue rightApart) :=
  inverseUniqueInCommutativeRing complexCommutativeRingWitness areSame
    (mulComplexInverseComplexDenotesOne leftValue leftApart)
    (mulComplexInverseComplexDenotesOne rightValue rightApart)

/-- `inverseComplex` is witness-independent: two apartness witnesses on the same
complex give same-denoting inverses (the reflexive corollary). -/
theorem inverseComplexWitnessIndependent {value : ComplexReal}
    (firstApart secondApart : IsApartFromZeroComplex value) :
    DenotesSameComplex (inverseComplex value firstApart)
      (inverseComplex value secondApart) :=
  inverseComplexCongr firstApart secondApart (denotesSameComplexRefl value)

end FX1Poly.ComputerAlgebra
