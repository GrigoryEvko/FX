import FX1Poly.ComputerAlgebra.Algebra.SetoidRingHom
import FX1Poly.ComputerAlgebra.Number.ComplexRealField

/-! # InverseCongruence — the analytic inverses are setoid-congruent (NUM-ALG-3)

The documented "honest wall" — no setoid congruence for the inverse, because
its argument is `Type`-valued positivity/apartness data — dissolves.  The
inverse is characterized not by HOW it is built but by WHAT it satisfies
(`value · inverse ~ 1`, shipped), and inverse uniqueness in a commutative ring
then forces congruence by pure equational ring algebra
(`inverseUniqueInCommutativeRing`, § SetoidRingHom).

Each result is a ONE-LINER instantiation of the generic engine at the ℝ or ℂ
ring witness.  The general base-congruence statement (`a ~ b`) subsumes
witness-independence as its reflexive special case, so the two facts the wall
asked for are one lemma.  No `Eq.rec`, no sign-branch dispatch, no new
estimates, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## ℝ — the direct positivity inverse -/

/-- **`inverseReal` is base-congruent** — same-denoting positive reals have
same-denoting reciprocals, regardless of which positivity witnesses were
chosen.  Inverse uniqueness at the ℝ ring witness: both reciprocals invert
same-denoting bases. -/
theorem inverseRealCongr {leftValue rightValue : RegularReal}
    (leftWitness : RealPositivityWitness leftValue)
    (rightWitness : RealPositivityWitness rightValue)
    (areSame : DenotesSameReal leftValue rightValue) :
    DenotesSameReal (inverseReal leftWitness) (inverseReal rightWitness) :=
  inverseUniqueInCommutativeRing regularRealCommutativeRingWitness areSame
    (mulRealInverseDenotesOne leftWitness) (mulRealInverseDenotesOne rightWitness)

/-- **`inverseReal` is witness-independent** — the reflexive corollary: two
positivity witnesses on the SAME real give same-denoting reciprocals. -/
theorem inverseRealWitnessIndependent {value : RegularReal}
    (firstWitness secondWitness : RealPositivityWitness value) :
    DenotesSameReal (inverseReal firstWitness) (inverseReal secondWitness) :=
  inverseRealCongr firstWitness secondWitness (denotesSameRealRefl value)

/-! ## ℝ — the apartness inverse (used by the Heyting field) -/

/-- **`inverseRealOfApartness` is base-congruent** — the sign-branch dispatch is
invisible to the engine: whatever branch each apartness witness takes, the
shipped field law `value · inverse ~ 1` is all that is consumed. -/
theorem inverseRealOfApartnessCongr {leftValue rightValue : RegularReal}
    (leftApart : RealApartnessWitness leftValue (constantReal zeroRational))
    (rightApart : RealApartnessWitness rightValue (constantReal zeroRational))
    (areSame : DenotesSameReal leftValue rightValue) :
    DenotesSameReal (inverseRealOfApartness leftApart)
      (inverseRealOfApartness rightApart) :=
  inverseUniqueInCommutativeRing regularRealCommutativeRingWitness areSame
    (mulRealInverseOfApartnessDenotesOne leftApart)
    (mulRealInverseOfApartnessDenotesOne rightApart)

/-- **`inverseRealOfApartness` is witness-independent** — the reflexive
corollary, spanning even a differing sign-side choice. -/
theorem inverseRealOfApartnessWitnessIndependent {value : RegularReal}
    (firstApart secondApart : RealApartnessWitness value (constantReal zeroRational)) :
    DenotesSameReal (inverseRealOfApartness firstApart)
      (inverseRealOfApartness secondApart) :=
  inverseRealOfApartnessCongr firstApart secondApart (denotesSameRealRefl value)

/-! ## ℂ — the Gauss inverse -/

/-- **`inverseComplex` is base-congruent** — the SAME engine at the ℂ ring
witness; no descent to `realPart`/`imaginaryPart` is needed, the shipped ℂ
field law drives it. -/
theorem inverseComplexCongr {leftValue rightValue : ComplexReal}
    (leftApart : IsApartFromZeroComplex leftValue)
    (rightApart : IsApartFromZeroComplex rightValue)
    (areSame : DenotesSameComplex leftValue rightValue) :
    DenotesSameComplex (inverseComplex leftValue leftApart)
      (inverseComplex rightValue rightApart) :=
  inverseUniqueInCommutativeRing complexCommutativeRingWitness areSame
    (mulComplexInverseComplexDenotesOne leftValue leftApart)
    (mulComplexInverseComplexDenotesOne rightValue rightApart)

/-- **`inverseComplex` is witness-independent** — the reflexive corollary: two
apartness witnesses on the same complex give same-denoting inverses. -/
theorem inverseComplexWitnessIndependent {value : ComplexReal}
    (firstApart secondApart : IsApartFromZeroComplex value) :
    DenotesSameComplex (inverseComplex value firstApart)
      (inverseComplex value secondApart) :=
  inverseComplexCongr firstApart secondApart (denotesSameComplexRefl value)

end FX1Poly.ComputerAlgebra
